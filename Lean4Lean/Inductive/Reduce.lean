import Lean.Structure
import Lean4Lean.Expr
import Lean4Lean.PExpr

namespace Lean

section

structure ExtMethods (m : Type → Type u) where
  isDefEq : PExpr → PExpr → m (Bool × Option PExpr)
  whnf  : PExpr → m (PExpr × Option PExpr)
  inferTypePure : PExpr → m PExpr
  appPrfIrrel : PExpr → PExpr → Option PExpr → PExpr → PExpr → m PExpr
  appHEqTrans? : PExpr → PExpr → PExpr → Option PExpr → Option PExpr → m (Option PExpr)
  isDefEqApp : PExpr → PExpr → (Nat × Option PExpr) → m (Bool × Option PExpr)

variable [Monad m] (env : Environment)
  (meth : ExtMethods m)

def getFirstCtor (dName : Name) : Option Name := do
  let some (.inductInfo info) := env.find? dName | none
  info.ctors.head?

def mkNullaryCtor (type : PExpr) (nparams : Nat) : Option PExpr :=
  type.toExpr.withApp fun d args => do
  let .const dName ls := d | none
  let name ← getFirstCtor env dName
  return mkAppRange (.const name ls) 0 nparams args |>.toPExpr type.data -- FIXME

/--
When `e` has the type of a K-like inductive, converts it into a constructor
application.

For instance if we have `e : Eq a a`, it is converted into `Eq.refl a` (which
it is definitionally equal to by proof irrelevance). Note that the indices of
`e`'s type must match those of the constructor application (for instance,
`e : Eq a b` cannot be converted if `a` and `b` are not defeq).
-/
def toCtorWhenK (rval : RecursorVal) (e : PExpr) : m (PExpr × Option PExpr) := do
  assert! rval.k
  let (appType, p?) ← meth.whnf (← meth.inferTypePure e)
  assert! p? == none
  let .const appTypeI _ := appType.toExpr.getAppFn | return (e, none)
  if appTypeI != rval.getInduct then return (e, none)
  if appType.toExpr.hasExprMVar then
    let appTypeArgs := appType.toExpr.getAppArgs
    for h : i in [rval.numParams:appTypeArgs.size] do
      if (appTypeArgs[i]'h.2).hasExprMVar then return (e, none)
  let some newCtorApp := mkNullaryCtor env appType rval.numParams | return (e, none)
  -- check that the indices of types of `e` and `newCtorApp` match
  let (defEq, p?) ← meth.isDefEq appType (← meth.inferTypePure newCtorApp)
  assert! p? == none
  unless defEq do return (e, none)
  return (newCtorApp, ← meth.appPrfIrrel appType appType none e newCtorApp)

def expandEtaStruct (eType e : PExpr) : (PExpr × Option PExpr) :=
  eType.toExpr.withApp fun I args => Id.run do
  let .const I ls := I | return (e, none)
  let some ctor := getFirstCtor env I | return (e, none)
  let some (.ctorInfo info) := env.find? ctor | unreachable!
  let mut result := mkAppRange (.const ctor ls) 0 info.numParams args
  for i in [:info.numFields] do
    result := .app result (.proj I i e)
  pure (result.toPExprMerge e eType, none)

/--
When `e` is of struct type, converts it into a constructor application using
projections.

For instance if we have `e : String`, it is converted into
`String.mk (String.data e)` (which is definitionally equal to `e` by struct
eta).
-/
def toCtorWhenStruct (inductName : Name) (e : PExpr) : m (PExpr × Option PExpr) := do
  if !isStructureLike env inductName || (e.toExpr.isConstructorApp?' env).isSome then
    return (e, none)
  let (eType, p?) ← meth.whnf (← meth.inferTypePure e)
  assert! p? == none
  if !eType.toExpr.getAppFn.isConstOf inductName then return (e, none)
  if (← meth.whnf (← meth.inferTypePure eType)).1 == Expr.prop.toPExpr default then return (e, none)
  return expandEtaStruct env eType e

def getRecRuleFor (rval : RecursorVal) (major : Expr) : Option RecursorRule := do
  let .const fn _ := major.getAppFn | none
  rval.rules.find? (·.ctor == fn)

/--
Performs recursor reduction on `e` (returning `none` if not applicable).

For recursor reduction to occur, `e` must be a recursor application where the
major premise is either a complete constructor application or of a K- or
structure-like inductive type (in which case it is converted into an equivalent
constructor application). The reduction is done by applying the
`RecursorRule.rhs` associated with the constructor to the parameters from the
recursor application and the fields of the constructor application.
-/
def inductiveReduceRec [Monad m] (env : Environment) (e : PExpr)
    : m (Option (PExpr × Option PExpr)) := do
  let recFn := e.toExpr.getAppFn
  let .const recFnName ls := recFn | return none
  let some (.recInfo info) := env.find? recFnName | return none
  let recArgs := e.toExpr.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major' := recArgs[majorIdx]? | return none
  let major := major'.toPExpr e.data -- FIXME
  let (majorK, majorEqmajorK?) := if info.k then ← toCtorWhenK env meth info major else (major, none)
  let (majorKWhnf, majorKEqmajorKWhnf?) ← meth.whnf majorK
  let majorEqmajorKWhnf? ← meth.appHEqTrans? major majorK majorKWhnf majorEqmajorK? majorKEqmajorKWhnf?
  let (majorMaybeCtor, majorKWhnfEqMajorMaybeCtor?) ← match majorKWhnf.toExpr with
    | .lit l => pure (l.toConstructor.toPExpr default, none)
    | _ => toCtorWhenStruct env meth info.getInduct majorKWhnf
  let majorEqMajorMaybeCtor? ← meth.appHEqTrans? major majorKWhnf majorMaybeCtor majorEqmajorKWhnf? majorKWhnfEqMajorMaybeCtor?
  let eNewMajor := mkAppN recFn (recArgs.set! majorIdx majorMaybeCtor) |>.toPExpr e.data --FIXME
  let (.true, eEqeNewMajor?) ← meth.isDefEqApp e eNewMajor (majorIdx, majorEqMajorMaybeCtor?) | unreachable!
  let some rule := getRecRuleFor info majorMaybeCtor | return none
  let majorArgs := majorMaybeCtor.toExpr.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  -- get parameters from recursor application (recursor rules don't need the indices,
  -- as these are determined by the constructor and its parameters/fields)
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx recArgs
  -- get fields from constructor application
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs
  if majorIdx + 1 < recArgs.size then
    rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
  return .some (rhs.toPExpr e.data, eEqeNewMajor?) -- FIXME

end
