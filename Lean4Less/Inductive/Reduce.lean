import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr

namespace Lean4Less
open Lean

section

structure ExtMethods (m : Type → Type u) where
  isDefEq : PExpr → PExpr → m (Bool × Option EExpr)
  isDefEqPure : PExpr → PExpr → m Bool
  whnf  : PExpr → m (PExpr × Option EExpr)
  inferTypePure : PExpr → m PExpr
  withPure : {T : Type} → m T → m T
  appPrfIrrelHEq : PExpr → PExpr → EExpr → PExpr → PExpr → m EExpr
  appPrfIrrel : PExpr → PExpr →  PExpr → m EExpr
  appHEqTrans? : PExpr → PExpr → PExpr → Option EExpr → Option EExpr → m (Option EExpr)
  isDefEqApp' : PExpr → PExpr → Nat → HashMap Nat (Option EExpr) → m (Bool × Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))
  isDefEqApp : PExpr → PExpr → Nat → HashMap Nat (Option EExpr) → m (Bool × Option EExpr)

variable [Monad m] (env : Environment)
  (meth : ExtMethods m)

def getFirstCtor (dName : Name) : Option Name := do
  let some (.inductInfo info) := env.find? dName | none
  info.ctors.head?

def mkNullaryCtor (type : PExpr) (nparams : Nat) : Option (PExpr × Name) :=
  type.toExpr.withApp fun d args => do
  let .const dName ls := d | none
  let name ← getFirstCtor env dName
  return (mkAppRange (.const name ls) 0 nparams args |>.toPExpr, name)

/--
When `e` has the type of a K-like inductive, converts it into a constructor
application.

For instance if we have `e : Eq a a`, it is converted into `Eq.refl a` (which
it is definitionally equal to by proof irrelevance). Note that the indices of
`e`'s type must match those of the constructor application (for instance,
`e : Eq a b` cannot be converted if `a` and `b` are not defeq).
-/
def toCtorWhenK (rval : RecursorVal) (e : PExpr) : m (PExpr × Option (EExpr) × (Option (Array (Option (PExpr × PExpr × EExpr))))) := do
  assert! rval.k
  let (type, p?) ← meth.whnf (← meth.inferTypePure e)
  assert! p? == none
  let .const typeI _ := type.toExpr.getAppFn | return (e, none, none)
  if typeI != rval.getInduct then return (e, none, none)
  if type.toExpr.hasExprMVar then
    let typeArgs := type.toExpr.getAppArgs
    for h : i in [rval.numParams:typeArgs.size] do
      if (typeArgs[i]'h.2).hasExprMVar then return (e, none, none)
  let some (newCtorApp, newCtorName) := mkNullaryCtor env type rval.numParams | return (e, none, none)
  if let (.const ctorName _) := e.toExpr.getAppFn then
    if ctorName == newCtorName then
      if let true ← meth.isDefEqPure e newCtorApp then
        return (e, none, none)
  let appType ← meth.inferTypePure newCtorApp
  -- check that the indices of types of `e` and `newCtorApp` match
  let (defEq, d?) ←
    if type.toExpr.isApp then meth.isDefEqApp' type appType 101 default
    else
      pure (← meth.isDefEqPure type appType, none)

  unless defEq do return (e, none, none)
  let (prf?, indEqs?) ←
    if let some (p, argEqs?) := d? then
      for argEq? in argEqs?[:rval.numParams] do
        assert! argEq? == none 
      pure (← meth.appPrfIrrelHEq type appType p e newCtorApp, .some (argEqs?[rval.numParams:].toArray))
    else
      pure (← meth.appPrfIrrel type e newCtorApp, .some (List.replicate rval.numIndices none).toArray)

  return (newCtorApp, prf?, indEqs?)

def expandEtaStruct (eType e : PExpr) : (PExpr × Option EExpr) :=
  eType.toExpr.withApp fun I args => Id.run do
  let .const I ls := I | return (e, none)
  let some ctor := getFirstCtor env I | return (e, none)
  let some (.ctorInfo info) := env.find? ctor | unreachable!
  let mut result := mkAppRange (.const ctor ls) 0 info.numParams args
  for i in [:info.numFields] do
    result := .app result (.proj I i e)
  pure (result.toPExpr, none)

/--
When `e` is of struct type, converts it into a constructor application using
projections.

For instance if we have `e : String`, it is converted into
`String.mk (String.data e)` (which is definitionally equal to `e` by struct
eta).
-/
def toCtorWhenStruct (inductName : Name) (e : PExpr) : m (PExpr × Option EExpr) := do
  if !isStructureLike env inductName || (e.toExpr.isConstructorApp?' env).isSome then
    return (e, none)
  let (eType, p?) ← meth.whnf (← meth.inferTypePure e)
  assert! p? == none
  if !eType.toExpr.getAppFn.isConstOf inductName then return (e, none)
  if (← meth.whnf (← meth.inferTypePure eType)).1 == Expr.prop.toPExpr then return (e, none)
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
    : m (Option (PExpr × Option EExpr)) := do
  let recFn := e.toExpr.getAppFn
  let .const recFnName ls := recFn | return none
  let some (.recInfo info) := env.find? recFnName | return none
  let recArgs := e.toExpr.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major' := recArgs[majorIdx]? | return none
  let major := major'.toPExpr
  let (majorWhnf, majorEqmajorWhnf?) ← meth.whnf major
  let (majorKWhnf, majorWhnfEqmajorKWhnf?, indEqs??) ← if info.k then toCtorWhenK env meth info majorWhnf else pure (majorWhnf, none, none)
  let majorEqmajorKWhnf? ← meth.appHEqTrans? major majorWhnf majorKWhnf majorEqmajorWhnf? majorWhnfEqmajorKWhnf?
  let (majorMaybeCtor, majorKWhnfEqMajorMaybeCtor?) ← match majorKWhnf.toExpr with
    | .lit l => pure (l.toConstructor.toPExpr, none)
    | _ => toCtorWhenStruct env meth info.getInduct majorKWhnf
  let majorEqMajorMaybeCtor? ← meth.appHEqTrans? major majorKWhnf majorMaybeCtor majorEqmajorKWhnf? majorKWhnfEqMajorMaybeCtor?
  let mut newRecArgs := recArgs.set! majorIdx majorMaybeCtor

  let indicesStartIdx := info.numParams + info.numMotives + info.numMinors

  let mut map := .insert default majorIdx majorEqMajorMaybeCtor?
  if let some indEqs? := indEqs?? then do
    for idx in [:indEqs?.size] do
      let indEq? := indEqs?[idx]!
      let indexIdx := indicesStartIdx + idx
      map := map.insert indexIdx (indEq?.map (fun (_, _, p) => p))
      if let some (_, e, _) := indEq? then
        newRecArgs := newRecArgs.set! indexIdx e

  let eNewMajor := mkAppN recFn newRecArgs |>.toPExpr
  -- (majorIdx, majorEqMajorMaybeCtor?)
  let (.true, eEqeNewMajor?) ← meth.isDefEqApp e eNewMajor 102 map | unreachable!
  let some rule := getRecRuleFor info majorMaybeCtor | return none
  let majorArgs := majorMaybeCtor.toExpr.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  -- get parameters from recursor application (recursor rules don't need the indices,
  -- as these are determined by the constructor and its parameters/fields)
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx newRecArgs
  -- get fields from constructor application
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs
  if majorIdx + 1 < newRecArgs.size then
    rhs := mkAppRange rhs (majorIdx + 1) newRecArgs.size newRecArgs
  return .some (rhs.toPExpr, eEqeNewMajor?)

end
