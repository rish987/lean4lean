import Lean.Structure
import Lean4Lean.Expr
import Lean4Less.EExpr
import Lean4Less.Ext

namespace Lean4Less
open Lean

section

structure ExtMethodsR (m : Type → Type u) extends ExtMethods m where
  isDefEqApp' : PExpr → PExpr → Std.HashMap Nat (Option EExpr) → m (Bool × Option (EExpr × Array (Option (PExpr × PExpr × EExpr))))
  isDefEqApp : PExpr → PExpr → Std.HashMap Nat (Option EExpr) → m (Bool × Option EExpr)
  smartCast : PExpr → PExpr → PExpr → m PExpr

variable [Monad m] (env : Environment)
  (meth : ExtMethodsR m)

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
def toCtorWhenK (rval : RecursorVal) (e : PExpr) : m (PExpr × Option (EExpr)) := do
  assert! rval.k
  let type ← meth.whnfPure (← meth.inferTypePure e 101) 107
  let .const typeI _ := type.toExpr.getAppFn | return (e, none)
  if typeI != rval.getInduct then return (e, none)
  if type.toExpr.hasExprMVar then
    let typeArgs := type.toExpr.getAppArgs
    for h : i in [rval.numParams:typeArgs.size] do
      if (typeArgs[i]'h.2).hasExprMVar then return (e, none)
  let some (newCtorApp, newCtorName) := mkNullaryCtor env type rval.numParams | return (e, none)
  if let (.const ctorName _) := e.toExpr.getAppFn then
    if ctorName == newCtorName then
      if let true ← meth.isDefEqPure e newCtorApp then
        return (e, none)
  let appType ← meth.inferTypePure newCtorApp 102
  -- check that the indices of types of `e` and `newCtorApp` match
  let (true, pt?) ← meth.isDefEq type appType | return (e, none)
  let (prf?) ←
    if let some pt := pt? then
      pure (← meth.appPrfIrrelHEq type appType pt e newCtorApp)
    else
      pure (← meth.appPrfIrrel type e newCtorApp)

  return (newCtorApp, prf?)

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
  let eType ← meth.whnfPure (← meth.inferTypePure e 103) 108
  if !eType.toExpr.getAppFn.isConstOf inductName then return (e, none)
  if (← meth.whnf (← meth.inferTypePure eType 104)).1 == Expr.prop.toPExpr then return (e, none)
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
  let recType := info.type.instantiateLevelParams info.levelParams ls
  let recArgs := e.toExpr.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major' := recArgs[majorIdx]? | return none
  let major := major'.toPExpr
  let (majorWhnf, majorEqmajorWhnf?) ← meth.whnf major
  let (majorKWhnf, majorWhnfEqmajorKWhnf?) ← if info.k then toCtorWhenK env meth info majorWhnf else pure (majorWhnf, none)
  let majorEqmajorKWhnf? ← meth.appHEqTrans? major majorWhnf majorKWhnf majorEqmajorWhnf? majorWhnfEqmajorKWhnf?
  let (majorMaybeCtor, majorKWhnfEqMajorMaybeCtor?) ← match majorKWhnf.toExpr with
    | .lit l => pure (l.toConstructor.toPExpr, none)
    | _ => toCtorWhenStruct env meth info.getInduct majorKWhnf
  let majorEqMajorMaybeCtor? ← meth.appHEqTrans? major majorKWhnf majorMaybeCtor majorEqmajorKWhnf? majorKWhnfEqMajorMaybeCtor?
  -- (majorIdx, majorEqMajorMaybeCtor?)
  let some rule := getRecRuleFor info majorMaybeCtor | return none
  let majorArgs := majorMaybeCtor.toExpr.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls

  let type ← meth.whnfPure (← meth.inferTypePure major 105) 105
  let newType ← meth.whnfPure (← meth.inferTypePure majorMaybeCtor 106) 106
  let (defEq, d?) ←
    if type.toExpr.isApp then
      meth.isDefEqApp' type newType default
    else
      pure (← meth.isDefEqPure type newType, none)

  assert! defEq == true

  let (paramEqs?, indEqs?) ←
    if let some (_, argEqs?) := d? then
      pure (argEqs?[:info.numParams].toArray, argEqs?[info.numParams:].toArray)
    else
      pure ((List.replicate (info.numParams) none).toArray, (List.replicate (info.numIndices) none).toArray)

  let motivesMinorsEqs? : Array (Option (PExpr × PExpr × EExpr)) ← do
    if paramEqs?.any (·.isSome) then
      let rec loop1 (type origType : Expr) (n : Nat) := do
        match (← meth.whnfPure type.toPExpr 101).toExpr, (← meth.whnfPure origType.toPExpr 102).toExpr, n with
      | .forallE _ _ body _, .forallE _ _ origBody _, m + 1 => 
        let idx := info.numParams - n
        let origParam := recArgs[idx]!
        let param := paramEqs?[idx]!.map (fun (_, s, _) => s.toExpr) |>.getD origParam
        loop1 (body.instantiate1 param) (origBody.instantiate1 origParam) m
      | body, origBody, m =>
        assert! m == 0
        pure (body, origBody)
      let (type', origType') ← loop1 recType recType info.numParams

      let rec loop2 (type origType : Expr) (n : Nat) (ret : (Array (Option (PExpr × PExpr × EExpr)))) := do
        match (← meth.whnfPure type.toPExpr 103).toExpr, (← meth.whnfPure origType.toPExpr 104).toExpr, n with
        | .forallE _ dom body _, .forallE _ origDom origBody _, m + 1 => 
          let idx := (info.numMotives + info.numMinors) - n + info.numParams
          let origMotiveMinor := recArgs[idx]!.toPExpr
          let newMotiveMinor ← meth.smartCast origDom.toPExpr dom.toPExpr origMotiveMinor
          let (true, origMotiveMinorEqnewMotiveMinor?) ← meth.isDefEq origMotiveMinor newMotiveMinor | unreachable!
          let ret := ret.push (origMotiveMinorEqnewMotiveMinor?.map fun p => (origMotiveMinor, newMotiveMinor, p))
          loop2 (body.instantiate1 newMotiveMinor) (origBody.instantiate1 origMotiveMinor) m ret
        | _, _, m =>
          assert! m == 0
          pure ret

      let ret ← loop2 type' origType' (info.numMotives + info.numMinors) #[]
      pure ret
    else
      pure (List.replicate (info.numMotives + info.numMinors) (none : Option (PExpr × PExpr × EExpr))).toArray

  let mut newRecArgs := recArgs.set! majorIdx majorMaybeCtor
  let mut map := .insert default majorIdx majorEqMajorMaybeCtor?

  for idx in [:paramEqs?.size] do
    let indEq? := paramEqs?[idx]!
    map := map.insert idx (indEq?.map (fun (_, _, p) => p))
    if let some (_, e, _) := indEq? then
      newRecArgs := newRecArgs.set! idx e

  let motivesStartIdx := info.numParams
  for idx in [:motivesMinorsEqs?.size] do
    let indEq? := motivesMinorsEqs?[idx]!
    let recIdx := motivesStartIdx + idx
    map := map.insert recIdx (indEq?.map (fun (_, _, p) => p))
    if let some (_, e, _) := indEq? then
      newRecArgs := newRecArgs.set! recIdx e

  let indicesStartIdx := info.numParams + info.numMotives + info.numMinors
  for idx in [:indEqs?.size] do
    let indEq? := indEqs?[idx]!
    let recIdx := indicesStartIdx + idx
    map := map.insert recIdx (indEq?.map (fun (_, _, p) => p))
    if let some (_, e, _) := indEq? then
      newRecArgs := newRecArgs.set! recIdx e

  let eNewMajor := mkAppN recFn newRecArgs |>.toPExpr
  -- get parameters from recursor application (recursor rules don't need the indices,
  -- as these are determined by the constructor and its parameters/fields)
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx newRecArgs
  -- get fields from constructor application
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs
  if majorIdx + 1 < newRecArgs.size then
    rhs := mkAppRange rhs (majorIdx + 1) newRecArgs.size newRecArgs
  let (.true, eEqeNewMajor?) ← meth.isDefEqApp e eNewMajor map | unreachable!
  return .some (rhs.toPExpr, eEqeNewMajor?)

end
