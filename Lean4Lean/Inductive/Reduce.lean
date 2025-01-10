import Lean.Structure
import Lean4Lean.Expr

namespace Lean

section
variable [Monad m] (env : Environment)
    (whnf : Nat → Expr → m Expr) (inferType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool)

def getFirstCtor (dName : Name) : Option Name := do
  let some (.inductInfo info) := env.find? dName | none
  info.ctors.head?

def mkNullaryCtor (type : Expr) (nparams : Nat) : Option (Expr × Name) :=
  type.withApp fun d args => do
  let .const dName ls := d | none
  let name ← getFirstCtor env dName
  return (mkAppRange (.const name ls) 0 nparams args, name)

def toCtorWhenK (rval : RecursorVal) (e : Expr) : m (Expr × Bool) := do
  assert! rval.k
  let appType ← whnf 1 (← inferType e)
  let .const appTypeI _ := appType.getAppFn | return (e, false)
  if appTypeI != rval.getMajorInduct then return (e, false)
  if appType.hasExprMVar then
    let appTypeArgs := appType.getAppArgs
    for h : i in [rval.numParams:appTypeArgs.size] do
      if (appTypeArgs[i]'h.2.1).hasExprMVar then return (e, false)
  let some (newCtorApp, newCtorName) := mkNullaryCtor env appType rval.numParams | return (e, false)
  unless ← isDefEq appType (← inferType newCtorApp) do return (e, false)
  if let (.const ctorName _) := e.getAppFn then
    if ctorName == newCtorName then
      if ← isDefEq e newCtorApp then return (e, false)
  return (newCtorApp, true)

def expandEtaStruct (eType e : Expr) : Expr :=
  eType.withApp fun I args => Id.run do
  let .const I ls := I | return e
  let some ctor := getFirstCtor env I | return e
  let some (.ctorInfo info) := env.find? ctor | unreachable!
  let mut result := mkAppRange (.const ctor ls) 0 info.numParams args
  for i in [:info.numFields] do
    result := .app result (.proj I i e)
  pure result

def toCtorWhenStruct (inductName : Name) (e : Expr) : m Expr := do
  if !isStructureLike env inductName || (e.isConstructorApp?' env).isSome then
    return e
  let eType ← whnf 2 (← inferType e)
  if !eType.getAppFn.isConstOf inductName then return e
  if (← whnf 3 (← inferType eType)) == .prop then return e
  return expandEtaStruct env eType e

def getRecRuleFor (rval : RecursorVal) (major : Expr) : Option RecursorRule := do
  let .const fn _ := major.getAppFn | none
  rval.rules.find? (·.ctor == fn)

set_option linter.unusedVariables false in
def inductiveReduceRec [Monad m] (env : Environment) (e : Expr)
    (whnf : Nat → Expr → m Expr) (trace : String → m Unit) (inferType : Expr → m Expr) (inferType' : Expr → m Expr) (isDefEq : Expr → Expr → m Bool) (kLikeReduction : Bool := true) :
    m (Option (Expr × Bool)) := do
  let .const recFn ls := e.getAppFn | return none
  let some (.recInfo info) := env.find? recFn | return none
  let recArgs := e.getAppArgs
  let majorIdx := info.getMajorIdx
  let some major' := recArgs[majorIdx]? | return none
  let mut major := major'
  let mut usedK := false
  -- let e' := mkAppN e.getAppFn recArgs[:majorIdx + 1]
  -- let eType' ← inferType' e
  if kLikeReduction then
    if info.k then
      (major, usedK) ← toCtorWhenK env whnf inferType isDefEq info major
  -- dbg_trace s!"DBG[28]: Reduce.lean:74: major={major}"
  match ← whnf 4 major with
  | .lit l => major := l.toConstructor
  | e => major ← toCtorWhenStruct env whnf inferType info.getMajorInduct e
  let some rule := getRecRuleFor info major | return none
  let majorArgs := major.getAppArgs
  if rule.nfields > majorArgs.size then return none
  if ls.length != info.levelParams.length then return none
  let mut rhs := rule.rhs.instantiateLevelParams info.levelParams ls
  rhs := mkAppRange rhs 0 info.getFirstIndexIdx recArgs
  rhs := mkAppRange rhs (majorArgs.size - rule.nfields) majorArgs.size majorArgs
  if majorIdx + 1 < recArgs.size then
    rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
  return (rhs, usedK)

end
