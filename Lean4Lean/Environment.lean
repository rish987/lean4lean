import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive

namespace Lean
namespace Environment
open TypeChecker

open private add from Lean.Environment

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M Unit := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← check v.type v.levelParams
  _ ← ensureSort sort v.type

def addAxiom (env : Environment) (v : AxiomVal) (opts : TypeCheckerOpts := {}) :
    Except KernelException (Environment × Data) := do
  let (_, s) ← (checkConstantVal env v.toConstantVal).run env
    (safety := if v.isUnsafe then .unsafe else .safe) (opts := opts)
  return (add env (.axiomInfo v), s.data)

def addDefinition (env : Environment) (v : DefinitionVal) (opts : TypeCheckerOpts := {}) :
    Except KernelException (Environment × Data) := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    _ ← (checkConstantVal env v.toConstantVal).run env (safety := .unsafe)
    let env' := add env (.opaqueInfo {v with isUnsafe := false})
    checkNoMVarNoFVar env' v.name v.value
    let (_, s) ← M.run env' (safety := .unsafe) (lctx := {}) opts do
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env' (.defnDecl v) valType
    return (add env (.defnInfo v), s.data)
  else
    let (_, s) ← M.run env (safety := .safe) (lctx := {}) opts do
      checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.defnDecl v) valType
    return (add env (.defnInfo v), s.data)

def addTheorem (env : Environment) (v : TheoremVal) (opts : TypeCheckerOpts := {}) :
    Except KernelException (Environment × Data) := do
  -- TODO(Leo): we must add support for handling tasks here
  let (_, s) ← M.run env (safety := .safe) (lctx := {}) opts do
    if !(← isProp v.type) then
      throw <| .thmTypeIsNotProp env v.name v.type
    checkConstantVal env v.toConstantVal
    checkNoMVarNoFVar env v.name v.value
    let valType ← TypeChecker.check v.value v.levelParams
    if !(← isDefEq valType v.type) then
      throw <| .declTypeMismatch env (.thmDecl v) valType
  return (add env (.thmInfo v), s.data)

def addOpaque (env : Environment) (v : OpaqueVal) (opts : TypeCheckerOpts := {}) :
    Except KernelException (Environment × Data) := do
  let (_, s) ← M.run env (safety := .safe) (lctx := {}) opts do
    checkConstantVal env v.toConstantVal
    let valType ← TypeChecker.check v.value v.levelParams
    if !(← isDefEq valType v.type) then
      throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return (add env (.opaqueInfo v), s.data)

def addMutual (env : Environment) (vs : List DefinitionVal) (opts : TypeCheckerOpts := {}) :
    Except KernelException (Environment × Data) := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let _ ← M.run env (safety := v₀.safety) (lctx := {}) opts do
    for v in vs do
      if v.safety != v₀.safety then
        throw <| .other
          "invalid mutual definition, declarations must have the same safety annotation"
      checkConstantVal env v.toConstantVal
  let mut env' := env
  for v in vs do
    env' := add env' (.opaqueInfo {v with isUnsafe := false})
  let (_, s) ← M.run env' (safety := v₀.safety) (lctx := {}) opts do
    for v in vs do
      checkNoMVarNoFVar env' v.name v.value
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valType
  return (env', s.data)

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Environment) (decl : @& Declaration) (opts : TypeCheckerOpts) :
    Except KernelException (Environment × Data) := do
  match decl with
  | .axiomDecl v => addAxiom env v opts
  | .defnDecl v => addDefinition env v opts 
  | .thmDecl v => addTheorem env v opts
  | .opaqueDecl v => addOpaque env v opts
  | .mutualDefnDecl v => addMutual env v opts
  | .quotDecl => pure (← addQuot env, {})
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe opts
    pure (← addInductive env lparams nparams types isUnsafe allowPrimitive opts, {})
