import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive

namespace Lean
namespace Environment
open TypeChecker

open private add from Lean.Environment

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M (PExpr × Level) := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let (vtypeType, vtype'?) ← check v.type v.levelParams
  let vtype' := vtype'?.getD v.type.toPExpr
  let (sort, vtypeTypeEqsort?) ← ensureSort vtypeType vtype'
  let .sort lvl := sort.toExpr | unreachable!
  let vtype'' := maybeCast vtypeTypeEqsort? lvl.succ vtypeType sort vtype'
  pure (vtype'', lvl)

def addAxiom (env : Environment) (v : AxiomVal) :
    Except KernelException (Environment × AxiomVal) := do
  let (type, _) ← (checkConstantVal env v.toConstantVal).run env
    (safety := if v.isUnsafe then .unsafe else .safe)
  return (add env (.axiomInfo v), {v with type})

def addDefinition (env : Environment) (v : DefinitionVal) :
    Except KernelException (Environment × DefinitionVal) := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    let (type, _) ← (checkConstantVal env v.toConstantVal).run env (safety := .unsafe)
    let env' := add env (.defnInfo v)
    checkNoMVarNoFVar env' v.name v.value
    M.run env' (safety := .unsafe) (lctx := {}) do
      let (vvalueType, _) ← TypeChecker.check v.value v.levelParams
      let (defEq, _) ← isDefEq vvalueType type
      if !defEq then
        throw <| .declTypeMismatch env' (.defnDecl v) vvalueType
    return (env', v) -- TODO handle unsafe defs
  else
    let (type, value) ← M.run env (safety := .safe) (lctx := {}) do
      let (type, lvl) ← checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
      checkNoMVarNoFVar env v.name v.value
      let (vvalueType, vvalue'?) ← TypeChecker.check v.value v.levelParams
      let vvalue' := vvalue'?.getD v.value.toPExpr
      let (defEq, vvalueTypeEqtype?) ← isDefEq vvalueType type
      if !defEq then
        throw <| .declTypeMismatch env (.defnDecl v) vvalueType
      pure (type, maybeCast vvalueTypeEqtype? lvl vvalueType type vvalue')
    return (add env (.defnInfo v), {v with type, value})

def addTheorem (env : Environment) (v : TheoremVal) :
    Except KernelException (Environment × TheoremVal) := do
  -- TODO(Leo): we must add support for handling tasks here
  M.run env (safety := .safe) (lctx := {}) do
    checkConstantVal env v.toConstantVal
    checkNoMVarNoFVar env v.name v.value
    let valType ← TypeChecker.check v.value v.levelParams
    if !(← isDefEq valType v.type) then
      throw <| .declTypeMismatch env (.thmDecl v) valType
  return add env (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) :
    Except KernelException (Environment × OpaqueVal) := do
  M.run env (safety := .safe) (lctx := {}) do
    checkConstantVal env v.toConstantVal
    let valType ← TypeChecker.check v.value v.levelParams
    if !(← isDefEq valType v.type) then
      throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return add env (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal) :
    Except KernelException (Environment × List DefinitionVal) := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  M.run env (safety := v₀.safety) (lctx := {}) do
    for v in vs do
      if v.safety != v₀.safety then
        throw <| .other
          "invalid mutual definition, declarations must have the same safety annotation"
      checkConstantVal env v.toConstantVal
  let mut env' := env
  for v in vs do
    env' := add env' (.defnInfo v)
  M.run env (safety := v₀.safety) (lctx := {}) do
    for v in vs do
      checkNoMVarNoFVar env' v.name v.value
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valType
  return env'

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Environment) (decl : @& Declaration) :
    Except KernelException (Environment × Declaration) := do
  match decl with
  | .axiomDecl v =>
    let (env, val) ← addAxiom env v
    pure (env, .axiomDecl val)
  | .defnDecl v =>
    let (env, val) ← addDefinition env v
    pure (env, .defnDecl val)
  | .thmDecl v =>
    let (env, val) ← addTheorem env v
    pure (env, .thmDecl val)
  | .opaqueDecl v =>
    let (env, val) ← addOpaque env v
    pure (env, .opaqueDecl val)
  | .mutualDefnDecl v =>
    let (env, val) ← addMutual env v
    pure (env, .mutualDefnDecl val)
  | .quotDecl => pure (← addQuot env, Declaration.quotDecl)
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    pure (← addInductive env lparams nparams types isUnsafe allowPrimitive, decl) -- TODO handle any possible patching in inductive type declarations (low priority)
