import Lean4Less.TypeChecker
import Lean4Less.Quot
import Lean4Less.Inductive.Add
import Lean4Less.Primitive

namespace Lean4Less
namespace Environment
open TypeChecker

open private add from Lean.Environment
open Lean
open Lean.Environment

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M (PExpr × Level) := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let (typeType, type'?) ← check v.type v.levelParams
  let type' := type'?.getD v.type.toPExpr
  let (sort, typeTypeEqSort?) ← ensureSort typeType type'
  let .sort lvl := sort.toExpr | unreachable!
  let type'' := maybeCast typeTypeEqSort? lvl.succ typeType sort type'
  pure (type'', lvl)

def addAxiom (env : Environment) (v : AxiomVal) :
    Except KernelException Environment := do
  let (type, _) ← (checkConstantVal env v.toConstantVal).run env
    (safety := if v.isUnsafe then .unsafe else .safe)
  let v := {v with type}
  return add env (.axiomInfo v)

def addDefinition (env : Environment) (v : DefinitionVal) :
    Except KernelException Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    let (type, _) ← (checkConstantVal env v.toConstantVal).run env (safety := .unsafe)
    let env' := add env (.defnInfo v)
    checkNoMVarNoFVar env' v.name v.value
    M.run env' (safety := .unsafe) (lctx := {}) do
      let (valueType, _) ← TypeChecker.check v.value v.levelParams
      let (defEq, _) ← isDefEq valueType type
      if !defEq then
        throw <| .declTypeMismatch env' (.defnDecl v) valueType
    return env' -- TODO handle unsafe defs (low priority)
  else
    let (type, value) ← M.run env (safety := .safe) (lctx := {}) do
      let (type, lvl) ← checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
      checkNoMVarNoFVar env v.name v.value
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      let value' := value'?.getD v.value.toPExpr
      let (defEq, valueTypeEqtype?) ← isDefEq valueType type
      if !defEq then
        throw <| .declTypeMismatch env (.defnDecl v) valueType
      pure (type, maybeCast valueTypeEqtype? lvl valueType type value')
    let v := {v with type, value}
    return add env (.defnInfo v)

def addTheorem (env : Environment) (v : TheoremVal) :
    Except KernelException Environment := do
  -- TODO(Leo): we must add support for handling tasks here
  let (type, value) ← M.run env (safety := .safe) (lctx := {}) do
    let (type, lvl) ← checkConstantVal env v.toConstantVal
    checkNoMVarNoFVar env v.name v.value
    let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
    let value' := value'?.getD v.value.toPExpr
    let (defEq, valueTypeEqtype?) ← isDefEq valueType type
    if !defEq then
      throw <| .declTypeMismatch env (.thmDecl v) valueType
    pure (type, maybeCast valueTypeEqtype? lvl valueType type value')
  let v := {v with type, value}
  return add env (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) :
    Except KernelException Environment := do
  let (type, value) ← M.run env (safety := .safe) (lctx := {}) do
    let (type, lvl) ← checkConstantVal env v.toConstantVal
    let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
    let value' := value'?.getD v.value.toPExpr
    let (defEq, valueTypeEqtype?) ← isDefEq valueType type
    if !defEq then
      throw <| .declTypeMismatch env (.opaqueDecl v) valueType
    pure (type, maybeCast valueTypeEqtype? lvl valueType type value')
  let v := {v with type, value}
  return add env (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal) :
    Except KernelException Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let vs' ← M.run env (safety := v₀.safety) (lctx := {}) do
    let mut vs' := #[]
    for v in vs do
      if v.safety != v₀.safety then
        throw <| .other
          "invalid mutual definition, declarations must have the same safety annotation"
      let (type, _) ← checkConstantVal env v.toConstantVal
      vs' := vs'.append #[{v with type}]
    pure vs'
  let mut env' := env
  for v' in vs' do
    env' := add env' (.defnInfo v')
  M.run env (safety := v₀.safety) (lctx := {}) do
    for v in vs do
      checkNoMVarNoFVar env' v.name v.value
      let (valueType, _) ← TypeChecker.check v.value v.levelParams
      let (defEq, _) ← isDefEq valueType v.type.toPExpr
      if !defEq then
        throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valueType
  return env' -- TODO handle mutual defs (low priority)

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Environment) (decl : @& Declaration) :
    Except KernelException Environment := do
  match decl with
  | .axiomDecl v =>
    let env ← addAxiom env v
    pure env
  | .defnDecl v =>
    let env ← addDefinition env v
    let some (.defnInfo v') := env.find? v.name | throw $ .other "unreachable"
    pure env
  | .thmDecl v =>
    let env ← addTheorem env v
    pure env
  | .opaqueDecl v =>
    let env ← addOpaque env v
    pure env
  | .mutualDefnDecl v =>
    let env ← addMutual env v
    pure env
  | .quotDecl => addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    addInductive env lparams nparams types isUnsafe allowPrimitive -- TODO handle any possible patching in inductive type declarations (low priority)
