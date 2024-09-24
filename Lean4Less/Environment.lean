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

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M (PExpr) := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let (typeType, type'?) ← check v.type v.levelParams
  let type' := type'?.getD v.type.toPExpr
  let (sort, typeTypeEqSort?) ← ensureSort typeType v.levelParams type'
  let type'' ← maybeCast typeTypeEqSort? typeType sort type' v.levelParams
  pure type''

def patchAxiom (env : Environment) (v : AxiomVal) :
    Except KernelException ConstantInfo := do
  let type ← (checkConstantVal env v.toConstantVal).run env v.name
    (safety := if v.isUnsafe then .unsafe else .safe)
  let v := {v with type}
  return .axiomInfo v

def patchDefinition (env : Environment) (v : DefinitionVal) :
    Except KernelException ConstantInfo := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    let type ← (checkConstantVal env v.toConstantVal).run env v.name (safety := .unsafe)
    let env' := add env (.defnInfo {v with type})
    checkNoMVarNoFVar env' v.name v.value
    M.run env' v.name (safety := .unsafe) (lctx := {}) do
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      let value' := value'?.getD v.value.toPExpr
      let (defEq, _) ← isDefEq valueType type v.levelParams
      if !defEq then
        throw <| .declTypeMismatch env' (.defnDecl v) valueType
      let value ← smartCast valueType type value' v.levelParams
      let v := {v with type, value}
      return .defnInfo v
  else
    M.run env v.name (safety := .safe) (lctx := {}) do
      -- dbg_trace s!"DBG[25]: Environment.lean:49: v.name={v.name}"
      let type ← checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
      checkNoMVarNoFVar env v.name v.value
      -- dbg_trace s!"DBG[34]: Environment.lean:52 (after checkNoMVarNoFVar env v.name v.value)"
      let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
      -- dbg_trace s!"DBG[98]: Environment.lean:54: valueType={valueType}"
      -- dbg_trace s!"DBG[100]: Environment.lean:51: type={type}"
      let value' := value'?.getD v.value.toPExpr
      -- dbg_trace s!"DBG[33]: Environment.lean:54 (after let value := value?.getD v.value.toPExpr)"
      let (defEq, _) ← isDefEq valueType type v.levelParams
      -- dbg_trace s!"DBG[31]: Environment.lean:57: valueTypeEqtype?={valueTypeEqtype?}"

      if !defEq then
        throw <| .declTypeMismatch env (.defnDecl v) valueType

      let value ← smartCast valueType type value' v.levelParams
      let v := {v with type, value}
      -- dbg_trace s!"DBG[35]: Environment.lean:64 (after let v := v with type, value)"
      return (.defnInfo v)

def patchTheorem (env : Environment) (v : TheoremVal) :
    Except KernelException ConstantInfo := do
  -- TODO(Leo): we must add support for handling tasks here
  let (type, value) ← M.run env v.name (safety := .safe) (lctx := {}) do
    let type ← checkConstantVal env v.toConstantVal
    checkNoMVarNoFVar env v.name v.value
    let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
    let value' := value'?.getD v.value.toPExpr
    let (defEq, _) ← isDefEq valueType type v.levelParams
    if !defEq then
      throw <| .declTypeMismatch env (.thmDecl v) valueType
    pure (type, ← smartCast valueType type value' v.levelParams)
  let v := {v with type, value}
  return .thmInfo v

def patchOpaque (env : Environment) (v : OpaqueVal) :
    Except KernelException ConstantInfo := do
  let (type, value) ← M.run env v.name (safety := .safe) (lctx := {}) do
    let type ← checkConstantVal env v.toConstantVal
    let (valueType, value'?) ← TypeChecker.check v.value v.levelParams
    let value' := value'?.getD v.value.toPExpr
    let (defEq, _) ← isDefEq valueType type v.levelParams
    if !defEq then
      throw <| .declTypeMismatch env (.opaqueDecl v) valueType
    pure (type, ← smartCast valueType type value' v.levelParams)
  let v := {v with type, value}
  return .opaqueInfo v

def patchMutual (env : Environment) (vs : List DefinitionVal) :
    Except KernelException (List ConstantInfo) := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let types ← M.run env `mutual (safety := v₀.safety) (lctx := {}) do
    let mut types := []
    for v in vs do
      if v.safety != v₀.safety then
        throw <| .other
          "invalid mutual definition, declarations must have the same safety annotation"
      let type ← checkConstantVal env v.toConstantVal
      types := types.append [type]
    pure types
  let mut env' := env
  let mut vs' := []
  for (type, v) in types.zip vs do
    let v' := {v with type}
    env' := add env' (.defnInfo v')
    vs' := vs'.append [v']
  M.run env' `mutual (safety := v₀.safety) (lctx := {}) do
    let mut newvs' := #[]
    for (v', type) in vs'.zip types do
      checkNoMVarNoFVar env' v'.name v'.value
      let (valueType, value'?) ← TypeChecker.check v'.value v'.levelParams
      let value' := value'?.getD v'.value.toPExpr
      let (defEq, _) ← isDefEq valueType type v'.levelParams
      if !defEq then
        throw <| .declTypeMismatch env' (.mutualDefnDecl vs') valueType
      let value ← smartCast valueType type value' vs[0]!.levelParams
      newvs' := newvs'.append #[{v' with value}]
    return newvs'.map .defnInfo |>.toList

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Environment) (decl : @& Declaration) :
    Except KernelException Environment := do
  match decl with
  | .axiomDecl v =>
    let v ← patchAxiom env v
    return add env v
  | .defnDecl v =>
    let v ← patchDefinition env v
    return add env v
  | .thmDecl v =>
    let v ← patchTheorem env v
    return add env v
  | .opaqueDecl v =>
    let v ← patchOpaque env v
    return add env v
  | .mutualDefnDecl vs =>
    let vs ← patchMutual env vs
    return vs.foldl (init := env) (fun env v => add env v)
  | .quotDecl => addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    addInductive env lparams nparams types isUnsafe allowPrimitive -- TODO handle any possible patching in inductive type declarations (low priority)