import Lean
import Lean4Lean.Replay
import Lean4Lean.Util

open Lean

namespace Lean4Lean

open private Lean.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.irBaseExts from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment
open private Lean.Environment.asyncConstsMap from Lean.Environment
open private Lean.Environment.asyncCtx? from Lean.Environment
open private Lean.Environment.importRealizationCtx? from Lean.Environment
open private Lean.Environment.localRealizationCtxMap from Lean.Environment
open private Lean.Environment.serverBaseExts from Lean.Environment
open private Lean.Environment.allRealizations from Lean.Environment
open private Lean.Environment.base from Lean.Environment
open private Lean.VisibilityMap from Lean.Environment
open private Lean.VisibilityMap.private from Lean.Environment
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Environment.updateBaseAfterKernelAdd from Lean.Environment

def updateKEnvHeader (kernel : Kernel.Environment) (newHeader : EnvironmentHeader) : Kernel.Environment :=
  Lean.Kernel.Environment.mk kernel.constants kernel.quotInit kernel.diagnostics (kernel.const2ModIdx) (Lean.Kernel.Environment.extensions kernel) (Lean.Kernel.Environment.irBaseExts kernel) newHeader

def updateEnvHeader (env : Environment) (newHeader : EnvironmentHeader) : Environment :=
  let base := Lean.Environment.base env
  let prv := Lean.VisibilityMap.private base
  let newPrv := updateKEnvHeader prv newHeader
  let pub := Lean.VisibilityMap.public base
  let newPub := updateKEnvHeader pub newHeader
  let newBase := Lean.VisibilityMap.mk newPrv newPub
  Lean.Environment.mk newBase (Lean.Environment.serverBaseExts env) (Lean.Environment.checked env) (Lean.Environment.asyncConstsMap env) (Lean.Environment.asyncCtx? env) (Lean.Environment.importRealizationCtx? env) (Lean.Environment.localRealizationCtxMap env) (Lean.Environment.allRealizations env) (env.isExporting)

def updateBaseAfterKernelAdd (env : Environment) (kernel : Kernel.Environment) : Environment :=
  let newKernel := Lean.Kernel.Environment.mk kernel.constants kernel.quotInit kernel.diagnostics (env.toKernelEnv.const2ModIdx) (Lean.Kernel.Environment.extensions env.toKernelEnv) (Lean.Kernel.Environment.irBaseExts env.toKernelEnv) (env.toKernelEnv.header)
  Lean.Environment.mk (Lean.VisibilityMap.mk newKernel newKernel) (Lean.Environment.serverBaseExts env) (.pure newKernel) (Lean.Environment.asyncConstsMap env) (Lean.Environment.asyncCtx? env) (Lean.Environment.importRealizationCtx? env) (Lean.Environment.localRealizationCtxMap env) (Lean.Environment.allRealizations env) (env.isExporting)

def updateConst2ModIdx (env : Kernel.Environment) (const2ModIdx : Std.HashMap Name ModuleIdx) : Kernel.Environment := Id.run $ do
  let mut newConst2ModIdx := env.const2ModIdx.union const2ModIdx
  let newKernel := Lean.Kernel.Environment.mk env.constants env.quotInit env.diagnostics newConst2ModIdx (Lean.Kernel.Environment.extensions env) (Lean.Kernel.Environment.irBaseExts env) (env.header)
  pure newKernel

def getDepConstsEnv (env : Environment) (consts : Array Name) (overrides : Std.HashMap Name ConstantInfo) : IO $ Std.HashMap Name ConstantInfo := do
  let mut (_, {map := map, ..}) ← ((Deps.namedConstDeps consts).toIO { options := default, fileName := "", fileMap := default } {env} {env, overrides})
  pure map

def checkConstants (env : Lean.Environment) (consts : Lean.NameSet) (addDeclFn : Declaration → M Unit) (initConsts : Array Name := #[]) (printErr := false) (opts : TypeCheckerOpts := {}) (op : String := "typecheck") (printProgress := false) (interactive : Bool := false) (dbgOnly := false) (overrides : Std.HashMap Name ConstantInfo) (deps := true) (write := true) : IO (Lean.NameSet × Environment) := do
  let mut onlyConstsToTrans : Lean.NameSet := default

  -- constants that should be skipped on account of already having been typechecked
  let mut skipConsts : Lean.NameSet := default
  -- constants that should throw an error if encountered on account of having previously failed to typecheck
  let mut errConsts : Lean.NameSet := default
  let mut modEnv := updateBaseAfterKernelAdd env (← Lean.mkEmptyEnvironment).toKernelEnv
  -- let modData ← mkModuleData modEnv
  -- let (_, s) ← importModulesCore modData.imports
  --   |>.run (s := { moduleNameSet := ({} : NameHashSet).insert modEnv.mainModule })
  -- for h : modIdx in [0:s.moduleData.size] do
  --   let mod := s.moduleData[modIdx]
  --   if mod.constants.any (·.name == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!) || mod.constNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!) || mod.extraConstNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!) then
  --     dbg_trace s!"DBG[57]: Commands.lean:91 {mod.constants.any (·.name == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!)}, {mod.constNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!)}, {mod.extraConstNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!)}"

  let loop const modEnv skipConsts errConsts onlyConstsToTrans printProgress := do
    try
      let mut modEnv := modEnv
      let mut skipConsts := skipConsts
      if not $ skipConsts.contains const then
        let map' ← do -- FIXME why is this needed?
          -- if let some ci := overrides[const]? then
          --   getDepConstsEnv env #[ci.name] overrides
          -- else
            getDepConstsEnv env #[const] overrides
        let mut map := map'
        let mapConsts := map.fold (init := default) fun acc const _ => acc.insert const

        let erredConsts : Lean.NameSet := mapConsts ∩ errConsts
        if erredConsts.size > 0 then
          throw $ IO.userError s!"Encountered untypecheckable constant dependencies: {erredConsts.toList}."

        let skippedConsts : Lean.NameSet := mapConsts ∩ skipConsts
        for skipConst in skippedConsts do
          map := map.erase skipConst

        let rp modEnv := do
          let mut modEnv := modEnv
          if dbgOnly then
            let (env', _) ← replay addDeclFn {newConstants := map.erase const, overrides, opts := opts} modEnv.toKernelEnv (printProgress := printProgress) (op := op)
            modEnv := updateBaseAfterKernelAdd modEnv env'
          else
            if deps then
              let (env, _) ← replay addDeclFn {newConstants := map, overrides, opts} modEnv.toKernelEnv (printProgress := printProgress) (op := op)
              modEnv := updateBaseAfterKernelAdd modEnv env
            else
              for (_, ci) in map.erase const |>.toList do
                modEnv := updateBaseAfterKernelAdd modEnv (modEnv.toKernelEnv.add ci)
              let (env, _) ← replay addDeclFn {newConstants := Std.HashMap.insert default const (map.get! const), overrides, opts} modEnv.toKernelEnv (printProgress := printProgress) (op := op)
              modEnv := updateBaseAfterKernelAdd modEnv env
          pure modEnv

        if (not interactive) && (not (initConsts.contains const)) && consts.size == 1 && const != `temp then
          let outName := (if dbgOnly then const.toString ++ "_dbg" else const.toString) ++ s!".olean"
          let outDir := ((← IO.Process.getCurrentDir).join "only_out")
          IO.FS.createDirAll outDir
          let outPath := outDir.join outName
          if dbgOnly && (← System.FilePath.pathExists outPath) then
            let (mod, region) ← readModuleData outPath
            let module := modEnv.mainModule
            let (_, s) ← importModulesCore mod.imports |>.run 
            modEnv ← finalizeImport s mod.imports {} 0 false false
            for const in mod.constants do
              modEnv := updateBaseAfterKernelAdd modEnv (modEnv.toKernelEnv.add const)
            modEnv := modEnv.setMainModule module
          else
            modEnv ← rp modEnv
            if write then
              -- let modData ← mkModuleData modEnv
              -- let (_, s) ← importModulesCore modData.imports
              --   |>.run (s := { moduleNameSet := ({} : NameHashSet).insert modEnv.mainModule })
              -- for h : modIdx in [0:s.moduleData.size] do
              --   let mod := s.moduleData[modIdx]
              --   if mod.constants.any (·.name == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!) || mod.constNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!) || mod.extraConstNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!) then
              --     dbg_trace s!"DBG[57]: Commands.lean:91 {mod.constants.any (·.name == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!)}, {mod.constNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!)}, {mod.extraConstNames.any (· == `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!)}"
              -- dbg_trace s!"DBG[53]: Commands.lean:94 {modEnv.contains `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!}, {outPath}"
              writeModule modEnv outPath
        else
          modEnv ← rp modEnv

        if dbgOnly then
          -- dbg_trace s!"DBG[56]: Commands.lean:83 {modEnv.contains `Std.DTreeMap.Internal.Impl.balanceR!_eq_balance!}"
          let (modEnv', _) ← replay addDeclFn {newConstants := Std.HashMap.insert default const (map.get! const), overrides, opts} modEnv.toKernelEnv (printProgress := printProgress) (op := op)
          modEnv := updateBaseAfterKernelAdd modEnv modEnv'
        skipConsts := skipConsts.union mapConsts -- TC success, so want to skip in future runs (already in environment)
      let onlyConstsToTrans := onlyConstsToTrans.insert const
      pure (modEnv, skipConsts, errConsts, onlyConstsToTrans)
    catch
    | e =>
      if printErr then
        dbg_trace s!"Error {op}ing constant `{const}`: {e.toString}"
      let errConsts := errConsts.insert const
      pure (modEnv, skipConsts, errConsts, onlyConstsToTrans)

  for const in initConsts do 
    (modEnv, skipConsts, errConsts, onlyConstsToTrans) ← loop const modEnv skipConsts errConsts onlyConstsToTrans false
  for const in consts.toList do 
    (modEnv, skipConsts, errConsts, onlyConstsToTrans) ← loop const modEnv skipConsts errConsts onlyConstsToTrans printProgress
  pure (onlyConstsToTrans, modEnv)

end Lean4Lean

-- elab "#check_l4l " i:ident : command => do
--   let env ← getEnv
--   discard $ Lean4Lean.checkConstants (printErr := true) env (.insert default i.getId) @Lean4Lean.replay
  -- match macroRes with
  -- | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  -- | none =>
  --   let kind := c.raw.getKind
  --   let elabs := commandElabAttribute.getEntries (←getEnv) kind
  --   match elabs with
  --   | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
  --   | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"
