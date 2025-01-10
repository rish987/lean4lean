import Lean
import Lean4Lean.Replay
import Lean4Lean.Util

open Lean

namespace Lean4Lean

open private add from Lean.Environment
open private Environment.mk from Lean.Environment

def getDepConstsEnv (env : Environment) (consts : Array Name) : IO $ Std.HashMap Name ConstantInfo := do
  let mut (_, {map := map, ..}) ← ((Deps.namedConstDeps consts).toIO { options := default, fileName := "", fileMap := default } {env} {env})
  pure map

def checkConstants (env : Lean.Environment) (consts : Lean.NameSet) (addDeclFn : Declaration → M Unit) (initConsts : Array Name := #[]) (printErr := false) (opts : TypeCheckerOpts := {}) (op : String := "typecheck") (printProgress := false) (interactive : Bool := false) (dbgOnly := false) : IO (Lean.NameSet × Environment) := do
  let mut onlyConstsToTrans : Lean.NameSet := default

  -- constants that should be skipped on account of already having been typechecked
  let mut skipConsts : Lean.NameSet := default
  -- constants that should throw an error if encountered on account of having previously failed to typecheck
  let mut errConsts : Lean.NameSet := default
  let mut modEnv := ← Lean.mkEmptyEnvironment

  let loop const modEnv skipConsts errConsts onlyConstsToTrans printProgress := do
    try
      let mut modEnv := modEnv
      let mut skipConsts := skipConsts
      if not $ skipConsts.contains const then
        let mut map ← getDepConstsEnv env #[const]
        let mapConsts := map.fold (init := default) fun acc const _ => acc.insert const

        let erredConsts : Lean.NameSet := mapConsts.intersectBy (fun _ _ _ => default) errConsts
        if erredConsts.size > 0 then
          throw $ IO.userError s!"Encountered untypecheckable constant dependencies: {erredConsts.toList}."

        let skippedConsts : Lean.NameSet := mapConsts.intersectBy (fun _ _ _ => default) skipConsts
        for skipConst in skippedConsts do
          map := map.erase skipConst

        let rp := do
          if dbgOnly then
            let (env, _) ← replay addDeclFn {newConstants := map.erase const, opts := {}} modEnv (printProgress := printProgress)
            pure env
          else
            let (env, _) ← replay addDeclFn {newConstants := map, opts := {}} modEnv (printProgress := printProgress)
            pure env

        if (not interactive) && (not (initConsts.contains const)) && consts.size == 1 && const != `temp then
          let outName := (const.toString) ++ s!".olean"
          let outDir := ((← IO.Process.getCurrentDir).join "saved")
          IO.FS.createDirAll outDir
          let outPath := outDir.join outName
          if ← System.FilePath.pathExists outPath then
            let (mod, _) ← readModuleData outPath
            let module := modEnv.mainModule
            let (_, s) ← importModulesCore mod.imports
              |>.run (s := { moduleNameSet := ({} : NameHashSet).insert module })
            modEnv ← finalizeImport s #[{module}] {} 0
            for const in mod.constants do
              modEnv := add modEnv const
            modEnv := modEnv.setMainModule module
          else
            modEnv ← rp
            writeModule modEnv.toMap₂ outPath
        else
          modEnv ← rp

        if dbgOnly then
          (modEnv, _) ← replay addDeclFn {newConstants := Std.HashMap.insert default const (map.get! const), opts} modEnv (printProgress := printProgress)
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
