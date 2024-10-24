/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Cli
import Lean.Util.FoldConsts
import Lean4Less.Environment
import Lean4Less.Fixtures.Tests -- FIXME should use separate fixtures dir
import Lean4Less.Replay
import Lean4Less.Commands

open Lean
open Lean4Lean
open Cli

open private add from Lean.Environment

def outDir : System.FilePath := System.mkFilePath [".", "out"]

structure ForEachModuleState where
  moduleNameSet : NameHashSet := {}
  env : Environment
  count := 0

-- def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx) (modIdx : Nat) (cname : Name) : IO α := do
--   let modName := s.moduleNames[modIdx]!
--   let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
--   throw <| IO.userError s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

abbrev ForEachModuleM := StateRefT ForEachModuleState IO

@[inline] nonrec def ForEachModuleM.run (env : Environment) (x : ForEachModuleM α) (s : ForEachModuleState := {env}) : IO (α × ForEachModuleState) :=
  x.run s

partial def forEachModule' (f : Name → ModuleData → ForEachModuleM Unit) (imports : Array Import) : ForEachModuleM Unit := do
  for i in imports do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      continue
    modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
    let mFile ← findOLean i.module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
    let (mod, _) ← readModuleData mFile
    forEachModule' f mod.imports
    modify fun s => { s with count := s.count + 1}
    f i.module mod

def mkModuleData (imports : Array Import) (env : Environment) : IO ModuleData := do
  let pExts ← persistentEnvExtensionsRef.get
  let entries := pExts.map fun pExt =>
    let state := pExt.getState env
    (pExt.name, pExt.exportEntriesFn state)
  let constNames := env.constants.foldStage2 (fun names name _ => names.push name) #[]
  let constants  := env.constants.foldStage2 (fun cs _ c => cs.push c) #[]
  return {
    extraConstNames := #[],
    imports, constNames, constants, entries
  }

def patchPreludeModName := `Init.PatchPrelude

/--
Run as e.g. `lake exe lean4lean` to check everything on the Lean search path,
or `lake exe lean4lean Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
-/
unsafe def runTransCmd (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mod : Name := p.positionalArg! "input" |>.value.toName
  let onlyConsts? := p.flag? "only" |>.map fun onlys => 
    onlys.as! (Array String)
  let cachedPath? := p.flag? "cached" |>.map fun sp => 
    System.FilePath.mk $ sp.as! String
  match mod with
    | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
    | m =>
      let (lemmEnv, success) ← Lean.Elab.runFrontend (include_str "patch" / "PatchTheoremsAx.lean") default default `Patch
      if not success then
        throw $ IO.userError $ "elab of patching defs failed"
      if let some onlyConsts := onlyConsts? then
        Lean.withImportModules #[{module := mod}] {} 0 fun env => do
          let mut env := env
          for (_, c) in lemmEnv.constants do
            env := add env c
          _ ← Lean4Less.checkL4L (onlyConsts.map (·.toName)) env (printProgress := true)
      else
        let outDir := ((← IO.Process.getCurrentDir).join "out")
        if (← outDir.pathExists) && not cachedPath?.isSome then
          IO.FS.removeDirAll outDir
        IO.FS.createDirAll outDir
        let mkMod imports env n := do
          let mod ← mkModuleData imports env
          let modPath := (modToFilePath outDir n "olean")
          let some modParent := modPath.parent | panic! s!"could not find parent dir of module {n}"
          IO.FS.createDirAll modParent
          saveModuleData modPath n mod

        IO.println s!">>init module"
        let patchConsts ← getDepConstsEnv lemmEnv Lean4Less.patchConsts
        let env ← replay Lean4Less.addDecl {newConstants := patchConsts, opts := {}} (← mkEmptyEnvironment) (printProgress := true) (op := "patch")
        mkMod #[] env patchPreludeModName

        let (_, s) ← ForEachModuleM.run env do
          forEachModule' (imports := #[m]) fun _ _ => do
            pure ()
        let numMods := s.moduleNameSet.size

        let (_, s) ← ForEachModuleM.run env do
          forEachModule' (imports := #[m]) fun dn d => do
            let skip ←
              if let some cachedPath := cachedPath? then
                if let some mfile ← SearchPath.findWithExt [cachedPath] "olean" dn then
                  if ← mfile.pathExists then
                    let (mod, _) ← readModuleData mfile
                    let mut env := (← get).env
                    for c in mod.constants do
                      env := add env c
                    modify fun s => {s with env}
                    pure true
                  else
                    pure false
                else
                  pure false
              else
                pure false
            unless not skip do return

            let newConstants ← d.constNames.zip d.constants |>.foldlM (init := default) fun acc (n, ci) => do
              if not ((← get).env.contains n) then
                pure $ acc.insert n ci
              else
                pure $ acc
            IO.println s!">>{dn} module [{(← get).count}/{numMods}]"
            let env ← replay Lean4Less.addDecl {newConstants := newConstants, opts := {}} (← get).env (printProgress := true) (op := "patch")
            let imports := if dn == `Init.Prelude then
                #[{module := `Init.PatchPrelude}] ++ d.imports
              else
                d.imports

            mkMod imports env dn
            modify fun s => {s with env}
        let env := s.env
        replayFromEnv Lean4Lean.addDecl m env.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})
        -- forEachModule' (imports := #[m]) (init := env) fun e dn d => do
        --   -- let newConstants := d.constNames.zip d.constants |>.foldl (init := default) fun acc (n, ci) => acc.insert n ci
        --
        --   IO.println s!"{dn} module"
        --   pure e
          -- replay Lean4Less.addDecl {newConstants := newConstants, opts := {}} e (printProgress := true)
        -- replayFromInit' Lean4Less.addDecl m lemmEnv (op := "patch") (initConsts? := Lean4Less.patchConsts) fun env' =>
        --   replayFromEnv Lean4Lean.addDecl m env'.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})
  return 0

unsafe def transCmd : Cmd := `[Cli|
  transCmd VIA runTransCmd; ["0.0.1"]
  "Translate from Lean to Lean-."

  FLAGS:
    -- p, print;               "Print translation of specified constants to standard output (relevant only with '-o ...')."
    -- w, write;               "Also write translation of specified constants (with dependencies) to file (relevant only with '-p')."
    o, only : Array String; "Only translate the specified constants and their dependencies."
    a, appopt : Bool; "Optimize application case"
    c, cached : String; "Use cached library translation files from specified directory."

  ARGS:
    input : String;         "Input .lean file."

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "rish987"
]

unsafe def main (args : List String) : IO UInt32 := do
  transCmd.validate args
