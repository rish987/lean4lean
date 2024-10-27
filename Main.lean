/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Cli
import Lean.Util.FoldConsts
import Lean4Lean.Environment
import Lean4Lean.Replay
import Lean4Lean.Commands

open Lean
open Cli
open Lean4Lean

/--
Run as e.g. `lake exe lean4lean` to check everything on the Lean search path,
or `lake exe lean4lean Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
-/
unsafe def runRunCmd (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let onlyConsts? := p.flag? "only" |>.map fun onlys => 
    onlys.as! (Array String)
  let fresh : Bool := p.hasFlag "fresh"
  let verbose : Bool := p.hasFlag "verbose"
  let compare : Bool := p.hasFlag "compare"
  let searchPath? := p.flag? "search-path" |>.map fun sp => 
    sp.as! String
  match searchPath? with
  | .some sp =>
    let path := System.FilePath.mk sp
    searchPathRef.set [path]
  | _ => initSearchPath (← findSysroot)
  let proofIrrelevance := not $ p.hasFlag "no-proof-irrel"
  let kLikeReduction := not $ p.hasFlag "no-klike-red"
  let opts := {proofIrrelevance, kLikeReduction}
  match p.positionalArg? "input" with
    | .some mod => match mod.value.toName with
      | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
      | m =>
        if let some onlyConsts := onlyConsts? then
          Lean.withImportModules #[{module := m}] {} 0 fun env => do
            let map := onlyConsts.foldl (init := default) fun acc n => .insert acc n.toName
            let _ ← checkConstants (printErr := true) env map Lean4Lean.addDecl (op := "typecheck") (printProgress := true)
        if fresh then
          replayFromFresh addDecl m (verbose := verbose) (compare := compare) (opts := opts)
        else
          replayFromImports addDecl m (verbose := verbose) (compare := compare) (opts := opts)
    | _ => do
      if fresh then
        throw <| IO.userError "--fresh flag is only valid when specifying a single module"
      let sp ← searchPathRef.get
      let mut tasks := #[]
      for path in (← SearchPath.findAllWithExt sp "olean") do
        if let some m ← searchModuleNameOfFileName path sp then
          tasks := tasks.push (m, ← IO.asTask (replayFromImports addDecl m verbose compare (opts := opts)))

      let mut numDone := 0
      let mut finished : NameSet := default
      while true do
        let mut allDone := true
        let mut numDone' := 0
        for (m, t) in tasks do
          if not (finished.find? m |>.isSome) then
            match ← IO.getTaskState t with
            | .finished =>
              if let .error e := t.get then
                IO.eprintln s!"lean4lean found a problem in {m}: {e}"
              numDone' := numDone' + 1
              finished := finished.insert m
            | _ => allDone := false
        if numDone' != numDone then
          numDone := numDone'
          IO.println s!"{numDone}/{tasks.size} tasks completed"
        if allDone then break
        IO.sleep 1000
  return 0

unsafe def runCmd : Cmd := `[Cli|
  runCmd VIA runRunCmd; ["0.0.1"]
  "Run Lean4Lean"

  FLAGS:
    o, only : Array String;         "Only translate the specified constants and their dependencies."
    f, fresh;                       "Typecheck imported modules"
    v, verbose;                     "Verbose mode"
    c, compare;                     "Compare Lean4Lean and kernel runtimes"
    s, "search-path" : String;      "Set search path directory"
    npi, "no-proof-irrel";          "Disable proof irrelevance"
    nklr, "no-klike-red";           "Disable k-like reduction"
    -- o, only : Array String; "Only translate the specified constants and their dependencies."

  ARGS:
    input : String;         "Input Lean module name."
]

unsafe def main (args : List String) : IO UInt32 := do
  runCmd.validate args
