/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Lean.Environment
import Lean4Lean.Replay

open Lean
open Lean4Lean

/--
Run as e.g. `lake exe lean4lean` to check everything on the Lean search path,
or `lake exe lean4lean Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "--"
  let fresh : Bool := "--fresh" ∈ flags
  let verbose : Bool := "--verbose" ∈ flags
  let compare : Bool := "--compare" ∈ flags
  match args with
    | [mod, only] => match mod.toName with
      | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
      | m =>
        replayFromFresh addDecl m (verbose := verbose) (compare := compare) (onlyConsts? := [only.toName])
    | [mod] => match mod.toName with
      | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
      | m =>
        if fresh then
          replayFromFresh addDecl m (verbose := verbose) (compare := compare)
        else
          replayFromImports addDecl m (verbose := verbose) (compare := compare)
    | _ => do
      if fresh then
        throw <| IO.userError "--fresh flag is only valid when specifying a single module"
      let sp ← searchPathRef.get
      let mut tasks := #[]
      for path in (← SearchPath.findAllWithExt sp "olean") do
        if let some m ← searchModuleNameOfFileName path sp then
          tasks := tasks.push (m, ← IO.asTask (replayFromImports addDecl m verbose compare))

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
