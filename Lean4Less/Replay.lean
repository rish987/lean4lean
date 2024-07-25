import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Less.Environment
import Lean4Lean.Replay

open Lean

namespace Lean4Less

open Lean4Less.Environment
open Lean4Lean

/-- Add a declaration, possibly throwing a `KernelException`. -/
def addDecl (d : Declaration) : M Unit := do
  if (← read).verbose then
    println! "adding {d.name}"
  let t1 ← IO.monoMsNow
  match addDecl' (← get).env d with
  | .ok env =>
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      if (← read).compare then
        let t3 ← match (← get).env.addDecl d with
        | .ok _ => IO.monoMsNow
        | .error ex => throwKernelException ex
        if (t2 - t1) > 2 * (t3 - t2) then
          println!
            "{(← get).env.mainModule}:{d.name}: lean took {t3 - t2}, lean4lean took {t2 - t1}"
        else
          println! "{(← get).env.mainModule}:{d.name}: lean4lean took {t2 - t1}"
      else
        println! "{(← get).env.mainModule}:{d.name}: lean4lean took {t2 - t1}"
    modify fun s => { s with env := env }
  | .error ex =>
    throwKernelException ex

end Lean4Less
