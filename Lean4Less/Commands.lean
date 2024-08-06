import Lean
import Lean4Less.Replay
import Lean4Lean.Util
import Lean4Lean.Commands

open Lean
open Lean4Lean

def ppConst (env : Environment) (n : Name) : IO Unit := do
  let options := default
  let options := KVMap.set options `pp.proofs true
  let options := KVMap.set options `pp.explicit true
  let options := KVMap.set options `pp.funBinderTypes true
  let some info := env.find? n | unreachable!
  IO.print s!"{info.name}: {← (PrettyPrinter.ppExprLegacy env default default options info.type)}"

  match info.value? with
  | .some v => IO.println s!"\n{← (PrettyPrinter.ppExprLegacy env default default options v)}"
  | _ => IO.println ""

/--
The set of all constants used to patch terms, in linearised order based on
dependencies in the patched versions of their types/values.
-/
def patchConsts : List Name := [
`cast,
`HEq,
`HEq.symm,
`HEq.refl,
`Eq,
`Eq.refl,
`L4L.forallHEq,
`L4L.prfIrrelHEq,
`L4L.appHEq,
`L4L.appHEq',
`L4L.appHEqBinNatFn,
`L4L.lambdaHEq,
`L4L.appArgHEq,
]

def transL4L (n : Name) : Lean.Elab.Command.CommandElabM Environment := do
  let mut env := (← getEnv)
  let (_, env') ← checkConstants (printErr := true) env (.insert default n) @Lean4Less.addDecl (initConsts := patchConsts)
  env := env'
  ppConst env n
  pure env

elab "#trans_l4l " i:ident : command => do
  _ ← transL4L i.getId

elab "#check_l4l " i:ident : command => do
  let env ← transL4L i.getId
  _ ← checkConstants (printErr := true) env (.insert default i.getId) @Lean4Lean.addDecl
  -- match macroRes with
  -- | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  -- | none =>
  --   let kind := c.raw.getKind
  --   let elabs := commandElabAttribute.getEntries (←getEnv) kind
  --   match elabs with
  --   | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
  --   | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"
