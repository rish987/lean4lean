import Lean
import Lean4Less.Replay
import Lean4Lean.Util
import Lean4Lean.Commands

open Lean
open Lean4Lean

namespace Lean4Less

def ppConst (env : Environment) (n : Name) : IO Unit := do
  let options := default
  let options := KVMap.set options `pp.proofs true
  let options := KVMap.set options `pp.explicit true
  let options := KVMap.set options `pp.funBinderTypes true
  let some info := env.find? n | unreachable!
  try
    IO.print s!"patched {info.name}: {← (PrettyPrinter.ppExprLegacy env default default options info.type)}"

    match info.value? with
    | .some v =>
      if v.approxDepth < 100 then
        IO.println s!"\n{← (PrettyPrinter.ppExprLegacy env default default options v)}"
      else
        IO.println s!"\n [[[expression too large]]]"
    | _ => IO.println ""
  catch
  | _ =>
    IO.print s!"patched {info.name}: {info.type}"
    match info.value? with
    | .some v =>
      if v.approxDepth < 100 then
        IO.println s!"\n{v}"
      else
        IO.println s!"\n [[[expression too large]]]"
    | _ => IO.println ""

/--
The set of all constants used to patch terms, in linearised order based on
dependencies in the patched versions of their types/values.
-/
def patchConsts : Array Name := #[
`L4L.eq_of_heq,
`cast,
`L4L.HEqRefl,
`L4L.castHEq,
`HEq,
`HEq.symm,
`HEq.refl,
`HEq.trans,
`Eq,
`Eq.refl,

`L4L.prfIrrel,
`L4L.prfIrrelHEq,
`L4L.prfIrrelHEqPQ,

`L4L.forallHEqUV,
`L4L.forallHEqUV',
`L4L.forallHEqAB,
`L4L.forallHEqABUV,
`L4L.forallHEqABUV',
`L4L.appArgHEq,
`L4L.appArgHEq',
`L4L.appFunHEq,
`L4L.appFunHEq',
`L4L.appHEq,
`L4L.appHEq',
`L4L.appHEqUV,
`L4L.appHEqUV',
`L4L.appFunHEqUV,
`L4L.appFunHEqUV',
`L4L.appHEqAB,
`L4L.appHEqABUV,
`L4L.appHEqABUV',
`L4L.lambdaHEq,
`L4L.lambdaHEq',
`L4L.lambdaHEqUV,
`L4L.lambdaHEqUV',
`L4L.lambdaHEqABUV,
`L4L.lambdaHEqABUV',

`L4L.castOrigHEq,
`L4L.castOrigHEqSymm,

`L4L.appHEqBinNatFn,
`sorryAx --FIXME
]

def transL4L' (ns : Array Name) (env : Environment) (pp := false) (printProgress := false) (interactive := false) (opts : TypeCheckerOpts := {}) : IO Environment := do
  let map := ns.foldl (init := default) fun acc n => .insert acc n
  let (_, newEnv) ← checkConstants (printErr := true) env map (@Lean4Less.addDecl (opts := opts)) (initConsts := patchConsts) (op := "patch") (printProgress := printProgress) (interactive := interactive)
  for n in ns do
    if pp then
      ppConst newEnv n
  pure newEnv

def transL4L (n : Array Name) (env? : Option Environment := none) : Lean.Elab.Command.CommandElabM Environment := do
  let env ← env?.getDM getEnv
  transL4L' n env

def checkL4L (ns : Array Name) (env : Environment) (printOutput := true) (printProgress := false) (interactive := false) (opts : TypeCheckerOpts := {}) : IO Environment := do
  let env ← transL4L' ns env (pp := printOutput) (printProgress := printProgress) (interactive := interactive) (opts := opts)
  let nSet := ns.foldl (init := default) fun acc n => acc.insert n
  -- unsafe replayFromEnv Lean4Lean.addDecl env.mainModule env.toMap₁ (op := "typecheck") (opts := {proofIrrelevance := false, kLikeReduction := false})

  let (_, checkEnv) ← checkConstants (printErr := true) env nSet Lean4Lean.addDecl (initConsts := patchConsts) (opts := {proofIrrelevance := not opts.proofIrrelevance, kLikeReduction := not opts.kLikeReduction}) (interactive := interactive)

  -- let env' ← transL4L' ns env
  -- for n in ns do
  --   let .some c  := env.find? n | unreachable!
  --   let .some c' := env'.find? n | unreachable!
  --
  --   let diffTypes := c.toConstantVal.type != c'.toConstantVal.type
  --   let diffVals := c.value? != c'.value?
  --   if diffTypes || diffVals then
  --     throw $ IO.userError $ s!"failed round-trip test: \n--- LHS\n {← ppConst env n} \n--- RHS\n {← ppConst env' n}"
  pure checkEnv

elab "#trans_l4l " i:ident : command => do
  _ ← transL4L #[i.getId]

elab "#check_only " i:ident : command => do
  _ ← checkConstants (printErr := true) (← getEnv) (.insert default i.getId) (Lean4Lean.addDecl (verbose := true)) (opts := {}) (interactive := true)

elab "#check_off " i:ident : command => do
  _ ← checkConstants (printErr := true) (← getEnv) (.insert default i.getId) Lean4Lean.addDecl (opts := {proofIrrelevance := false, kLikeReduction := false}) (interactive := true)

elab "#check_l4l " i:ident : command => do
  _ ← checkL4L #[i.getId] (← getEnv) (interactive := true)

end Lean4Less
  -- match macroRes with
  -- | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  -- | none =>
  --   let kind := c.raw.getKind
  --   let elabs := commandElabAttribute.getEntries (←getEnv) kind
  --   match elabs with
  --   | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
  --   | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"
