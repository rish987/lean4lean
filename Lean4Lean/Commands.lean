import Lean
import Lean4Lean.Replay

open Lean Elab Command Term Meta

-- TODO existing function for this?
partial def Lean.Name.isCStage : Name → Bool
| .str p s   => s.startsWith "_cstage" || p.isCStage
| .num p _   => p.isCStage
| .anonymous => false

namespace Deps
  structure Context where
    env        : Environment

  structure State where
    map : HashMap Name ConstantInfo := {}
  abbrev DepsM := ReaderT Context <| StateRefT State IO

  @[inline] def DepsM.run (x : DepsM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
    x ctx |>.run s

  @[inline] def DepsM.toIO (x : DepsM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

  partial def namedConstDeps (name : Name) : DepsM Unit := do
    match ((← get).map.find? name) with
    | .none =>
      let some const := (← read).env.find? name | throw $ IO.userError s!"could not find constant \"{name}\" for translation, verify that it exists in the Lean input"
      modify fun s => { s with map := s.map.insert name const }
      let deps := const.getUsedConstantsAsSet
      for dep in deps do
        if !dep.isImplementationDetail && !dep.isCStage then
          namedConstDeps dep
    | .some _ => pure default
end Deps

def checkConstants (env : Lean.Environment) (consts : Lean.NameSet) (printErr := false) : IO Lean.NameSet := do
  let mut onlyConstsToTrans : Lean.NameSet := default

  -- constants that should be skipped on account of already having been typechecked
  let mut skipConsts : Lean.NameSet := default
  -- constants that should throw an error if encountered on account of having previously failed to typecheck
  let mut errConsts : Lean.NameSet := default
  let mut modEnv := ← Lean.mkEmptyEnvironment
  for const in consts do
    try
      if not $ skipConsts.contains const then
        let mut (_, {map := map, ..}) ← ((Deps.namedConstDeps const).toIO { options := default, fileName := "", fileMap := default } {env} {env})
        let mapConsts := map.fold (init := default) fun acc const _ => acc.insert const

        let erredConsts : Lean.NameSet := mapConsts.intersectBy (fun _ _ _ => default) errConsts
        if erredConsts.size > 0 then
          throw $ IO.userError s!"Encountered untypecheckable constant dependencies: {erredConsts.toList}."

        let skippedConsts : Lean.NameSet := mapConsts.intersectBy (fun _ _ _ => default) skipConsts
        for skipConst in skippedConsts do
          map := map.erase skipConst

        modEnv ← Lean4Lean.replay {newConstants := map} modEnv 
        skipConsts := skipConsts.union mapConsts -- TC success, so want to skip in future runs (already in environment)
      onlyConstsToTrans := onlyConstsToTrans.insert const
    catch
    | e =>
      if printErr then
        dbg_trace s!"Error typechecking constant `{const}`: {e.toString}"
      errConsts := errConsts.insert const
  pure onlyConstsToTrans

elab "#check_l4l " i:ident : command => do
  let env ← getEnv
  discard $ checkConstants (printErr := true) env (.insert default i.getId)
  -- match macroRes with
  -- | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  -- | none =>
  --   let kind := c.raw.getKind
  --   let elabs := commandElabAttribute.getEntries (←getEnv) kind
  --   match elabs with
  --   | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
  --   | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"
