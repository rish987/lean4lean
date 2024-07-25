import Lean
import Lean4Lean.Replay
import Lean4Lean.Util

open Lean

namespace Lean4Lean

def checkConstants (env : Lean.Environment) (consts : Lean.NameSet) (addDeclFn : Declaration → M Unit) (printErr := false) : IO (Lean.NameSet × Environment) := do
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

        modEnv ← replay addDeclFn {newConstants := map} modEnv
        skipConsts := skipConsts.union mapConsts -- TC success, so want to skip in future runs (already in environment)
      onlyConstsToTrans := onlyConstsToTrans.insert const
    catch
    | e =>
      if printErr then
        dbg_trace s!"Error typechecking constant `{const}`: {e.toString}"
      errConsts := errConsts.insert const
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
