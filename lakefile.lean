import Lake
open Lake DSL

package lean4lean

require batteries from git "https://github.com/leanprover-community/batteries" @ "0f3e143dffdc3a591662f3401ce1d7a3405227c0"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true

@[default_target]
lean_lib Lean4Lean.Theory where
  globs := #[.andSubmodules `Lean4Lean.Theory]

@[default_target]
lean_lib Lean4Lean.Verify where
  globs := #[.andSubmodules `Lean4Lean.Verify]
