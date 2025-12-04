import Lake
open Lake DSL

package lean4lean

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.26.0-rc2"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.26.0-rc2"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true
