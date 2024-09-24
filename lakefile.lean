import Lake
open Lake DSL

package lean4lean

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true
