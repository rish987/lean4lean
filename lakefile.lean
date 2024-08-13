import Lake
open Lake DSL

package lean4lean

require batteries from git "https://github.com/leanprover-community/batteries" @ "ad26fe1ebccc9d5b7ca9111d5daf9b4488374415"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true
