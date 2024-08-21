import Lake
open Lake DSL

package lean4less

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

require lean4lean from "/home/rvaishna/projects/lean4lean/" -- "lean2dk" branch

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "main"

@[default_target]
lean_lib patch { globs := #[Glob.submodules `patch] }

@[default_target]
lean_lib tests { roots := #[`Tests] }

@[default_target]
lean_lib Lean4Less

@[default_target]
lean_exe lean4less where
  root := `Main
  supportInterpreter := true
