import Lake
open Lake DSL

package lean4less

require std from git "https://github.com/leanprover/std4" @ "v4.7.0-rc2"

require lean4lean from "/home/rish/lean4lean/"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "8b1b1ac817cc2f5589a8efca18c59c828d3ca560"

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
