import Lake
open Lake DSL

package lean4less

require std from git "https://github.com/leanprover/std4" @ "v4.7.0-rc2"

@[default_target]
lean_lib Lean4Less

@[default_target]
lean_exe lean4less where
  root := `Main
  supportInterpreter := true
