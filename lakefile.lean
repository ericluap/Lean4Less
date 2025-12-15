import Lake
open Lake DSL

package lean4less where
  testDriver := "tests"

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.27.0-rc1"
require "leanprover-community" / "Qq" @ git "master"

-- require lean4lean from "/home/rvaishna/projects/lean4lean/"

require lean4lean from git "https://github.com/ericluap/lean4lean" @ "lean4less"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.27.0-rc1"

@[default_target]
lean_lib patch { globs := #[Glob.submodules `patch] }

@[default_target]
lean_lib Lean4Less

@[default_target]
lean_exe lean4less where
  root := `Main
  supportInterpreter := true

lean_lib tests where
  globs := #[.submodules `tests]
