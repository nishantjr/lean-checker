import Lake
open Lake DSL

package «lean-checker» where
  -- add package configuration options here

lean_lib «LeanChecker» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-checker» where
  root := `Main

require mathlib from git
   "https://github.com/leanprover-community/mathlib4.git"
