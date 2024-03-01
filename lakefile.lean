import Lake
open Lake DSL

def moreLeanArgs := #[
  "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
]

def moreServerArgs := moreLeanArgs


package «lean-checker» where
  moreLeanArgs := moreLeanArgs
  moreServerArgs := moreServerArgs

lean_lib «LeanChecker» where
  moreLeanArgs := moreLeanArgs

@[default_target]
lean_exe «lean-checker» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
