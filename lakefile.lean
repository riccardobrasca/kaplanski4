import Lake
open Lake DSL

package «kaplanski4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Kaplanski4» {
  -- add any library configuration options here
}
