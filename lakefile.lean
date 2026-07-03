import Lake
open Lake DSL

package «lean-2d-yang-mills» where
  -- Satellite repo for the THE-ERIKSSON-PROGRAMME 2D Yang-Mills sandbox.

lean_lib Lean2dYangMills where
  -- Public import root: `import Lean2dYangMills`.

lean_lib Interfaces where
  -- Parent repository contract: `import Interfaces`.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "07642720480157414db592fa85b626dafb71355b"
