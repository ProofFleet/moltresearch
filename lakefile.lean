import Lake
open Lake DSL

package «moltresearch» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

-- Root entrypoints live at repo root:
--   MoltResearch.lean / Solutions.lean / Tasks.lean / Conjectures.lean

@[default_target]
lean_lib MoltResearch

lean_lib Solutions

-- Backlog (not built by default target). Keep as lean_libs so editors work.
lean_lib Tasks
lean_lib Conjectures
