import Lake
open Lake DSL

package "grain_encoding" where
  -- Use shared packages directory at parent level
  packagesDir := "/Users/nikos/current_work/mypapers/VLDB-2026/formal_verification/.lake/packages"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

-- Declare libraries
lean_lib GrainDefinitions
lean_lib GrainedData
