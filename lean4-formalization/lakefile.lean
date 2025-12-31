import Lake
open Lake DSL

package "pipeline3_verification" where
  -- Use shared packages directory at parent level
  packagesDir := "/Users/nikos/current_work/mypapers/VLDB-2026/formal_verification/.lake/packages"

-- Add Mathlib as a dependency
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

-- Declare libraries
lean_lib GrainDefinitions
lean_lib GrainInference
lean_lib GrainInferenceExample
lean_lib Pipeline1
lean_lib Pipeline2
lean_lib Pipeline3
lean_lib TypeCheckerErrorA
lean_lib TypeCheckerErrorB
lean_lib TypeCheckerErrorC
lean_lib TypeCheckerErrorD
lean_lib TypeCheckerErrorE
