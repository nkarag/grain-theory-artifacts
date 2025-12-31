# Grain Verification: How It Works

This document explains how the automatic grain verification works in `GrainInference.lean`.

## Overview

The verification process has three main steps:

1. **Compute** the result grain using the grain inference formulas (set operations)
2. **Compare** the computed grain with the target grain (set equality)
3. **Return** `true` if they match, `false` otherwise (mismatch detected)

## Step 1: Represent Grain as a Set of Field Names

Grain is represented as a list of field name strings:

```lean
abbrev Field := String
abbrev Grain := List Field

-- Example grains
def G_SalesChannel : Grain := ["customerId", "channelId", "date"]
def G_SalesProduct : Grain := ["customerId", "productId", "date"]
def G_JoinKey : Grain := ["customerId", "date"]
def G_Target : Grain := ["customerId", "date"]  -- Target grain for the pipeline
```

## Step 2: Implement Type-Level Set Operations

The grain inference formulas use set operations from the paper (Section 3, Foundations):

```lean
-- Union (∪_{typ}): All fields from both types
def grain_union (g1 g2 : Grain) : Grain :=
  dedup (g1 ++ g2)

-- Intersection (∩_{typ}): Only fields common to both types
def grain_intersection (g1 g2 : Grain) : Grain :=
  g1.filter (fun f => g2.contains f)

-- Difference (-_{typ}): Fields in first but not in second
def grain_difference (g1 g2 : Grain) : Grain :=
  g1.filter (fun f => !g2.contains f)
```

## Step 3: Apply the Grain Inference Formulas

The formulas from Section 5 (Grain Inference) are applied automatically:

```lean
-- Case A formula (Theorem 5.1):
-- G[Res] = (G[R1] - J_k) ∪ (G[R2] - J_k) ∪ (G[R1] ∩ G[R2] ∩ J_k)
def equi_join_grain_case_a (G_R1 G_R2 J_k : Grain) : Grain :=
  let part1 := G_R1 -_g J_k                    -- (G[R1] - J_k)
  let part2 := G_R2 -_g J_k                    -- (G[R2] - J_k)
  let part3 := (G_R1 ∩_g G_R2) ∩_g J_k         -- (G[R1] ∩ G[R2] ∩ J_k)
  part1 ∪_g part2 ∪_g part3                    -- Combine all parts

-- Group-by formula: G[Res] = G_cols
def group_by_grain (G_cols : Grain) : Grain :=
  G_cols
```

Example computation for Pipeline 1:
```
Input:
  G[SalesChannel] = ["customerId", "channelId", "date"]
  G[SalesProduct] = ["customerId", "productId", "date"]
  J_k = ["customerId", "date"]

Computation:
  Part 1: G[SalesChannel] - J_k = ["channelId"]
  Part 2: G[SalesProduct] - J_k = ["productId"]
  Part 3: (G[SalesChannel] ∩ G[SalesProduct]) ∩ J_k = ["customerId", "date"]
  
Result: ["channelId", "productId", "customerId", "date"]
```

## Step 4: Check Grain Equality (Set Equality)

The `grain_eq` function checks if two grains are equal as sets (order doesn't matter):

```lean
def grain_eq (g1 g2 : Grain) : Bool :=
  g1.all (fun f => g2.contains f) && g2.all (fun f => g1.contains f)
```

This checks:
- `g1.all (fun f => g2.contains f)` → Every field in g1 is in g2 (g1 ⊆ g2)
- `g2.all (fun f => g1.contains f)` → Every field in g2 is in g1 (g2 ⊆ g1)
- Both together → g1 = g2 (as sets)

## Step 5: Verify Pipeline Correctness

The compatibility check compares computed grain with target grain:

```lean
def grain_compatible (computed target : Grain) : Bool :=
  grain_eq computed target

def pipeline1_verification : Bool :=
  grain_compatible computed_pipeline1_grain G_Target

#eval pipeline1_verification  -- Output: false (MISMATCH!)
```

## Verification Examples

### Pipeline 1 (INCORRECT)

```
Computed grain: ["channelId", "productId", "customerId", "date"]
Target grain:   ["customerId", "date"]

grain_eq check:
  - Is "channelId" in target? NO → FAIL!
  
Result: false (grain mismatch detected!)
```

### Pipeline 3 (CORRECT)

```
Computed grain: ["customerId", "date"]
Target grain:   ["customerId", "date"]

grain_eq check:
  - Is "customerId" in target? YES ✓
  - Is "date" in target? YES ✓
  - Is "customerId" in computed? YES ✓
  - Is "date" in computed? YES ✓
  
Result: true (grains match!)
```

## Summary

The verification process is:

1. **Input**: Source grains (from input types) and target grain (expected output)
2. **Process**: Apply grain inference formulas using set operations
3. **Output**: Boolean indicating whether computed grain matches target grain

This is **pure set comparison** of field name lists - the same logic you would implement in Python or any other language. The power comes from:
- Formulas being applied automatically
- Verification happening at compile time (via `#eval`)
- No data processing required

## Build Output

When you run `lake build`, you see the computation:

```
Part 1 (G[R1] - J_k): [channelId]
Part 2 (G[R2] - J_k): [productId]
Part 3 (G[R1] ∩ G[R2] ∩ J_k): [customerId, date]
Result (Part1 ∪ Part2 ∪ Part3): [channelId, productId, customerId, date]
Target grain: [customerId, date]
Pipeline 1 correct? false
```

This demonstrates that grain verification happens **automatically** by applying formulas and comparing sets.

