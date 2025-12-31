# Formal Verification of Pipeline Examples

This directory contains formal verifications of pipelines from the illustrative example in the paper, demonstrating that grain theory enables rigorous, machine-checkable correctness proofs for data pipelines.

## Files

- **`Pipeline3.lean`**: Formal verification that **Pipeline 3 is CORRECT** (aggregate first, then join)
- **`Pipeline1.lean`**: Formal verification that **Pipeline 1 is INCORRECT** (direct join - grain mismatch detected)
- **`Pipeline2.lean`**: Formal verification that **Pipeline 2 is INCORRECT** (direct join then aggregate - metrics duplication violation detected)

## Overview

These formalizations use **Lean 4** to prove correctness (Pipeline 3) and detect incorrectness (Pipeline 1) at the **type level**, requiring no data processing or query execution. Both verifications follow the complete **5-step methodology** from Section 6.1 of the paper.

## Pipeline Specifications

### Pipeline 3: Aggregate first, then join (CORRECT ✓)

### Input Types
- `SalesChannel`: `CustomerId × ChannelId × Date`
  - Grain: `G[SalesChannel] = CustomerId × ChannelId × Date`
- `SalesProduct`: `CustomerId × ProductId × Date`
  - Grain: `G[SalesProduct] = CustomerId × ProductId × Date`

### Target Type
- `SalesReport`: `CustomerId × Date`
  - Grain: `G[SalesReport] = CustomerId × Date`

### Pipeline Steps

1. **Aggregation Step 1**: `R1' = γ_{CustomerId, Date}(SalesChannel)`
   - Result type: `SalesChannelAgg = CustomerId × Date`
   - Grain: `G[SalesChannelAgg] = CustomerId × Date` ✓

2. **Aggregation Step 2**: `R2' = γ_{CustomerId, Date}(SalesProduct)`
   - Result type: `SalesProductAgg = CustomerId × Date`
   - Grain: `G[SalesProductAgg] = CustomerId × Date` ✓

3. **Join Step**: `R1' ⋈_{J_k} R2'` where `J_k = CustomerId × Date`
   - Result type: `JoinResult = CustomerId × Date`
   - By **Equal Grains Corollary Case 1**: Since `J_k = G[R1'] = G[R2']`, we have `G[JoinResult] = J_k = CustomerId × Date` ✓

4. **Verification**: `G[JoinResult] = CustomerId × Date = G[SalesReport]` ✓

### Pipeline 1: Direct join (INCORRECT ✗)

**Pipeline 1**: Direct join `R1 ⋈_{J_k} R2` where `J_k = CustomerId × Date`

**Result**: 
- `G[Pipeline1JoinResult] = ChannelId × ProductId × CustomerId × Date`
- `G[SalesReport] = CustomerId × Date`
- **Grain mismatch detected**: `G[Res] ≠ G[Target]` ✗

See `Pipeline1.lean` for the complete verification following all 5 steps of the methodology.

### Pipeline 2: Direct join, then aggregate (INCORRECT ✗)

**Pipeline 2**: 
1. Join `R1 ⋈_{J_k} R2` where `J_k = CustomerId × Date` → `Res_join`
2. Group by `CustomerId, Date` with `SUM` aggregations → `Res_final`

**Result**:
- `G[Res_join] = ChannelId × ProductId × CustomerId × Date`
- `G[Res_final] = CustomerId × Date = G[Target]` ✓ (final grain matches!)
- **BUT**: `G[Res_join] <_g G[SalesChannel]` and `G[Res_join] <_g G[SalesProduct]`
- **Metrics duplication violation detected**: Join result is finer than both inputs → double-counting ✗

**The subtle point**: Even though the final grain matches the target, the intermediate join creates a fan trap that causes metrics duplication. This violation is detected by comparing intermediate grains, demonstrating the importance of checking all pipeline steps, not just the final result.

See `Pipeline2.lean` for the complete verification following all 5 steps of the methodology.

## Verification Methodology

The verification follows the **complete 5-step methodology** from Section 6.1 of the paper:

### Step 1: Identify Grains
**Goal**: Determine `G[R]` for all types `R` in the pipeline at the type level.

**Theorems**:
- `step1_identify_grain_SalesChannel`: `SalesChannel ≡_g SalesChannel` (G[SalesChannel] = CustomerId × ChannelId × Date)
- `step1_identify_grain_SalesProduct`: `SalesProduct ≡_g SalesProduct` (G[SalesProduct] = CustomerId × ProductId × Date)
- `step1_identify_grain_SalesReport`: `SalesReport ≡_g SalesReport` (G[SalesReport] = CustomerId × Date)

### Step 2: Determine Grain Relations
**Goal**: Establish `≡_g`, `≤_g`, or `⟨⟩_g` relationships between types.

**Theorems**:
- `step2a_source_to_source_incomparable`: `SalesChannel ⟨⟩_g SalesProduct` (incomparable grains)
- `step2b1_SalesChannel_le_SalesReport`: `SalesChannel ≤_g SalesReport` (source finer than target)
- `step2b2_SalesProduct_le_SalesReport`: `SalesProduct ≤_g SalesReport` (source finer than target)

**Conclusion**: Sources are at finer grains than target, so aggregation is required.

### Step 3: Apply Grain Inference
**Goal**: Use the appropriate grain inference rule from Table 1 to compute expected result grain for each transformation.

**Step 3.1: Grouping Operations** (Table 1 - Unary Operations)
- `step1a_grouping_grain_inference`: `SalesChannelAgg ≡_g JoinKey`
  - **Formula Applied**: `G[γ_{G_cols}(R)] = G_cols`
  - **Result**: `G[SalesChannelAgg] = CustomerId × Date`
  
- `step1b_grouping_grain_inference`: `SalesProductAgg ≡_g JoinKey`
  - **Formula Applied**: `G[γ_{G_cols}(R)] = G_cols`
  - **Result**: `G[SalesProductAgg] = CustomerId × Date`

- `step1_equal_grains_after_aggregation`: `SalesChannelAgg ≡_g SalesProductAgg`
  - **Result**: Both aggregated types have equal grain

**Step 3.2: Equi-Join Operation** (Equal Grains Corollary Case 1)
- `step2_equal_grains_join_case1`: `SalesChannelAgg ≡_g SalesProductAgg → JoinResult ≡_g JoinKey`
  - **Formula Applied**: Equal Grains Case 1: `J_k = G[R1] = G[R2] → G[Res] = J_k`
  - **Result**: `G[JoinResult] = J_k = CustomerId × Date`

### Step 4: Verify Grain Consistency
**Goal**: Compare expected grain with actual result grain to verify correctness.

**Theorem**:
- `step4_result_equals_target_grain`: `JoinResult ≡_g SalesReport`
  - **Verification**: `G[JoinResult] = CustomerId × Date = G[SalesReport]` ✓

### Step 5: Detect Violations
**Goal**: Identify discrepancies indicating potential bugs or incorrect transformations.

**Result**: No violations detected
- ✓ Grain consistency verified: `G[JoinResult] = G[SalesReport]`
- ✓ No fan trap: `G[JoinResult] = G[SalesChannelAgg] = G[SalesProductAgg]` (not finer than inputs)
- ✓ Pipeline passes grain analysis

### Complete Pipeline Verification
```lean
theorem pipeline3_complete_verification :
  JoinResult ≡_g SalesReport
```
**Meaning**: The complete pipeline produces the correct grain, verified by following all 5 steps of the methodology.

## How to Verify

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/) installed (via `elan`)
- [Cursor Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) installed

### Setup (First Time)

1. **Install dependencies**: The project uses Mathlib 4, which is automatically downloaded when you build:
   ```bash
   cd formal_verification
   lake build
   ```
   This will download Mathlib and all its dependencies (this may take a few minutes the first time).

2. **Verify setup**:
   ```bash
   elan show  # Should show: leanprover/lean4:v4.26.0
   lean --version  # Should show: Lean (version 4.26.0, ...)
   ```

### Using the Formalization

**In Cursor/VS Code:**
1. Open `Pipeline3.lean` in Cursor
2. The Lean extension should automatically detect the project and start the language server
3. You'll see:
   - ✓ Green checkmarks for verified theorems
   - Red squiggles for errors
   - Hover tooltips showing types and documentation

**From Command Line:**
```bash
cd formal_verification
lake build  # Builds the project and checks all proofs
```

### Using Lean Language Server
Open `Pipeline3.lean` in VS Code with the Lean extension. The proofs will be checked automatically, and you can see:
- ✓ Green checkmarks for verified theorems
- Error messages if proofs are incomplete

## Significance

This formalization demonstrates that:

1. **Type-Level Verification**: Grain correctness can be verified purely at the type level, without executing queries or processing data.

2. **Machine-Checkable Proofs**: The proofs are verified by Lean's type checker, providing mathematical certainty.

3. **Complete 5-Step Methodology**: All three verifications follow all 5 steps of the methodology from Section 6.1:
   - **Step 1**: Identify grains for all types (with formal theorems)
   - **Step 2**: Determine grain relations (`≡_g`, `≤_g`, `⟨⟩_g`) between all types (with formal proofs)
   - **Step 3**: Apply grain inference formulas from Table 1 at each transformation step
   - **Step 4**: Verify grain consistency by comparing result grain to target grain
   - **Step 5**: Detect violations
   
   This demonstrates that the complete methodology can be systematically applied and formally verified, calculating the grain at each transformation step and verifying it against expectations. **Pipeline 2** demonstrates the importance of checking intermediate grains, not just the final result.

4. **Foundation for Tooling**: This demonstrates that grain theory provides a foundation for building formal verification tools for data pipelines.

## Extending the Formalization

To extend this to other pipelines:

1. **Define the types** (input, intermediate, output)
2. **Define grain functions** for each type
3. **Apply grain inference rules** for each transformation
4. **Prove grain equivalence** between result and target

The structure can be reused for any pipeline that follows the grain inference methodology.

## Connection to the Paper

This formalization directly implements the **complete 5-step verification methodology** described in Section 6.1 ("Type-Level Verification Methodology"):

1. **Step 1 (Identify grains)**: Formally prove `G[R]` for all types `R` in the pipeline
   - `SalesChannel ≡_g SalesChannel` (G[SalesChannel] = CustomerId × ChannelId × Date)
   - `SalesProduct ≡_g SalesProduct` (G[SalesProduct] = CustomerId × ProductId × Date)
   - `SalesReport ≡_g SalesReport` (G[SalesReport] = CustomerId × Date)

2. **Step 2 (Determine grain relations)**: Formally establish `≡_g`, `≤_g`, or `⟨⟩_g` relationships
   - `SalesChannel ⟨⟩_g SalesProduct` (incomparable grains)
   - `SalesChannel ≤_g SalesReport` (source finer than target)
   - `SalesProduct ≤_g SalesReport` (source finer than target)
   - **Conclusion**: Aggregation is required (sources are finer than target)

3. **Step 3 (Apply grain inference)**: Systematically apply formulas from **Table 1**:
   - Grouping formula: `G[γ_{G_cols}(R)] = G_cols` (applied to both aggregations)
   - Equal Grains Case 1: `J_k = G[R1] = G[R2] → G[Res] = J_k` (applied to join)

4. **Step 4 (Verify grain consistency)**: Compare expected grain with actual result grain
   - `JoinResult ≡_g SalesReport` (grain matches target) ✓

5. **Step 5 (Detect violations)**: Identify discrepancies indicating potential bugs
   - No violations detected: grain consistency verified, no fan trap, pipeline passes ✓

The verification demonstrates that:
- **All 5 steps** can be formally implemented and verified
- **Table 1 formulas** are systematically applied at each transformation step
- **Grain calculation** happens step-by-step with verification at each step
- **Grain relations** are formally established before applying inference rules
- **The complete methodology** is mathematically rigorous and machine-checkable

## Future Work

Potential extensions:
- Formalize the full equi-join theorem (Case A and Case B)
- Verify other pipeline alternatives (Pipeline 1, Pipeline 2)
- Add proofs for fan trap detection
- Integrate with SQL query verification tools
- Build automated grain inference for SQL queries

## References

- Main paper: "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"
- Lean 4: https://leanprover.github.io/lean4/doc/
- Mathlib: https://leanprover-community.github.io/mathlib4_docs/

