# Equi-Join Grain Inference Revalidation

## Purpose

This revalidation tests the paper's Theorem 6.1 (equi-join grain inference) against a corrected formula across 100 SQL examples, verifying that:

1. The paper's formula produces a **correct but non-minimal** grain in all Case B (incomparable $J_k$-portions) examples.
2. The corrected formula produces a grain that is both a **unique identifier** and a **minimal unique identifier** in all 100 examples.

## Background

### The paper's formula (Theorem 6.1)

The paper defines the grain of the equi-join result using two cases based on the relationship between $G_1^{J_k} = G[R_1] \cap_{typ} J_k$ and $G_2^{J_k} = G[R_2] \cap_{typ} J_k$:

**Case A** (comparable: $G_1^{J_k} \subseteq_{typ} G_2^{J_k}$ or vice versa):

$$G[\text{Res}] \equiv_g (G[R_1] -_{typ} J_k) \times (G[R_2] -_{typ} J_k) \times (G[R_1] \cap_{typ} G[R_2] \cap_{typ} J_k)$$

**Case B** (incomparable: neither is a subtype of the other):

$$G[\text{Res}] \equiv_g (G[R_1] -_{typ} J_k) \times (G[R_2] -_{typ} J_k) \times ((G[R_1] \cup_{typ} G[R_2]) \cap_{typ} J_k)$$

### The theory gap

The paper's Case B proof establishes that omitting *both* uncommon $J_k$-portions simultaneously creates a circular dependency, then concludes that *both* must be included. This is a quantifier error: $\neg(\neg A \land \neg B)$ is read as $(A \land B)$ when the valid inference is $(A \lor B)$ -- at least one, not necessarily both.

### The corrected formula

$$G[\text{Res}] \equiv_g G[R_1] \cup_{typ} (G[R_2] -_{typ} J_k)$$

This single formula works for both Case A and Case B. It includes all of $G[R_1]$ (enabling the bootstrapping argument) plus only the grain columns of $R_2$ that lie outside the join key. See `THEORY_GAP_CASE_B.md` for the full analysis.

## Methodology

### Test structure

For each of the 100 examples:

1. **Create $R_1$ and $R_2$** with defined schemas, grain constraints (primary keys), and functional dependencies.
2. **Populate data** using `generate_series` with modular arithmetic for grain columns and randomized non-grain columns. $R_2$ is derived from $R_1$ through the join key to ensure dense join results.
3. **Compute the equi-join** $R_1 \bowtie_{J_k} R_2$ and store the result.
4. **Test uniqueness**: verify `COUNT(*) = COUNT(DISTINCT grain_columns)`.
5. **Test minimality**: for each grain column $c_i$, remove it and check whether the remaining columns are still unique. If they are, $c_i$ is removable and the grain is **not minimal**.

### Minimality test (PL/pgSQL)

For a candidate grain $(c_1, c_2, \ldots, c_n)$ over a result table:

```
minimal := TRUE
FOR i IN 1..n LOOP
    reduced_cols := (c_1, ..., c_{i-1}, c_{i+1}, ..., c_n)
    IF COUNT(DISTINCT reduced_cols) = total_rows THEN
        minimal := FALSE           -- c_i is removable
    END IF
END LOOP
```

A grain that passes uniqueness but fails minimality contains redundant columns -- it is a correct but non-minimal unique identifier.

### Example categories

| Category | Case | Count | Description |
|----------|------|-------|-------------|
| Main Theorem | B | 9 | $R_1(a,b,c,e)$, $G_1 = \{a,c\}$; $R_2(a,b,c,d)$, $G_2 = \{a,b\}$; $J_k = \{a,b,c\}$ |
| Incomparable Grains | B | 9 | $R_1(a,b,c,v_1)$, $G_1 = \{a,c\}$; $R_2(a,b,d,v_2)$, $G_2 = \{b,d\}$; $J_k = \{a,b\}$ |
| Natural Join | B | 9 | $R_1(a,b,c)$, $G_1 = \{a,b\}$; $R_2(b,c,d)$, $G_2 = \{c,d\}$; $J_k = \{b,c\}$ |
| Main Theorem | A | 13 | $R_1(a,b,v_1)$, $G_1 = \{a\}$; $R_2(a,b,v_2)$, $G_2 = \{a,b\}$; $J_k = \{a,b\}$ |
| Equal Grains | A | 20 | $G_1 = G_2$, grain size 1--4, join key size 1--4 |
| Ordered Grains | A | 25 | $G_1 \subseteq_{typ} G_2$ or $G_2 \subseteq_{typ} G_1$, 10 normal + 15 reversed |
| Incomparable Grains | A | 7 | $G_1 \not\subseteq_{typ} G_2$ but $G_1^{J_k} = G_2^{J_k}$ (comparable $J_k$-portions) |
| Natural Join | A | 8 | $G_1^{J_k} \subseteq_{typ} G_2^{J_k}$ |

Each category is tested with multiple data distributions (varying grain column cardinalities) to eliminate distribution-specific artifacts.

## Results

### Summary

| | Paper formula (Thm 6.1) | Corrected formula |
|---|---|---|
| **Uniqueness** | **100/100** | **100/100** |
| **Minimality** | **73/100** | **100/100** |

### By case type

| Case | Examples | Paper unique | Paper minimal | Corrected unique | Corrected minimal |
|------|----------|--------------|---------------|------------------|-------------------|
| A | 73 | 73/73 | 73/73 | 73/73 | 73/73 |
| B | 27 | 27/27 | **0/27** | 27/27 | 27/27 |

### Key observations

1. **Both formulas always produce unique identifiers** (100/100 uniqueness). The paper's formula is never *wrong* -- it always identifies result rows uniquely.

2. **The paper's formula fails minimality on every Case B example** (0/27). In each case, it includes $J_k$-grain columns that are recoverable through the bootstrapping argument.

3. **The corrected formula passes both uniqueness and minimality on all 100 examples** (100/100). It produces the tightest possible grain.

4. **Case A is unaffected.** Both formulas produce identical grains for all 73 Case A examples, and all pass both tests.

### Case B detail: removable columns in the paper's grain

| Examples | Paper grain | Removable columns | Corrected grain |
|----------|-------------|-------------------|-----------------|
| 1--9 (Main Theorem) | $(a, b, c)$ | $b$ and/or $c$ | $(a, c)$ |
| 10--18 (Incomparable) | $(a, b, c, d)$ | $a$ and $b$ | $(a, c, d)$ |
| 19--27 (Natural Join) | $(a, b, c, d)$ | $b$ and $c$ | $(a, b, d)$ |

In every Case B example, the paper's formula includes columns from $G_2^{J_k}$ that are redundant -- they can be recovered through the join condition once $G[R_1]$ is fully known.

### Concrete example (Example 1)

$$R_1 = \{a, b, c, e\} \quad G[R_1] = \{a, c\} \quad \text{FDs: } \{a,c\} \to \{b,e\}$$
$$R_2 = \{a, b, c, d\} \quad G[R_2] = \{a, b\} \quad \text{FDs: } \{a,b\} \to \{c,d\}$$
$$J_k = \{a, b, c\}$$

- $G_1^{J_k} = \{a, c\}$, $G_2^{J_k} = \{a, b\}$ -- incomparable (Case B).
- **Paper's grain:** $(a, b, c)$ -- all of $J_k$. **Unique but not minimal**: removing $b$ still leaves $(a, c) = G[R_1]$, which determines $r_1$, hence $r_1.b$, hence $r_2$ via join.
- **Corrected grain:** $(a, c) = G[R_1] \cup_{typ} (G[R_2] -_{typ} J_k) = \{a,c\} \cup_{typ} \emptyset$. **Unique and minimal**: removing $a$ or $c$ produces duplicates.

## Reproducing the results

### Prerequisites

- PostgreSQL (tested on 14+)
- Python 3.8+

### Running

```bash
# Generate the SQL (optional -- revalidation.sql is already provided)
python3 generate_revalidation.py > revalidation.sql

# Run against a local PostgreSQL database
psql -d postgres -f revalidation.sql 2>&1 | tee output.txt

# Check the summary
grep -A 20 'Total examples:' output.txt
```

The SQL uses `SELECT setseed(0.42)` for reproducible random values. Results are stored in `revalidation.test_results` and can be queried after execution:

```sql
-- Summary by case type
SELECT case_type,
       COUNT(*) AS examples,
       COUNT(*) FILTER (WHERE paper_minimal) AS paper_min_pass,
       COUNT(*) FILTER (WHERE corrected_minimal) AS corrected_min_pass
FROM revalidation.test_results
WHERE result_rows > 0
GROUP BY case_type;

-- Case B details
SELECT example_id, description, paper_grain, paper_removable, corrected_grain
FROM revalidation.test_results
WHERE case_type = 'B'
ORDER BY example_id;
```

## Files

| File | Description |
|------|-------------|
| `generate_revalidation.py` | Python generator for the SQL test suite (813 lines) |
| `revalidation.sql` | Generated SQL: schema, data, tests for 100 examples (12,797 lines) |
| `output.txt` | Full PostgreSQL output from the validation run |
| `REVALIDATION_RESULTS.md` | This document |
