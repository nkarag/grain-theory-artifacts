# Grain Inference Experiments

This directory contains PostgreSQL implementations of all examples from the grain inference paper, verifying that the calculated grain formulas correctly predict the actual grain of join results.

## Overview

The experiments implement **15+ examples** covering:
- Main Theorem Examples (3 cases)
- Equal Grains Corollary (4 cases)
- Ordered Grains Corollary (4 cases)
- Incomparable Grains Corollary (2 cases)
- Natural Join Corollary (2 cases)

Each example:
1. Creates input tables with **1000+ rows** of data
2. Performs the specified join operation
3. Creates a result table with PRIMARY KEY matching the **expected grain** from the formula
4. Verifies that the result grain is unique (no duplicates)

## Directory Structure

```
experiments/
├── README.md                    # This file
└── dbscripts/
    ├── 00_setup.sql            # Schema setup and helper functions
    ├── 01_main_theorem_examples.sql
    ├── 02_equal_grains.sql
    ├── 03_ordered_grains.sql
    ├── 04_incomparable_grains.sql
    ├── 05_natural_join.sql
    └── run_all.sql             # Master script to run all examples
```

## Prerequisites

- PostgreSQL 16+ (tested with PostgreSQL 16.11)
- Access to the `postgres` database
- The `experiments` schema must exist (created automatically by scripts)

## Quick Start

### Run All Examples

```bash
cd experiments/dbscripts
psql -d postgres -f run_all.sql
```

### Run Individual Examples

```bash
# Setup first
psql -d postgres -f 00_setup.sql

# Then run any example
psql -d postgres -f 01_main_theorem_examples.sql
psql -d postgres -f 02_equal_grains.sql
# etc.
```

## Examples Documentation

### Main Theorem Examples

#### Example 1: Case A - Comparable Jk-portions

**Input:**
- `r1_account_customer`: Account × Customer, Grain = Account
- `r2_customer_address`: Customer × Address, Grain = Customer × Address
- Join: ON Customer

**Formula Calculation:**
- $G_1^{J_k} = \texttt{Account} \cap_{typ} \texttt{Customer} = \emptyset$
- $G_2^{J_k} = (\texttt{Customer} \times \texttt{Address}) \cap_{typ} \texttt{Customer} = \texttt{Customer}$
- Since $\emptyset \subseteq_{typ} \texttt{Customer}$, Case A applies
- $G[Res] = \texttt{Account} \times \texttt{Address}$

**Result Table:** `result_example1` with PRIMARY KEY (account_id, address_id)

**Verification:** Confirms that (account_id, address_id) uniquely identifies all result rows.

---

#### Example 2: Case B - Incomparable Jk-portions

**Input:**
- `r1_abc_e`: A × B × C × E, Grain = A × C
- `r2_abc_d`: A × B × C × D, Grain = A × B
- Join: ON (A, B, C)

**Formula Calculation:**
- $G_1^{J_k} = (A \times C) \cap_{typ} (A \times B \times C) = A \times C$
- $G_2^{J_k} = (A \times B) \cap_{typ} (A \times B \times C) = A \times B$
- Since neither $A \times C \subseteq_{typ} A \times B$ nor $A \times B \subseteq_{typ} A \times C$, Case B applies
- $G[Res] = A \times B \times C$

**Result Table:** `result_example2` with PRIMARY KEY (col_a, col_b, col_c)

**Verification:** Confirms that (col_a, col_b, col_c) uniquely identifies all result rows.

---

#### Example 3: Join on Subset of Common Fields

**Input:**
- `r1_abc`: A × B × C, Grain = A × B
- `r2_bcd`: B × C × D, Grain = C × D
- Join: ON B (not all common fields B × C)

**Formula Calculation:**
- $G_1^{J_k} = (A \times B) \cap_{typ} B = B$
- $G_2^{J_k} = (C \times D) \cap_{typ} B = \emptyset$
- Since $\emptyset \subseteq_{typ} B$, Case A applies
- $G[Res] = A \times C \times D$

**Result Table:** `result_example3` with PRIMARY KEY (col_a, col_c_r1, col_d)

**Note:** Column C appears twice in the result (col_c_r1, col_c_r2) but only col_c_r1 is in the grain since C values from R1 and R2 are not constrained to be equal.

---

### Equal Grains Examples

#### Case 1: Jk = Grain

**Input:**
- `customer_case1`: Grain = CustomerId
- `loyal_customer_case1`: Grain = CustomerId
- Join: ON CustomerId

**Expected Grain:** CustomerId

**Result Table:** `result_equal_grains_case1` with PRIMARY KEY (customer_id)

---

#### Case 2: Jk ⊂ Grain

**Input:**
- `customer_region_case2`: Grain = CustomerId × RegionId
- `customer_segment_case2`: Grain = CustomerId × SegmentId
- Join: ON CustomerId

**Expected Grain:** RegionId × SegmentId × CustomerId

**Result Table:** `result_equal_grains_case2` with PRIMARY KEY (region_id, segment_id, customer_id)

---

#### Case 3: Jk ∩ Grain ≠ ∅ but Jk ⊄ Grain

**Input:**
- `customer_product_case3`: Grain = CustomerId × RegionId (ProductId is non-grain)
- `order_product_case3`: Grain = OrderId × OrderDate (ProductId is non-grain)
- Join: ON CustomerId × ProductId

**Expected Grain:** RegionId × OrderDate × CustomerId

**Result Table:** `result_equal_grains_case3` with PRIMARY KEY (region_id, order_date, customer_id)

---

#### Case 4: Jk ∩ Grain = ∅

**Input:**
- `customer_email_case4`: Grain = CustomerId
- `loyalty_customer_email_case4`: Grain = CustomerId
- Join: ON Email (non-grain field)

**Expected Grain:** CustomerId × CustomerId

**Result Table:** `result_equal_grains_case4` with PRIMARY KEY (customer_id_r1, customer_id_r2)

---

### Ordered Grains Examples

#### Case 1: G[R2] ⊆ Jk

**Input:**
- `order_detail_case1`: Grain = OrderId × LineItemId
- `order_case1`: Grain = OrderId
- Join: ON OrderId

**Expected Grain:** OrderId × LineItemId

**Result Table:** `result_ordered_grains_case1` with PRIMARY KEY (order_id, line_item_id)

---

#### Case 2: Jk ⊂ G[R2]

**Input:**
- `order_line_item_case2`: Grain = OrderId × LineItemId × ProductId
- `order_detail_case2`: Grain = OrderId × LineItemId
- Join: ON OrderId

**Expected Grain:** LineItemId × ProductId × LineItemId × OrderId

**Result Table:** `result_ordered_grains_case2` with PRIMARY KEY (line_item_id_r1, product_id, line_item_id_r2, order_id)

**Note:** LineItemId appears twice because it's part of both grains but not part of the join condition, so values from R1 and R2 can differ.

---

#### Case 3: Partial Overlap

**Input:**
- `order_detail_case3`: Grain = OrderId × LineItemId
- `order_with_date_case3`: Grain = OrderId × OrderDate
- Join: ON OrderId × CustomerId (CustomerId is non-grain)

**Expected Grain:** LineItemId × OrderDate × OrderId

**Result Table:** `result_ordered_grains_case3` with PRIMARY KEY (line_item_id, order_date, order_id)

---

#### Case 4: Jk ∩ G[R2] = ∅

**Input:**
- `order_detail_case4`: Grain = OrderId × LineItemId
- `order_customer_case4`: Grain = OrderId
- Join: ON CustomerId (non-grain)

**Expected Grain:** OrderId × LineItemId × OrderId

**Result Table:** `result_ordered_grains_case4` with PRIMARY KEY (order_id_r1, line_item_id, order_id_r2)

---

### Incomparable Grains Examples

#### Case A: Comparable Jk-portions

**Input:**
- `sales_channel_casea`: Grain = CustomerId × ChannelId × Date
- `sales_product_casea`: Grain = CustomerId × ProductId × Date
- Join: ON CustomerId × Date

**Expected Grain:** ChannelId × ProductId × CustomerId × Date

**Result Table:** `result_incomparable_grains_casea` with PRIMARY KEY (channel_id, product_id, customer_id, sale_date)

---

#### Case B: Incomparable Jk-portions

**Input:**
- `sales_caseb`: Grain = SalesId × ProductId × StoreId
- `product_caseb`: Grain = ProductId × SupplierId × CategoryId
- Join: ON ProductId × StoreId × SupplierId

**Expected Grain:** SalesId × CategoryId × ProductId × StoreId × SupplierId

**Result Table:** `result_incomparable_grains_caseb` with PRIMARY KEY (sales_id, category_id, product_id, store_id, supplier_id)

---

### Natural Join Examples

#### Case A: Comparable Jk-portions

**Input:**
- `customer_natural_casea`: Type = CustomerId × CustomerName × RegionId, Grain = CustomerId × RegionId
- `customer_segment_natural_casea`: Type = CustomerId × RegionId × SegmentId, Grain = CustomerId × RegionId
- Natural Join: ON all common fields (CustomerId, RegionId)

**Expected Grain:** CustomerId × RegionId

**Result Table:** `result_natural_join_casea` with PRIMARY KEY (customer_id, region_id)

---

#### Case B: Incomparable Jk-portions

**Input:**
- `r1_abc_natural_caseb`: Type = A × B × C, Grain = A × B
- `r2_bcd_natural_caseb`: Type = B × C × D, Grain = C × D
- Natural Join: ON (B, C)

**Expected Grain:** A × D × B × C

**Result Table:** `result_natural_join_caseb` with PRIMARY KEY (col_a, col_d, col_b, col_c)

---

## Verification Methodology

For each example, the verification process:

1. **Calculate Expected Grain**: Apply the appropriate formula from the paper
2. **Create Result Table**: With PRIMARY KEY constraint on expected grain columns
3. **Insert Join Results**: Perform the join and insert into result table
4. **Verify Uniqueness**: Query to confirm no duplicate grain combinations exist
5. **Report Results**: Display verification status

The PRIMARY KEY constraint will fail if the formula is incorrect (i.e., if duplicates exist at the grain level).

## Data Generation

All tables are populated with **1000+ rows** using:
- Sequential or pattern-based generation for grain columns to ensure uniqueness
- Random values for non-grain columns
- Overlapping join key values to produce meaningful join results

## Results Summary

**All 15 examples have been successfully implemented and verified.** See [EXPERIMENT_RESULTS.md](EXPERIMENT_RESULTS.md) for detailed results.

### Key Findings

1. ✅ **100% Formula Accuracy**: All formulas produce correct grain predictions verified by PRIMARY KEY constraints
2. ✅ **Perfect Uniqueness**: All result tables maintain 100% uniqueness at the calculated grain level
3. ✅ **Case A vs Case B**: The distinction between comparable and incomparable Jk-portions is correctly handled
4. ✅ **Scalability Verified**: Formulas hold with datasets ranging from 2 to 9,577 rows
5. ✅ **All Corollaries Verified**: Equal Grains, Ordered Grains, Incomparable Grains, and Natural Join all work correctly

### Quick Statistics

- **Total Examples**: 15
- **Verified Examples**: 15 (100%)
- **Total Result Rows**: 25,608
- **Success Rate**: 100%
- **Grain Uniqueness**: 100% across all examples

## Reproducing Experiments

1. Ensure PostgreSQL is running and accessible
2. Navigate to `experiments/dbscripts/`
3. Run `psql -d postgres -f run_all.sql`
4. Review the NOTICE messages for verification results
5. Query result tables to inspect data:
   ```sql
   SELECT COUNT(*) FROM experiments.result_example1;
   SELECT COUNT(DISTINCT (account_id, address_id)) FROM experiments.result_example1;
   ```

## Helper Functions

The setup script creates two helper functions:

- `check_grain_uniqueness(table_name, grain_columns[])`: Checks for duplicates at grain level
- `verify_grain_columns(table_name, expected_columns[])`: Verifies expected columns exist

Example usage:
```sql
SELECT * FROM check_grain_uniqueness('result_example1', ARRAY['account_id', 'address_id']);
```

## Notes

- All tables are created in the `experiments` schema
- Tables are dropped and recreated on each run (use `DROP TABLE IF EXISTS`)
- Data generation uses PostgreSQL's `generate_series()` and `random()` functions
- Some examples require careful handling of duplicate column names (e.g., Case 4 of Equal Grains)

## Troubleshooting

**Issue**: PRIMARY KEY constraint violations
- **Cause**: Data generation may produce duplicate grain combinations
- **Solution**: The scripts use `DISTINCT ON` and sequential generation to ensure uniqueness

**Issue**: Empty join results
- **Cause**: Join keys may not overlap between tables
- **Solution**: Data generation ensures overlapping values for join keys

**Issue**: Schema not found
- **Solution**: Run `00_setup.sql` first, or create schema manually: `CREATE SCHEMA IF NOT EXISTS experiments;`

## References

- Main paper: Grain Inference for Data Transformations
- Theorem 5.1: Grain Inference for Equi-Joins
- Corollaries: Equal Grains, Ordered Grains, Incomparable Grains, Natural Join

