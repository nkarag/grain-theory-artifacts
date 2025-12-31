# Grain as First-Class Type-Level Property: Implementation Patterns

This document presents elegant approaches for encoding grain semantics in various programming languages and data processing frameworks, enabling compile-time verification of grain correctness.

**Status**:
- ✅ **Complete**: Python/PySpark, dbt, SQL
- ⏳ **Pending**: Lean 4, Agda, Haskell (to be added after review)

---

## Table of Contents

1. [Python with PySpark](#1-python-with-pyspark)
2. [dbt (SQL + Jinja + YAML)](#2-dbt-sql--jinja--yaml)
3. [SQL with Extensions](#3-sql-with-extensions)
4. [Lean 4](#4-lean-4) *(Coming soon)*
5. [Agda](#5-agda) *(Coming soon)*
6. [Haskell](#6-haskell) *(Coming soon)*

---

## Core Concept

The grain defines the **level of detail (granularity)** at which each element represents information. By encoding grain as a first-class type-level property, we enable:

- **Compile-time verification**: Type checker catches grain mismatches before runtime
- **Zero computational cost**: No runtime overhead for grain checking
- **Semantic correctness**: Prevents using data with wrong granularity (entity vs versioned vs event semantics)

---

## 1. Python with PySpark

Python's gradual typing system (via `typing` module) combined with runtime validation provides practical grain-aware data processing.

### Approach A: Generic DataFrame with Grain Type Parameter

**Key Idea**: Use `Generic[G]` to create `GrainedDataFrame[G]` where `G` is the grain type. Type checkers (mypy, pyright) enforce grain compatibility.

```python
from typing import Generic, TypeVar, Protocol, runtime_checkable
from pyspark.sql import DataFrame as SparkDF
from dataclasses import dataclass
from abc import ABC, abstractmethod

# ============================================================================
# Grain Type Definitions
# ============================================================================

@runtime_checkable
class Grain(Protocol):
    """Protocol defining what a grain type must provide"""
    columns: tuple[str, ...]

@dataclass(frozen=True)
class EntityGrain:
    """Grain for entity semantics: one row per customer"""
    columns: tuple[str, ...] = ("customer_id",)

@dataclass(frozen=True)
class VersionedGrain:
    """Grain for versioned semantics: multiple time-stamped rows per customer"""
    columns: tuple[str, ...] = ("customer_id", "effective_from")

@dataclass(frozen=True)
class EventGrain:
    """Grain for event semantics: each creation/modification event"""
    columns: tuple[str, ...] = ("customer_id", "created_on", "event_type")

# ============================================================================
# Grained DataFrame
# ============================================================================

G = TypeVar('G', bound=Grain)

class GrainedDataFrame(Generic[G]):
    """
    DataFrame with compile-time grain semantics.

    The type parameter G encodes the grain, enabling type checker to catch
    grain mismatches at compile time (before any Spark job execution).
    """

    def __init__(self, df: SparkDF, grain: G):
        """
        Create a grained DataFrame.

        Args:
            df: Underlying Spark DataFrame
            grain: Grain specification (determines type parameter G)

        Raises:
            ValueError: If grain columns don't exist in DataFrame schema
        """
        self._df = df
        self._grain = grain
        # Runtime validation (defensive programming)
        self._validate_grain()

    def _validate_grain(self) -> None:
        """Verify grain columns exist in schema"""
        df_cols = set(self._df.columns)
        grain_cols = set(self._grain.columns)
        if not grain_cols.issubset(df_cols):
            missing = grain_cols - df_cols
            raise ValueError(
                f"Grain columns {missing} not found in DataFrame. "
                f"Available columns: {df_cols}"
            )

    @property
    def df(self) -> SparkDF:
        """Access underlying Spark DataFrame"""
        return self._df

    @property
    def grain(self) -> G:
        """Access grain specification"""
        return self._grain

    def __repr__(self) -> str:
        grain_name = self._grain.__class__.__name__
        num_rows = self._df.count()
        return f"GrainedDataFrame[{grain_name}]({num_rows} rows)"

# ============================================================================
# Grain-Aware Functions (Type-Checked)
# ============================================================================

def process_entity_customers(
    df: GrainedDataFrame[EntityGrain]
) -> GrainedDataFrame[EntityGrain]:
    """
    Process customers with entity grain semantics.

    Type signature enforces: input must have EntityGrain.
    Type checker (mypy/pyright) rejects VersionedGrain or EventGrain.
    """
    # Business logic here - knows grain is entity-level
    result = df.df.select("customer_id", "name").distinct()
    return GrainedDataFrame(result, EntityGrain())

def aggregate_versioned_to_entity(
    df: GrainedDataFrame[VersionedGrain]
) -> GrainedDataFrame[EntityGrain]:
    """
    Aggregate versioned data to entity grain.

    Type signature shows grain transformation:
    - Input: VersionedGrain (customer_id × effective_from)
    - Output: EntityGrain (customer_id)
    """
    # Group by customer_id, taking latest version
    from pyspark.sql import functions as F

    result = (df.df
              .groupBy("customer_id")
              .agg(F.max("effective_from").alias("latest_date"),
                   F.first("name").alias("name")))

    return GrainedDataFrame(result, EntityGrain())

def join_same_grain(
    left: GrainedDataFrame[G],
    right: GrainedDataFrame[G],
    on: list[str]
) -> GrainedDataFrame[G]:
    """
    Join two DataFrames with the SAME grain.

    Type signature enforces: both inputs must have identical grain type G.
    Type checker prevents joining EntityGrain with VersionedGrain.
    """
    result = left.df.join(right.df, on=on, how="inner")
    return GrainedDataFrame(result, left.grain)

# ============================================================================
# Usage Examples
# ============================================================================

# Create DataFrames with different grains
from pyspark.sql import SparkSession
spark = SparkSession.builder.getOrCreate()

# Entity grain: one row per customer
entity_data = spark.createDataFrame([
    (1, "Alice", "alice@example.com"),
    (2, "Bob", "bob@example.com")
], ["customer_id", "name", "email"])

entity_df = GrainedDataFrame(entity_data, EntityGrain())

# Versioned grain: multiple rows per customer
versioned_data = spark.createDataFrame([
    (1, "2024-01-01", "Alice", "alice@old.com"),
    (1, "2024-06-01", "Alice", "alice@new.com"),
    (2, "2024-01-01", "Bob", "bob@example.com")
], ["customer_id", "effective_from", "name", "email"])

versioned_df = GrainedDataFrame(versioned_data, VersionedGrain())

# ✓ Type checks - correct grain
result1 = process_entity_customers(entity_df)

# ✓ Type checks - explicit grain transformation
result2 = aggregate_versioned_to_entity(versioned_df)

# ✗ Type error caught by mypy/pyright:
# result3 = process_entity_customers(versioned_df)
# Error: Argument 1 has incompatible type "GrainedDataFrame[VersionedGrain]"
#        Expected type: "GrainedDataFrame[EntityGrain]"

# ✓ Type checks - same grain join
entity_df2 = GrainedDataFrame(entity_data, EntityGrain())
joined = join_same_grain(entity_df, entity_df2, on=["customer_id"])

# ✗ Type error caught by mypy/pyright:
# bad_join = join_same_grain(entity_df, versioned_df, on=["customer_id"])
# Error: Type variable "G" has incompatible values (EntityGrain, VersionedGrain)
```

**Benefits**:
- Type checker catches grain mismatches before Spark job submission
- Clear API: function signatures document grain requirements
- Runtime validation provides additional safety net
- Compatible with existing PySpark code (wraps Spark DataFrame)

**Limitations**:
- Requires Python 3.9+ for full typing support
- Type checking is optional (Python's gradual typing)
- Runtime validation has small overhead (but prevents expensive Spark jobs)

---

### Approach B: Type Class Pattern (Functional Style)

**Key Idea**: Use Protocol to define `HasGrain` interface, enabling automatic grain inference.

```python
from typing import Protocol, TypeVar, Generic, get_type_hints
from pyspark.sql import DataFrame as SparkDF

class HasGrain(Protocol):
    """Type class for types with grain"""
    @property
    def grain_columns(self) -> tuple[str, ...]: ...

class EntityCustomer:
    """Customer with entity grain semantics"""
    grain_columns = ("customer_id",)

    def __init__(self, customer_id: int, name: str, email: str):
        self.customer_id = customer_id
        self.name = name
        self.email = email

class VersionedCustomer:
    """Customer with versioned grain semantics"""
    grain_columns = ("customer_id", "effective_from")

    def __init__(self, customer_id: int, effective_from: str,
                 name: str, email: str):
        self.customer_id = customer_id
        self.effective_from = effective_from
        self.name = name
        self.email = email

T = TypeVar('T', bound=HasGrain)

class TypedDataFrame(Generic[T]):
    """DataFrame parameterized by row type with grain"""

    def __init__(self, df: SparkDF, row_type: type[T]):
        self._df = df
        self._row_type = row_type
        # Grain is automatically inferred from row_type
        self._grain = row_type.grain_columns

    @property
    def grain(self) -> tuple[str, ...]:
        return self._grain

    def process(self) -> SparkDF:
        """Process with grain-aware logic"""
        return self._df.groupBy(*self._grain).count()

# Usage
entity_df = TypedDataFrame(spark_df, EntityCustomer)
# Grain automatically inferred: ("customer_id",)

versioned_df = TypedDataFrame(spark_df, VersionedCustomer)
# Grain automatically inferred: ("customer_id", "effective_from")
```

**Benefits**:
- Grain automatically derived from data type
- Less annotation burden
- Type-safe via protocols

**Limitations**:
- Requires defining wrapper classes for each grain variant
- Less explicit than Approach A

---

### Approach C: Phantom Type Parameter (Simplest)

**Key Idea**: Grain as phantom type parameter - not stored, only for type checking.

```python
from typing import Generic, TypeVar

# Grain types (empty - just for type checking)
class EntityGrain: pass
class VersionedGrain: pass

G = TypeVar('G')

class DataFrame(Generic[G]):
    """DataFrame with phantom grain type parameter"""

    def __init__(self, df: SparkDF):
        self._df = df
        # G is phantom - not stored, only for type checking

# Usage
entity_df: DataFrame[EntityGrain] = DataFrame(spark_df)
versioned_df: DataFrame[VersionedGrain] = DataFrame(spark_df)

def process_entity(df: DataFrame[EntityGrain]) -> DataFrame[EntityGrain]:
    return df

# Type error:
# process_entity(versioned_df)  # Error: EntityGrain ≠ VersionedGrain
```

**Benefits**:
- Simplest implementation
- Zero runtime overhead
- Pure type-level enforcement

**Limitations**:
- No runtime validation
- Grain type must be manually specified
- Easy to misuse (assign wrong grain type)

---

## 2. dbt (SQL + Jinja + YAML)

dbt provides a declarative framework for data transformations. We can encode grain in model configurations and create compile-time validations.

### Approach: Grain as Model Config + Compile-Time Validation

**Key Idea**: Store grain metadata in `schema.yml`, create custom dbt tests/macros for compile-time validation.

#### Step 1: Define Grain in schema.yml

```yaml
# models/schema.yml
version: 2

models:
  # Entity grain: one row per customer
  - name: customers_entity
    description: Customer data at entity grain (one row per customer)
    config:
      grain:
        type: entity
        columns: [customer_id]
        semantics: entity
        description: "Each row represents a distinct customer entity"
    columns:
      - name: customer_id
        description: Unique customer identifier
        tests:
          - unique
          - not_null
      - name: name
        description: Customer name
      - name: email
        description: Customer email

  # Versioned grain: multiple rows per customer
  - name: customers_versioned
    description: Customer data at versioned grain (temporal versions)
    config:
      grain:
        type: versioned
        columns: [customer_id, effective_from]
        semantics: versioned
        description: "Each row represents a version of customer information"
    columns:
      - name: customer_id
        description: Customer identifier (not unique - multiple versions)
        tests:
          - not_null
      - name: effective_from
        description: Version effective date
        tests:
          - not_null
      - name: effective_to
        description: Version expiry date (NULL for current version)
      - name: name
      - name: email
    tests:
      # Grain uniqueness test
      - unique:
          column_name: "customer_id || '|' || effective_from"
          config:
            severity: error

  # Aggregated grain: customer × date
  - name: sales_report
    description: Daily sales aggregated by customer
    config:
      grain:
        type: aggregated
        columns: [customer_id, date]
        semantics: aggregated
        description: "Each row represents sales for a customer on a specific date"
    columns:
      - name: customer_id
        tests:
          - not_null
      - name: date
        tests:
          - not_null
      - name: total_amount
    tests:
      - unique:
          column_name: "customer_id || '|' || date"
```

#### Step 2: Custom dbt Test for Grain Compatibility

```sql
-- tests/generic/grain_compatible_join.sql
{% test grain_compatible_join(model, left_model, right_model, join_keys) %}
    {#
        Compile-time test: Verify grain compatibility for joins

        Args:
            model: The model performing the join
            left_model: Left table being joined
            right_model: Right table being joined
            join_keys: List of join key columns

        Raises:
            Compiler error if grains are incompatible
    #}

    {%- set left_grain = get_model_grain(left_model) -%}
    {%- set right_grain = get_model_grain(right_model) -%}

    {# Validate grain compatibility #}
    {% if not grains_compatible_for_join(left_grain, right_grain, join_keys) %}
        {{ exceptions.raise_compiler_error(
            "Grain mismatch in join:\n" ~
            "  Left table (" ~ left_model ~ "): grain = " ~ left_grain.columns | join(", ") ~ "\n" ~
            "  Right table (" ~ right_model ~ "): grain = " ~ right_grain.columns | join(", ") ~ "\n" ~
            "  Join keys: " ~ join_keys | join(", ") ~ "\n" ~
            "This join may produce incorrect results (fan trap or chasm trap)."
        ) }}
    {% endif %}

    -- If validation passes, return empty result (test passes)
    select 1 where false

{% endtest %}
```

#### Step 3: Helper Macros for Grain Operations

```sql
-- macros/grain_utils.sql

{% macro get_model_grain(model_name) %}
    {#
        Extract grain configuration from model metadata

        Returns: dict with keys: type, columns, semantics
    #}
    {%- set model = graph.nodes.values() | selectattr("name", "equalto", model_name) | first -%}

    {%- if model and model.config and model.config.grain -%}
        {{ return(model.config.grain) }}
    {%- else -%}
        {{ exceptions.raise_compiler_error(
            "Model '" ~ model_name ~ "' does not have grain metadata defined in schema.yml"
        ) }}
    {%- endif -%}
{% endmacro %}

{% macro grains_compatible_for_join(left_grain, right_grain, join_keys) %}
    {#
        Check if two grains are compatible for joining

        Compatible if:
        1. Grains are equal (same columns)
        2. Join keys equal both grains (natural join at same grain)
        3. One grain is subset of other AND subset grain = join keys

        Returns: boolean
    #}

    {%- set left_cols = left_grain.columns | sort -%}
    {%- set right_cols = right_grain.columns | sort -%}
    {%- set join_cols = join_keys | sort -%}

    {# Case 1: Equal grains #}
    {%- if left_cols == right_cols -%}
        {{ return(true) }}
    {%- endif -%}

    {# Case 2: Join keys match both grains (natural join) #}
    {%- if join_cols == left_cols and join_cols == right_cols -%}
        {{ return(true) }}
    {%- endif -%}

    {# Case 3: Check if one grain ordered by other #}
    {%- set left_is_subset = left_cols | reject("in", right_cols) | list | length == 0 -%}
    {%- set right_is_subset = right_cols | reject("in", left_cols) | list | length == 0 -%}

    {%- if left_is_subset and join_cols == left_cols -%}
        {{ return(true) }}
    {%- elif right_is_subset and join_cols == right_cols -%}
        {{ return(true) }}
    {%- endif -%}

    {# Grains incompatible #}
    {{ return(false) }}

{% endmacro %}

{% macro validate_grain_transformation(input_grain, output_grain, operation) %}
    {#
        Validate that a transformation correctly changes grain

        Args:
            input_grain: Grain before transformation
            output_grain: Expected grain after transformation
            operation: Type of operation (aggregation, join, etc.)
    #}

    {%- if operation == "aggregation" -%}
        {# Output grain must be coarser (subset of input grain) #}
        {%- set output_is_subset = output_grain.columns | reject("in", input_grain.columns) | list | length == 0 -%}
        {%- if not output_is_subset -%}
            {{ exceptions.raise_compiler_error(
                "Invalid aggregation: output grain contains columns not in input grain"
            ) }}
        {%- endif -%}
    {%- endif -%}

{% endmacro %}
```

#### Step 4: Usage in dbt Models

```sql
-- models/sales_report.sql
{{
    config(
        materialized='table',
        grain={
            'type': 'aggregated',
            'columns': ['customer_id', 'date'],
            'semantics': 'aggregated'
        }
    )
}}

-- Validate grain compatibility at compile time
{{ validate_grain_compatible_sources([
    'customers_entity',
    'sales_transactions'
]) }}

with sales_channel_agg as (
    -- Aggregate to customer × date grain
    select
        customer_id,
        date,
        sum(channel_revenue) as channel_revenue
    from {{ ref('sales_channel') }}
    group by customer_id, date
),

sales_product_agg as (
    -- Aggregate to customer × date grain
    select
        customer_id,
        date,
        sum(product_revenue) as product_revenue
    from {{ ref('sales_product') }}
    group by customer_id, date
)

-- Join at same grain (customer × date)
select
    coalesce(sc.customer_id, sp.customer_id) as customer_id,
    coalesce(sc.date, sp.date) as date,
    coalesce(sc.channel_revenue, 0) as channel_revenue,
    coalesce(sp.product_revenue, 0) as product_revenue,
    coalesce(sc.channel_revenue, 0) + coalesce(sp.product_revenue, 0) as total_revenue
from sales_channel_agg sc
full outer join sales_product_agg sp
    on sc.customer_id = sp.customer_id
    and sc.date = sp.date
```

```yaml
# models/sales_report.yml
models:
  - name: sales_report
    config:
      grain:
        type: aggregated
        columns: [customer_id, date]
    tests:
      # Test grain compatibility
      - grain_compatible_join:
          left_model: sales_channel_agg
          right_model: sales_product_agg
          join_keys: [customer_id, date]

      # Test grain uniqueness
      - unique:
          column_name: "customer_id || '|' || date"
```

**Benefits**:
- Compile-time errors via dbt macros (before query execution)
- Self-documenting: grain metadata in schema.yml
- Automated testing: custom tests enforce grain constraints
- Fits dbt's declarative philosophy

**Limitations**:
- Grain checking happens at dbt compile time, not in SQL itself
- Requires discipline to maintain grain metadata
- Custom macros add complexity

---

## 3. SQL with Extensions

Pure SQL lacks type-level features, but we can approximate grain-aware type checking through:
1. Comment annotations + external static analyzer
2. Hypothetical SQL extensions (for paper discussion)

### Approach A: Comment Annotations + Static Analysis

**Key Idea**: Use structured comments to annotate grain, build external static analyzer to check compatibility.

```sql
-- ============================================================================
-- Table Definitions with Grain Annotations
-- ============================================================================

-- Grain annotation format:
-- @grain: <grain_type>
-- @grain_columns: <column_list>
-- @semantics: <description>

CREATE TABLE customers (
    customer_id INT PRIMARY KEY,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(100) NOT NULL
)
-- @grain: entity
-- @grain_columns: customer_id
-- @semantics: Each row represents a distinct customer entity (one row per customer)
;

CREATE TABLE customers_versioned (
    customer_id INT NOT NULL,
    effective_from DATE NOT NULL,
    effective_to DATE,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(100) NOT NULL,
    PRIMARY KEY (customer_id, effective_from)
)
-- @grain: versioned
-- @grain_columns: customer_id, effective_from
-- @semantics: Each row represents a version of customer information over time
;

CREATE TABLE sales_channel (
    customer_id INT NOT NULL,
    channel_id INT NOT NULL,
    date DATE NOT NULL,
    revenue DECIMAL(10, 2) NOT NULL,
    PRIMARY KEY (customer_id, channel_id, date)
)
-- @grain: fact
-- @grain_columns: customer_id, channel_id, date
-- @semantics: Sales facts at channel × customer × date granularity
;

-- ============================================================================
-- Query with Grain Annotations
-- ============================================================================

-- Query annotation format:
-- @input_grain: <table_name>: <grain_columns>
-- @output_grain: <grain_columns>
-- @grain_transformation: <operation>

-- Example 1: Correct aggregation (grain coarsening)
-- @input_grain: sales_channel: customer_id, channel_id, date
-- @output_grain: customer_id, date
-- @grain_transformation: aggregation (group by customer_id, date)
SELECT
    customer_id,
    date,
    SUM(revenue) as total_revenue
FROM sales_channel
-- Static analyzer validates:
-- - Output grain (customer_id, date) is coarser than input grain ✓
-- - GROUP BY columns match output grain ✓
GROUP BY customer_id, date;

-- Example 2: Incorrect join (grain mismatch - caught by analyzer)
-- @input_grain: customers: customer_id
-- @input_grain: customers_versioned: customer_id, effective_from
-- @expects_output_grain: customer_id
-- @grain_transformation: join on customer_id
SELECT
    c.customer_id,
    c.name as current_name,
    cv.name as historical_name
FROM customers c
JOIN customers_versioned cv
    ON c.customer_id = cv.customer_id
-- Static analyzer ERROR:
-- Grain mismatch detected:
--   Left table (customers): grain = [customer_id]
--   Right table (customers_versioned): grain = [customer_id, effective_from]
--   Join keys: [customer_id]
-- Result grain would be [customer_id, effective_from] (finer than expected)
-- This creates a fan trap (one customer → many versions)
-- Recommendation: Aggregate customers_versioned first or add effective_from to join
;

-- Example 3: Correct join (same grain)
-- @input_grain: sales_channel_agg: customer_id, date
-- @input_grain: sales_product_agg: customer_id, date
-- @output_grain: customer_id, date
-- @grain_transformation: equi-join on customer_id, date
WITH sales_channel_agg AS (
    SELECT customer_id, date, SUM(revenue) as channel_revenue
    FROM sales_channel
    GROUP BY customer_id, date
    -- @grain: customer_id, date
),
sales_product_agg AS (
    SELECT customer_id, date, SUM(revenue) as product_revenue
    FROM sales_product
    GROUP BY customer_id, date
    -- @grain: customer_id, date
)
SELECT
    c.customer_id,
    c.date,
    c.channel_revenue,
    p.product_revenue
FROM sales_channel_agg c
FULL OUTER JOIN sales_product_agg p
    ON c.customer_id = p.customer_id
    AND c.date = p.date
-- Static analyzer validates:
-- - Both inputs have same grain [customer_id, date] ✓
-- - Join keys match grain ✓
-- - Output grain equals input grains ✓
;

-- ============================================================================
-- Static Analyzer Implementation (Pseudocode)
-- ============================================================================

/*
class SQLGrainAnalyzer:
    def analyze_query(sql: str) -> AnalysisResult:
        # 1. Parse SQL and extract grain annotations
        tables = extract_table_grains(sql)
        query_annotations = extract_query_annotations(sql)

        # 2. Infer result grain from transformations
        for operation in query_operations:
            if operation.type == "JOIN":
                result_grain = infer_join_grain(
                    left_grain=tables[operation.left].grain,
                    right_grain=tables[operation.right].grain,
                    join_keys=operation.join_keys
                )

                # Check against expected grain
                if query_annotations.expects_output_grain:
                    if result_grain != query_annotations.expects_output_grain:
                        raise GrainMismatchError(
                            f"Expected grain {query_annotations.expects_output_grain}, "
                            f"but join produces {result_grain}"
                        )

            elif operation.type == "GROUP BY":
                result_grain = operation.group_by_columns

                # Validate: GROUP BY grain must be coarser than input
                if not is_coarser(result_grain, input_grain):
                    raise InvalidAggregationError(
                        f"GROUP BY columns {result_grain} not valid for "
                        f"input grain {input_grain}"
                    )

        return AnalysisResult(
            grain=result_grain,
            warnings=[...],
            errors=[...]
        )

Usage:
    $ sql-grain-check query.sql

    ERROR in query.sql:15
    Grain mismatch in join:
      Left: customers (grain: customer_id)
      Right: customers_versioned (grain: customer_id, effective_from)
      Join keys: customer_id
    Result grain [customer_id, effective_from] ≠ expected [customer_id]
    This creates a fan trap (1:N relationship)
*/
```

**Benefits**:
- Works with existing SQL code
- No changes to SQL syntax
- Static analysis before query execution
- Can integrate with CI/CD pipelines

**Limitations**:
- Requires external tool
- Annotations in comments (not enforced by SQL parser)
- No standard for grain annotations

---

### Approach B: Hypothetical SQL Extensions (For Paper Discussion)

**Key Idea**: What if SQL supported grain annotations natively?

```sql
-- ============================================================================
-- Hypothetical SQL with Native Grain Support
-- ============================================================================

-- Syntax: CREATE TABLE ... WITH GRAIN (columns) AS grain_type

CREATE TABLE customers
WITH GRAIN (customer_id) AS entity_grain
(
    customer_id INT PRIMARY KEY,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(100) NOT NULL
);

CREATE TABLE customers_versioned
WITH GRAIN (customer_id, effective_from) AS versioned_grain
(
    customer_id INT NOT NULL,
    effective_from DATE NOT NULL,
    effective_to DATE,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(100) NOT NULL,
    PRIMARY KEY (customer_id, effective_from)
);

-- Query grain inference (automatic)
SELECT customer_id, SUM(revenue)
FROM sales
GROUP BY customer_id
-- Compiler infers: result grain = (customer_id)
;

-- Type error caught at compile time
SELECT *
FROM customers c
JOIN customers_versioned cv
    ON c.customer_id = cv.customer_id
-- COMPILE ERROR:
-- Grain mismatch in join:
--   customers: grain = (customer_id)
--   customers_versioned: grain = (customer_id, effective_from)
-- Cannot join tables with incompatible grains without explicit grain transformation
;

-- Correct: Explicit grain coarsening before join
WITH cv_latest AS (
    SELECT customer_id, name, email
    FROM customers_versioned
    QUALIFY ROW_NUMBER() OVER (PARTITION BY customer_id ORDER BY effective_from DESC) = 1
    -- Compiler infers: result grain = (customer_id) after QUALIFY
)
SELECT c.*, cv.name as versioned_name
FROM customers c
JOIN cv_latest cv
    ON c.customer_id = cv.customer_id
-- ✓ Compile success: both sides have grain (customer_id)
;

-- Grain-aware aggregation syntax
SELECT customer_id, date, SUM(revenue) AS total_revenue
FROM sales_channel
GROUP BY customer_id, date
ENSURE GRAIN (customer_id, date)
-- Compiler validates: GROUP BY columns exactly match ENSURE GRAIN clause
;

-- Grain transformation operators
CREATE TEMPORARY TABLE sales_entity AS
SELECT * FROM sales_versioned
COARSEN GRAIN TO (customer_id)  -- Hypothetical grain transformation
    BY LATEST(effective_from);  -- Keep latest version per customer
```

**Benefits** (if implemented):
- Native SQL support for grain
- Compile-time checking (part of SQL parser)
- Type-safe grain transformations
- Self-documenting queries

**Limitations**:
- Hypothetical (not in SQL standard)
- Would require significant SQL engine changes
- Backward compatibility challenges

**For Paper**: This demonstrates the value of grain-aware type systems and motivates the need for compile-time verification, even if implemented via external tools in practice.

---

## Summary Comparison

| Approach | Language | Compile-Time Check | Runtime Validation | Ease of Adoption |
|----------|----------|-------------------|-------------------|------------------|
| Generic `GrainedDataFrame[G]` | Python/PySpark | ✓ (mypy/pyright) | ✓ (defensive) | Medium |
| Type class `HasGrain` | Python/PySpark | ✓ (mypy/pyright) | ✓ (automatic) | Medium |
| Phantom type | Python/PySpark | ✓ (mypy/pyright) | ✗ (no check) | Easy |
| dbt config + tests | dbt | ✓ (dbt compile) | ✗ (N/A) | Medium |
| SQL annotations + analyzer | SQL | ✓ (external tool) | ✗ (N/A) | Hard |
| SQL extensions | SQL | ✓ (hypothetical) | ✗ (N/A) | N/A |

---

## 4. Lean 4

Lean 4 is a dependently-typed proof assistant where we can encode grain as a type-level relation with mathematical proofs. This enables **compile-time verification** with rigorous guarantees.

### Progressive Power Spectrum (Lean 4)

1. **Parametric types**: `DataType (Grain : Type)` - grain as type parameter
2. **Type relations**: `IsGrainOf G R` - grain relation with proofs
3. **Type classes**: `GrainedData R` - automatic grain inference
4. **Dependent records**: `DataWithGrain` - grain proof carried in data

We'll focus on approaches 2-4, as they provide the strongest guarantees.

---

### Approach A: Type-Level Grain Relation (IsGrainOf)

**Key Idea**: Define grain as a **relation** between types, containing the grain function, its inverse, and proofs of isomorphism.

This is the foundational approach used in [GrainDefinitions.lean](GrainDefinitions.lean).

```lean
-- ============================================================================
-- Core Grain Definitions (from GrainDefinitions.lean)
-- ============================================================================

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

-- Type-level subset relation
-- A ⊆_typ B means there exists a surjective projection p : B → A
def TypeSubset (A B : Type) : Prop :=
  ∃ (p : B → A), Function.Surjective p

notation:50 A " ⊆_typ " B => TypeSubset A B

-- IsGrainOf: G is the grain of R
-- This is a RELATION (a Prop), not a type class
-- It contains the grain function, inverse, and proofs
def IsGrainOf (G R : Type) : Prop :=
  (G ⊆_typ R) ∧  -- G is a subset of R
  (∃ (fg : G → R) (grain : R → G),
    Function.Bijective fg ∧  -- fg is an isomorphism
    (∀ r, fg (grain r) = r) ∧  -- fg ∘ grain = id
    (∀ g, grain (fg g) = g))  -- grain ∘ fg = id
  -- Note: Irreducibility omitted for brevity

-- Grain equality (isomorphism between grains)
def GrainEquiv (R1 R2 : Type) : Prop :=
  ∃ (G1 G2 : Type), IsGrainOf G1 R1 ∧ IsGrainOf G2 R2 ∧
    (∃ f : G1 → G2, Function.Bijective f)

notation:50 R1 " ≡_g " R2 => GrainEquiv R1 R2

-- Grain ordering (functional dependency)
def GrainOrdering (R1 R2 : Type) : Prop :=
  ∃ (G1 G2 : Type), IsGrainOf G1 R1 ∧ IsGrainOf G2 R2 ∧
    (∃ f : G1 → G2, Function.Injective f)

notation:50 R1 " ≤_g " R2 => GrainOrdering R1 R2

-- ============================================================================
-- Example: Bank Account with External Grain
-- ============================================================================

-- Domain types
structure Month : Type where
  year : Nat
  monthNum : Fin 12  -- 0-11
  deriving DecidableEq

structure AccountId : Type where
  id : Nat
  deriving DecidableEq

structure Amount : Type where
  cents : Int
  deriving DecidableEq

-- BankAccountSnapshot: grain is Month (NOT a field of the type!)
-- The grain can be external/derived/computed
structure BankAccountSnapshot : Type where
  account : AccountId
  balance : Amount
  lastTransactionDate : Nat  -- Unix timestamp

-- The grain is Month - computed externally from snapshot metadata
-- (e.g., the snapshot represents end-of-month balance)
structure SnapshotMonth : Type where
  month : Month

-- Grain function: given a month, construct a snapshot
-- (In real system, this would query a database)
axiom fg_snapshot : SnapshotMonth → BankAccountSnapshot

-- Inverse: extract month from snapshot
-- (In real system, this might parse metadata or use snapshot timestamp)
axiom grain_snapshot : BankAccountSnapshot → SnapshotMonth

-- Prove this is a grain relation
axiom snapshot_grain_proof :
  IsGrainOf SnapshotMonth BankAccountSnapshot

-- ============================================================================
-- Example: Customer with Multiple Grain Semantics
-- ============================================================================

-- Domain types
structure CustomerId : Type where
  id : Nat
  deriving DecidableEq

structure CustomerName : Type where
  name : String

structure Email : Type where
  email : String

structure EffectiveFrom : Type where
  date : Nat  -- Unix timestamp
  deriving DecidableEq

-- Customer type (same structure, different grain semantics)
structure Customer : Type where
  customerId : CustomerId
  name : CustomerName
  email : Email
  effectiveFrom : EffectiveFrom

-- Grain 1: Entity semantics (one row per customer)
structure CustomerEntityGrain : Type where
  customerId : CustomerId
  deriving DecidableEq

-- Grain 2: Versioned semantics (multiple versions per customer)
structure CustomerVersionedGrain : Type where
  customerId : CustomerId
  effectiveFrom : EffectiveFrom
  deriving DecidableEq

-- Grain functions for entity semantics
def fg_entity : CustomerEntityGrain → Customer :=
  λ g => {
    customerId := g.customerId,
    name := { name := "" },  -- Would be looked up from database
    email := { email := "" },
    effectiveFrom := { date := 0 }
  }

def grain_entity : Customer → CustomerEntityGrain :=
  λ c => { customerId := c.customerId }

-- Grain functions for versioned semantics
def fg_versioned : CustomerVersionedGrain → Customer :=
  λ g => {
    customerId := g.customerId,
    name := { name := "" },  -- Would be looked up from database
    email := { email := "" },
    effectiveFrom := g.effectiveFrom
  }

def grain_versioned : Customer → CustomerVersionedGrain :=
  λ c => { customerId := c.customerId, effectiveFrom := c.effectiveFrom }

-- Prove grain relations (proofs omitted with sorry for brevity)
theorem customer_entity_grain :
  IsGrainOf CustomerEntityGrain Customer := by
  sorry

theorem customer_versioned_grain :
  IsGrainOf CustomerVersionedGrain Customer := by
  sorry

-- ============================================================================
-- Using Grain Relations in Functions
-- ============================================================================

-- Function requiring entity grain semantics
def processEntityCustomers
  (customers : List Customer)
  (h : IsGrainOf CustomerEntityGrain Customer) :
  List CustomerId :=
  customers.map (λ c => c.customerId)

-- Function requiring versioned grain semantics
def processVersionedCustomers
  (customers : List Customer)
  (h : IsGrainOf CustomerVersionedGrain Customer) :
  List (CustomerId × EffectiveFrom) :=
  customers.map (λ c => (c.customerId, c.effectiveFrom))

-- Usage: Proof must be provided
#check processEntityCustomers [customer1, customer2] customer_entity_grain
-- ✓ Type checks - grain proof provided

-- Type error: wrong grain proof
-- #check processEntityCustomers [customer1, customer2] customer_versioned_grain
-- ✗ Type error: expected IsGrainOf CustomerEntityGrain Customer
--                  but got IsGrainOf CustomerVersionedGrain Customer
```

**Key Points**:
- `IsGrainOf G R` is a **relation (Prop)**, not a type class
- Grain can be **external** to the type structure (Month for BankAccountSnapshot)
- **Same type, different grains** yield different semantics (Customer)
- **Compile-time verification**: Functions require grain proofs

**Benefits**:
- Rigorous mathematical foundation
- Explicit grain proofs prevent misuse
- Works with ANY data type (not just tables)
- Zero runtime overhead (proofs erased during compilation)

---

### Approach B: Type Class for Grained Data

**Key Idea**: Define a **type class** `GrainedData R` that encodes grain relation as an implicit parameter. This enables automatic grain inference.

```lean
-- ============================================================================
-- Type Class: GrainedData
-- ============================================================================

-- Type class: data type R with grain G
-- This wraps the IsGrainOf relation for convenience
class GrainedData (R : Type) (G : Type) where
  grainProof : IsGrainOf G R
  -- Extract grain from element
  grain : R → G
  -- Reconstruct element from grain
  fromGrain : G → R
  -- Proofs
  grain_fromGrain : ∀ g, grain (fromGrain g) = g
  fromGrain_grain : ∀ r, fromGrain (grain r) = r

-- ============================================================================
-- Instances for Different Grain Semantics
-- ============================================================================

-- Instance 1: Customer with entity grain
instance : GrainedData Customer CustomerEntityGrain where
  grainProof := customer_entity_grain
  grain := grain_entity
  fromGrain := fg_entity
  grain_fromGrain := by sorry
  fromGrain_grain := by sorry

-- Note: Lean 4 allows multiple instances, but requires explicit selection
-- when ambiguous. We can use different namespaces or explicit instance terms.

-- Instance 2: Customer with versioned grain (in different namespace)
namespace Versioned
  instance : GrainedData Customer CustomerVersionedGrain where
    grainProof := customer_versioned_grain
    grain := grain_versioned
    fromGrain := fg_versioned
    grain_fromGrain := by sorry
    fromGrain_grain := by sorry
end Versioned

-- ============================================================================
-- Grain-Aware Functions Using Type Classes
-- ============================================================================

-- Function requiring specific grain G
-- The type class instance is automatically inferred
def extractGrains {R G : Type} [GrainedData R G]
  (data : List R) : List G :=
  data.map (λ r => GrainedData.grain r)

-- Usage: type class instance resolved automatically
#check extractGrains ([] : List Customer)  -- Uses entity grain instance
-- Result type: List CustomerEntityGrain

-- For versioned grain, use explicit namespace
#check Versioned.extractGrains ([] : List Customer)
-- Result type: List CustomerVersionedGrain

-- Function enforcing grain equality
def joinSameGrain {R1 R2 G : Type}
  [GrainedData R1 G] [GrainedData R2 G]
  (left : List R1) (right : List R2) :
  List (G × R1 × R2) :=
  -- Join on grain G (both types must have same grain)
  sorry  -- Implementation omitted

-- ✓ Type checks: both have entity grain
#check joinSameGrain
  ([] : List Customer)
  ([] : List Customer)

-- ✗ Type error: grain mismatch
-- Cannot join entity grain with versioned grain
-- #check joinSameGrain
--   ([] : List Customer)  -- entity grain
--   (Versioned.data)      -- versioned grain
-- Error: type class resolution fails (CustomerEntityGrain ≠ CustomerVersionedGrain)
```

**Benefits**:
- **Automatic grain inference**: Type class resolution finds the right instance
- **Implicit grain proofs**: No need to pass proofs explicitly
- **Cleaner API**: Functions are less verbose

**Limitations**:
- Multiple instances require disambiguation (namespaces or explicit terms)
- Less explicit than Approach A (may hide grain assumptions)

---

### Approach C: Dependent Record (Grain Proof in Data)

**Key Idea**: Bundle data with its grain proof in a **dependent record**. The grain is a type parameter, and the proof is a field.

```lean
-- ============================================================================
-- Dependent Record: CustomerWithGrain
-- ============================================================================

-- Data type parameterized by grain, carrying grain proof
structure CustomerWithGrain (Grain : Type) where
  data : Customer
  grainProof : IsGrainOf Grain Customer

-- ============================================================================
-- Smart Constructors for Different Grains
-- ============================================================================

-- Constructor for entity grain customers
def mkEntityCustomer (c : Customer) : CustomerWithGrain CustomerEntityGrain :=
  { data := c, grainProof := customer_entity_grain }

-- Constructor for versioned grain customers
def mkVersionedCustomer (c : Customer) : CustomerWithGrain CustomerVersionedGrain :=
  { data := c, grainProof := customer_versioned_grain }

-- ============================================================================
-- Grain-Aware Functions
-- ============================================================================

-- Function accepting only entity grain
def processEntityOnly
  (customers : List (CustomerWithGrain CustomerEntityGrain)) :
  List CustomerId :=
  customers.map (λ c => c.data.customerId)

-- Function accepting only versioned grain
def processVersionedOnly
  (customers : List (CustomerWithGrain CustomerVersionedGrain)) :
  List (CustomerId × EffectiveFrom) :=
  customers.map (λ c => (c.data.customerId, c.data.effectiveFrom))

-- Generic function accepting any grain G
def extractGrainsGeneric {G : Type}
  (customers : List (CustomerWithGrain G)) :
  List G :=
  -- Extract grain from each customer using the grain proof
  sorry  -- Would use grain function from proof

-- ============================================================================
-- Usage Examples
-- ============================================================================

-- Create customers with different grains
def customer1 : Customer := {
  customerId := { id := 1 },
  name := { name := "Alice" },
  email := { email := "alice@example.com" },
  effectiveFrom := { date := 20240101 }
}

def entityCustomer := mkEntityCustomer customer1
def versionedCustomer := mkVersionedCustomer customer1

-- ✓ Type checks: correct grain
#check processEntityOnly [entityCustomer]

-- ✗ Type error: wrong grain
-- #check processEntityOnly [versionedCustomer]
-- Error: type mismatch
--   CustomerWithGrain CustomerVersionedGrain
-- is not convertible to
--   CustomerWithGrain CustomerEntityGrain

-- ✓ Type checks: both use same generic function
#check extractGrainsGeneric [entityCustomer]    -- Returns List CustomerEntityGrain
#check extractGrainsGeneric [versionedCustomer] -- Returns List CustomerVersionedGrain

-- ============================================================================
-- Grain Transformation
-- ============================================================================

-- Transform versioned grain to entity grain (aggregate to latest)
def aggregateToEntity
  (versioned : List (CustomerWithGrain CustomerVersionedGrain)) :
  List (CustomerWithGrain CustomerEntityGrain) :=
  -- Group by customer_id, take latest version, produce entity grain
  sorry  -- Implementation omitted

-- The type signature documents the grain transformation!
-- Input: CustomerVersionedGrain (customer_id × effective_from)
-- Output: CustomerEntityGrain (customer_id)
```

**Benefits**:
- **Grain proof bundled with data**: Cannot lose track of grain
- **Type-safe grain transformations**: Signatures document grain changes
- **Prevents grain confusion**: Same data type with different grains are different types

**Limitations**:
- More verbose than type classes
- Grain proof carried at runtime (though erased in compiled code)

---

### Summary: Lean 4 Approaches

| Approach | Explicitness | Automation | Type Safety | Use Case |
|----------|--------------|------------|-------------|----------|
| **IsGrainOf relation** | High | Low | Maximum | Theoretical foundations, formal verification |
| **Type class** | Medium | High | High | Practical development with inference |
| **Dependent record** | High | Low | Maximum | When grain must be tracked with data |

**Recommended**: Use **type classes** for practical development, **dependent records** for critical transformations, and **IsGrainOf relations** for formal proofs.

---

## 5. Agda

Agda is a dependently-typed proof assistant similar to Lean 4. The fundamental approach is identical, with only syntactic differences.

### Progressive Power Spectrum (Agda)

Same as Lean 4:
1. **Parametric types**: `DataType (Grain : Set)` - grain as type parameter
2. **Type relations**: `G IsGrainOf R` - grain relation with proofs
3. **Records (type classes)**: `IsData` - grain proof parameterized record
4. **Universe polymorphism**: Grain definitions lifted to any universe level

---

### Approach A: Type-Level Grain Relation (Infix)

**Key Idea**: Define grain as a **relation** `_IsGrainOf_` using Agda's mixfix notation. This is the pattern from the user's [pdl-notions.agda](pdl-notions.agda).

```agda
-- ============================================================================
-- Core Grain Definitions (based on pdl-notions.agda)
-- ============================================================================

module GrainTheory where

open import Level using (Level; suc)
open import Relation.Binary using (Rel)
open import Function using (_∘_; id)
open import Data.Product using (∃; _×_; _,_)

-- Type-level relation: G is the grain of R
-- This is a RELATION, not a type class
-- Contains grain function, inverse, and proofs
_IsGrainOf_ : ∀ {ℓ} → Rel Set (suc (suc ℓ))
G IsGrainOf R =
    ∃ λ (grain : R → G) →
        ∃ λ (fg : G → R) →
              (fg ∘ grain ≡ id)
            × (grain ∘ fg ≡ id)
            × IsIrreducibleGrain grain
  where
    -- Irreducibility (simplified for example)
    postulate IsIrreducibleGrain : (R → G) → Set

-- Helper to extract grain function from relation
get-grain : ∀ {G R} → (G IsGrainOf R) → (R → G)
get-grain (grain , _) = grain

-- Helper to extract reconstruction function
get-fg : ∀ {G R} → (G IsGrainOf R) → (G → R)
get-fg (_ , fg , _) = fg

-- ============================================================================
-- Example: Bank Account with External Grain
-- ============================================================================

module BankAccountExample where
  open import Data.Nat using (ℕ)
  open import Data.Fin using (Fin)

  -- Month type (grain is external to BankAccountSnapshot)
  record Month : Set where
    field
      year : ℕ
      monthNum : Fin 12

  record AccountId : Set where
    field
      id : ℕ

  record Amount : Set where
    field
      cents : ℤ

  -- BankAccountSnapshot: grain is Month (NOT a field!)
  record BankAccountSnapshot : Set where
    field
      account : AccountId
      balance : Amount
      lastTransactionDate : ℕ

  -- Grain is Month - computed externally
  record SnapshotMonth : Set where
    field
      month : Month

  -- Grain relation proof (axiomatized for brevity)
  postulate
    grain-snapshot : BankAccountSnapshot → SnapshotMonth
    fg-snapshot : SnapshotMonth → BankAccountSnapshot
    snapshot-grain-proof : SnapshotMonth IsGrainOf BankAccountSnapshot

-- ============================================================================
-- Example: Customer with Multiple Grain Semantics
-- ============================================================================

module CustomerExample where
  open import Data.Nat using (ℕ)
  open import Data.String using (String)

  -- Domain types
  record CustomerId : Set where
    field
      id : ℕ

  record CustomerName : Set where
    field
      name : String

  record Email : Set where
    field
      email : String

  record EffectiveFrom : Set where
    field
      date : ℕ

  -- Customer type (same structure, different grain semantics)
  record Customer : Set where
    field
      customerId : CustomerId
      name : CustomerName
      email : Email
      effectiveFrom : EffectiveFrom

  -- Grain 1: Entity semantics
  record CustomerEntityGrain : Set where
    field
      customerId : CustomerId

  -- Grain 2: Versioned semantics
  record CustomerVersionedGrain : Set where
    field
      customerId : CustomerId
      effectiveFrom : EffectiveFrom

  -- Grain functions for entity semantics
  grain-entity : Customer → CustomerEntityGrain
  grain-entity c = record { customerId = Customer.customerId c }

  fg-entity : CustomerEntityGrain → Customer
  fg-entity g = record {
    customerId = CustomerEntityGrain.customerId g ;
    name = record { name = "" } ;  -- Would be looked up
    email = record { email = "" } ;
    effectiveFrom = record { date = 0 }
  }

  -- Grain functions for versioned semantics
  grain-versioned : Customer → CustomerVersionedGrain
  grain-versioned c = record {
    customerId = Customer.customerId c ;
    effectiveFrom = Customer.effectiveFrom c
  }

  fg-versioned : CustomerVersionedGrain → Customer
  fg-versioned g = record {
    customerId = CustomerVersionedGrain.customerId g ;
    name = record { name = "" } ;
    email = record { email = "" } ;
    effectiveFrom = CustomerVersionedGrain.effectiveFrom g
  }

  -- Grain relation proofs (axiomatized for brevity)
  postulate
    customer-entity-grain : CustomerEntityGrain IsGrainOf Customer
    customer-versioned-grain : CustomerVersionedGrain IsGrainOf Customer

  -- ============================================================================
  -- Using Grain Relations in Functions
  -- ============================================================================

  -- Function requiring entity grain semantics
  processEntityCustomers :
    (customers : List Customer) →
    (h : CustomerEntityGrain IsGrainOf Customer) →
    List CustomerId
  processEntityCustomers customers h =
    map (λ c → Customer.customerId c) customers

  -- Function requiring versioned grain semantics
  processVersionedCustomers :
    (customers : List Customer) →
    (h : CustomerVersionedGrain IsGrainOf Customer) →
    List (CustomerId × EffectiveFrom)
  processVersionedCustomers customers h =
    map (λ c → (Customer.customerId c , Customer.effectiveFrom c)) customers

  -- Usage: Proof must be provided
  example-entity : List CustomerId
  example-entity = processEntityCustomers [customer1 , customer2] customer-entity-grain
  -- ✓ Type checks - grain proof provided

  -- Type error: wrong grain proof
  -- example-error : List CustomerId
  -- example-error = processEntityCustomers [customer1 , customer2] customer-versioned-grain
  -- ✗ Type error: expected CustomerEntityGrain IsGrainOf Customer
  --                  but got CustomerVersionedGrain IsGrainOf Customer
```

**Key Syntactic Differences from Lean 4**:
- `_IsGrainOf_` uses mixfix notation (infix relation)
- `∃ λ (x : T) → ...` instead of `∃ (x : T), ...`
- `≡` for propositional equality instead of `=`
- Record syntax: `record { field = value }` instead of `{ field := value }`

**Everything else is conceptually identical to Lean 4**.

---

### Approach B: Record-Based Type Class (IsData)

**Key Idea**: Define `IsData` record parameterized by grain relation proof. This is a **type class pattern** in Agda (using instance arguments in Agda 2.6+).

```agda
-- ============================================================================
-- Record: IsData (Type Class Pattern)
-- ============================================================================

module IsDataPattern where
  open GrainTheory
  open CustomerExample

  -- IsData: Data type R with grain G and entity key EK
  -- Parameterized by grain relation proof
  record IsData {R G EK : Set}
                (grain-def-rel : G IsGrainOf R)
                (entity-key-def-rel : EK IsEntityKeyOf G R)
               : Set₁ where
    field
      Constraints : Cons R  -- Domain constraints (simplified)

    -- Extract grain function from relation
    grain : R → G
    grain = get-grain grain-def-rel

    -- Extract reconstruction function from relation
    fg : G → R
    fg = get-fg grain-def-rel

  -- Dummy definitions for example
  postulate
    Cons : Set → Set
    _IsEntityKeyOf_ : Set → Set → Set → Set

  -- ============================================================================
  -- Instances for Different Grain Semantics
  -- ============================================================================

  -- Instance 1: Customer with entity grain
  instance
    CustomerEntityData : IsData customer-entity-grain entity-key-proof-entity
    CustomerEntityData = record {
      Constraints = basic-constraints  -- Domain-specific constraints
    }
      where
        postulate
          basic-constraints : Cons Customer
          entity-key-proof-entity : CustomerEntityGrain IsEntityKeyOf CustomerEntityGrain Customer

  -- Instance 2: Customer with versioned grain (named explicitly)
  instance
    CustomerVersionedData : IsData customer-versioned-grain entity-key-proof-versioned
    CustomerVersionedData = record {
      Constraints = versioned-constraints
    }
      where
        postulate
          versioned-constraints : Cons Customer
          entity-key-proof-versioned : CustomerVersionedGrain IsEntityKeyOf CustomerVersionedGrain Customer

  -- ============================================================================
  -- Grain-Aware Functions Using Instance Arguments
  -- ============================================================================

  -- Function using instance argument (Agda 2.6+)
  extractGrains : ∀ {R G EK} {grain-rel : G IsGrainOf R} {ek-rel : EK IsEntityKeyOf G R}
                  → {{_ : IsData grain-rel ek-rel}}
                  → List R → List G
  extractGrains {{dataInst}} data =
    map (IsData.grain dataInst) data

  -- Usage: instance resolved automatically
  example-extract : List CustomerEntityGrain
  example-extract = extractGrains {grain-rel = customer-entity-grain} [customer1 , customer2]
  -- ✓ Type checks - instance CustomerEntityData resolved automatically
```

**Key Points**:
- **Named instances**: Agda allows multiple instances (must be named explicitly when ambiguous)
- **Instance arguments**: `{{_ : IsData ...}}` for automatic resolution (Agda 2.6+)
- **Grain function extracted from relation**: `grain = get-grain grain-def-rel`

**Benefits**:
- Same as Lean 4 type class approach
- Explicit instance names avoid ambiguity
- Automatic instance resolution (with instance arguments)

---

### Approach C: Parameterized Data Type

**Key Idea**: Same as Lean 4's dependent record approach.

```agda
-- ============================================================================
-- Parameterized Data Type: CustomerWithGrain
-- ============================================================================

module ParameterizedGrain where
  open GrainTheory
  open CustomerExample

  -- Data type parameterized by grain, carrying grain proof
  record CustomerWithGrain (Grain : Set) : Set₁ where
    field
      data : Customer
      grainProof : Grain IsGrainOf Customer

  -- ============================================================================
  -- Smart Constructors
  -- ============================================================================

  mkEntityCustomer : Customer → CustomerWithGrain CustomerEntityGrain
  mkEntityCustomer c = record {
    data = c ;
    grainProof = customer-entity-grain
  }

  mkVersionedCustomer : Customer → CustomerWithGrain CustomerVersionedGrain
  mkVersionedCustomer c = record {
    data = c ;
    grainProof = customer-versioned-grain
  }

  -- ============================================================================
  -- Grain-Aware Functions
  -- ============================================================================

  processEntityOnly : List (CustomerWithGrain CustomerEntityGrain) → List CustomerId
  processEntityOnly customers =
    map (λ c → Customer.customerId (CustomerWithGrain.data c)) customers

  processVersionedOnly : List (CustomerWithGrain CustomerVersionedGrain)
                       → List (CustomerId × EffectiveFrom)
  processVersionedOnly customers =
    map (λ c → let cust = CustomerWithGrain.data c
               in (Customer.customerId cust , Customer.effectiveFrom cust))
        customers

  -- ============================================================================
  -- Usage Examples
  -- ============================================================================

  customer1 : Customer
  customer1 = record {
    customerId = record { id = 1 } ;
    name = record { name = "Alice" } ;
    email = record { email = "alice@example.com" } ;
    effectiveFrom = record { date = 20240101 }
  }

  entityCustomer : CustomerWithGrain CustomerEntityGrain
  entityCustomer = mkEntityCustomer customer1

  versionedCustomer : CustomerWithGrain CustomerVersionedGrain
  versionedCustomer = mkVersionedCustomer customer1

  -- ✓ Type checks: correct grain
  example-entity : List CustomerId
  example-entity = processEntityOnly (entityCustomer ∷ [])

  -- ✗ Type error: wrong grain
  -- example-error : List CustomerId
  -- example-error = processEntityOnly (versionedCustomer ∷ [])
  -- Error: type mismatch
  --   CustomerWithGrain CustomerVersionedGrain
  -- !=
  --   CustomerWithGrain CustomerEntityGrain
```

**Identical to Lean 4 approach**, just different syntax.

---

### Summary: Agda Approaches

| Approach | Lean 4 Equivalent | Key Difference |
|----------|-------------------|----------------|
| **_IsGrainOf_ relation** | `IsGrainOf G R` | Mixfix notation (infix) |
| **IsData record** | Type class | Named instances, explicit selection |
| **CustomerWithGrain** | Dependent record | Identical concept |

**Agda and Lean 4 have the same fundamental capabilities**. Choice is based on:
- **Syntax preference**: Agda's mixfix vs Lean 4's notation
- **Ecosystem**: Lean 4 has mathlib, Agda has standard library
- **Tooling**: Lean 4 LSP vs Agda mode for Emacs/VS Code

---

## 6. Haskell

Haskell provides a rich type system with type classes, data kinds, GADTs, and type families. We can encode grain with increasing sophistication.

### Progressive Power Spectrum (Haskell)

1. **Type classes (simple)**: `HasGrain a` with associated type for grain
2. **Phantom types**: `DataFrame g a` where `g` is phantom type parameter
3. **DataKinds + GADTs**: Promote grain to type-level, use GADTs for enforcement
4. **Type families**: Compute grain transformations at type level
5. **Singletons**: Runtime representation of type-level grain for proofs

---

### Approach A: Type Class with Associated Type (Simple)

**Key Idea**: Define `HasGrain` type class with an associated type for the grain.

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- ============================================================================
-- Type Class: HasGrain
-- ============================================================================

-- Type class: data type 'a' has grain 'Grain a'
class HasGrain a where
  type Grain a :: *
  grain :: a -> Grain a
  fromGrain :: Grain a -> a

-- ============================================================================
-- Example: Customer with Different Grain Semantics
-- ============================================================================

-- Domain types
newtype CustomerId = CustomerId Int deriving (Eq, Show)
newtype CustomerName = CustomerName String deriving (Eq, Show)
newtype Email = Email String deriving (Eq, Show)
newtype EffectiveFrom = EffectiveFrom Int deriving (Eq, Show)

-- Customer data type (same structure)
data Customer = Customer
  { customerId :: CustomerId
  , customerName :: CustomerName
  , email :: Email
  , effectiveFrom :: EffectiveFrom
  } deriving (Eq, Show)

-- Grain types
data CustomerEntityGrain = CustomerEntityGrain CustomerId
  deriving (Eq, Show)

data CustomerVersionedGrain = CustomerVersionedGrain CustomerId EffectiveFrom
  deriving (Eq, Show)

-- ============================================================================
-- Problem: Cannot have multiple instances for same type!
-- ============================================================================

-- This won't work:
-- instance HasGrain Customer where
--   type Grain Customer = CustomerEntityGrain
--   grain c = CustomerEntityGrain (customerId c)
--   fromGrain (CustomerEntityGrain cid) =
--     Customer cid (CustomerName "") (Email "") (EffectiveFrom 0)

-- instance HasGrain Customer where  -- ERROR: Duplicate instance!
--   type Grain Customer = CustomerVersionedGrain
--   ...

-- Solution: Use newtype wrappers to differentiate
newtype EntityCustomer = EntityCustomer Customer deriving (Eq, Show)
newtype VersionedCustomer = VersionedCustomer Customer deriving (Eq, Show)

instance HasGrain EntityCustomer where
  type Grain EntityCustomer = CustomerEntityGrain
  grain (EntityCustomer c) = CustomerEntityGrain (customerId c)
  fromGrain (CustomerEntityGrain cid) =
    EntityCustomer $ Customer cid (CustomerName "") (Email "") (EffectiveFrom 0)

instance HasGrain VersionedCustomer where
  type Grain VersionedCustomer = CustomerVersionedGrain
  grain (VersionedCustomer c) =
    CustomerVersionedGrain (customerId c) (effectiveFrom c)
  fromGrain (CustomerVersionedGrain cid eff) =
    VersionedCustomer $ Customer cid (CustomerName "") (Email "") eff

-- ============================================================================
-- Grain-Aware Functions
-- ============================================================================

-- Extract grains from list
extractGrains :: HasGrain a => [a] -> [Grain a]
extractGrains = map grain

-- Usage
exampleEntity :: [CustomerEntityGrain]
exampleEntity = extractGrains [EntityCustomer customer1, EntityCustomer customer2]
-- ✓ Type checks

exampleVersioned :: [CustomerVersionedGrain]
exampleVersioned = extractGrains [VersionedCustomer customer1, VersionedCustomer customer2]
-- ✓ Type checks

-- Join with same grain
joinSameGrain :: (HasGrain a, HasGrain b, Grain a ~ Grain b, Eq (Grain a))
              => [a] -> [b] -> [(Grain a, a, b)]
joinSameGrain left right =
  [ (g, l, r)
  | l <- left
  , r <- right
  , let g = grain l
  , g == grain r
  ]

-- ✓ Type checks: both have entity grain (via newtype wrappers)
exampleJoin :: [(CustomerEntityGrain, EntityCustomer, EntityCustomer)]
exampleJoin = joinSameGrain
  [EntityCustomer customer1]
  [EntityCustomer customer2]

-- ✗ Type error: grain mismatch
-- badJoin = joinSameGrain
--   [EntityCustomer customer1]     -- Grain = CustomerEntityGrain
--   [VersionedCustomer customer2]  -- Grain = CustomerVersionedGrain
-- Error: Couldn't match type 'CustomerEntityGrain' with 'CustomerVersionedGrain'
```

**Benefits**:
- Type-level grain tracked via associated type
- Type checker enforces grain compatibility
- Clean API with type inference

**Limitations**:
- **Cannot have multiple instances for same type** (requires newtype wrappers)
- Less powerful than GADTs approach

---

### Approach B: Phantom Types with DataKinds (Intermediate)

**Key Idea**: Use **phantom type parameter** for grain, promote grain types to type-level kinds with DataKinds.

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

import GHC.TypeLits (Symbol)

-- ============================================================================
-- Grain Types Promoted to Type-Level Kinds
-- ============================================================================

-- Grain semantics (promoted to kind)
data GrainSemantics = EntityGrain | VersionedGrain | EventGrain

-- ============================================================================
-- DataFrame Parameterized by Grain
-- ============================================================================

-- DataFrame with phantom grain type parameter
-- 'g :: GrainSemantics' is a type-level grain kind
data DataFrame (g :: GrainSemantics) a = DataFrame [a]
  deriving (Show)

-- ============================================================================
-- Smart Constructors
-- ============================================================================

mkEntityDF :: [Customer] -> DataFrame 'EntityGrain Customer
mkEntityDF = DataFrame

mkVersionedDF :: [Customer] -> DataFrame 'VersionedGrain Customer
mkVersionedDF = DataFrame

mkEventDF :: [Customer] -> DataFrame 'EventGrain Customer
mkEventDF = DataFrame

-- ============================================================================
-- Grain-Aware Functions
-- ============================================================================

-- Function accepting only entity grain
processEntityDF :: DataFrame 'EntityGrain Customer -> [CustomerId]
processEntityDF (DataFrame customers) = map customerId customers

-- Function accepting only versioned grain
processVersionedDF :: DataFrame 'VersionedGrain Customer
                   -> [(CustomerId, EffectiveFrom)]
processVersionedDF (DataFrame customers) =
  map (\c -> (customerId c, effectiveFrom c)) customers

-- Generic function accepting any grain
processAnyGrain :: DataFrame g Customer -> Int
processAnyGrain (DataFrame customers) = length customers

-- Join with same grain (grain parameter must match)
joinSameGrainDF :: DataFrame g a -> DataFrame g b -> DataFrame g (a, b)
joinSameGrainDF (DataFrame left) (DataFrame right) =
  DataFrame [(l, r) | l <- left, r <- right]

-- ============================================================================
-- Usage Examples
-- ============================================================================

customer1 :: Customer
customer1 = Customer (CustomerId 1) (CustomerName "Alice") (Email "alice@example.com") (EffectiveFrom 20240101)

customer2 :: Customer
customer2 = Customer (CustomerId 2) (CustomerName "Bob") (Email "bob@example.com") (EffectiveFrom 20240601)

entityDF :: DataFrame 'EntityGrain Customer
entityDF = mkEntityDF [customer1, customer2]

versionedDF :: DataFrame 'VersionedGrain Customer
versionedDF = mkVersionedDF [customer1, customer2]

-- ✓ Type checks: correct grain
exampleProcessEntity :: [CustomerId]
exampleProcessEntity = processEntityDF entityDF

-- ✗ Type error: wrong grain
-- errorExample = processEntityDF versionedDF
-- Error: Couldn't match type ''VersionedGrain' with ''EntityGrain'

-- ✓ Type checks: same grain join
exampleJoinSame :: DataFrame 'EntityGrain (Customer, Customer)
exampleJoinSame = joinSameGrainDF entityDF entityDF

-- ✗ Type error: grain mismatch
-- errorJoin = joinSameGrainDF entityDF versionedDF
-- Error: Couldn't match type ''VersionedGrain' with ''EntityGrain'

-- ============================================================================
-- Grain Transformation at Type Level
-- ============================================================================

-- Type family: compute result grain after aggregation
type family AggregateGrain (g :: GrainSemantics) :: GrainSemantics where
  AggregateGrain 'VersionedGrain = 'EntityGrain
  AggregateGrain 'EventGrain = 'EntityGrain
  AggregateGrain 'EntityGrain = 'EntityGrain

-- Aggregation function with grain transformation
aggregateToEntity :: DataFrame 'VersionedGrain Customer
                  -> DataFrame (AggregateGrain 'VersionedGrain) Customer
aggregateToEntity (DataFrame customers) =
  -- Group by customer_id, take latest version
  DataFrame (nubBy (\c1 c2 -> customerId c1 == customerId c2) customers)
  where
    nubBy :: (a -> a -> Bool) -> [a] -> [a]
    nubBy _ [] = []
    nubBy eq (x:xs) = x : nubBy eq (filter (not . eq x) xs)

-- Type signature shows grain transformation!
-- Input: DataFrame 'VersionedGrain Customer
-- Output: DataFrame 'EntityGrain Customer (since AggregateGrain 'VersionedGrain = 'EntityGrain)

exampleAggregate :: DataFrame 'EntityGrain Customer
exampleAggregate = aggregateToEntity versionedDF
-- ✓ Type checks: grain transformation verified at compile time
```

**Benefits**:
- **Type-level grain**: Grain is a type parameter, not a value
- **Compile-time verification**: Type checker enforces grain compatibility
- **Type families**: Compute grain transformations at type level
- **No runtime overhead**: Phantom types erased during compilation

**Limitations**:
- Requires GHC extensions (DataKinds, GADTs, TypeFamilies)
- More complex than simple type classes
- Cannot easily pattern match on grain at value level

---

### Approach C: GADTs with Grain Proofs (Advanced)

**Key Idea**: Use **GADTs** to encode grain proofs directly in the data constructor.

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

-- ============================================================================
-- GADT: DataFrame with Grain Proof
-- ============================================================================

-- Grain types (promoted to kinds)
data GrainSemantics = EntityGrain | VersionedGrain | EventGrain

-- GADT: DataFrame with grain constraint encoded in constructor
data DataFrameGADT (g :: GrainSemantics) a where
  -- Entity grain: only accepts entity semantics
  EntityDF :: [Customer] -> DataFrameGADT 'EntityGrain Customer

  -- Versioned grain: only accepts versioned semantics
  VersionedDF :: [Customer] -> DataFrameGADT 'VersionedGrain Customer

  -- Event grain: only accepts event semantics
  EventDF :: [Customer] -> DataFrameGADT 'EventGrain Customer

deriving instance Show (DataFrameGADT g Customer)

-- ============================================================================
-- Pattern Matching Provides Grain Information
-- ============================================================================

-- Process DataFrame: grain known from pattern match
processDF :: DataFrameGADT g Customer -> String
processDF (EntityDF customers) =
  "Entity grain: " ++ show (length customers) ++ " customers"
processDF (VersionedDF customers) =
  "Versioned grain: " ++ show (length customers) ++ " versions"
processDF (EventDF customers) =
  "Event grain: " ++ show (length customers) ++ " events"

-- Function accepting only entity grain
processEntityGADT :: DataFrameGADT 'EntityGrain Customer -> [CustomerId]
processEntityGADT (EntityDF customers) = map customerId customers

-- Function accepting only versioned grain
processVersionedGADT :: DataFrameGADT 'VersionedGrain Customer
                     -> [(CustomerId, EffectiveFrom)]
processVersionedGADT (VersionedDF customers) =
  map (\c -> (customerId c, effectiveFrom c)) customers

-- ============================================================================
-- Grain Transformation with GADTs
-- ============================================================================

-- Transform versioned to entity grain
aggregateGADT :: DataFrameGADT 'VersionedGrain Customer
              -> DataFrameGADT 'EntityGrain Customer
aggregateGADT (VersionedDF customers) =
  EntityDF (nubBy (\c1 c2 -> customerId c1 == customerId c2) customers)
  where
    nubBy :: (a -> a -> Bool) -> [a] -> [a]
    nubBy _ [] = []
    nubBy eq (x:xs) = x : nubBy eq (filter (not . eq x) xs)

-- ============================================================================
-- Usage Examples
-- ============================================================================

entityGADT :: DataFrameGADT 'EntityGrain Customer
entityGADT = EntityDF [customer1, customer2]

versionedGADT :: DataFrameGADT 'VersionedGrain Customer
versionedGADT = VersionedDF [customer1, customer2]

-- ✓ Type checks: correct grain
exampleEntityGADT :: [CustomerId]
exampleEntityGADT = processEntityGADT entityGADT

-- ✗ Type error: wrong grain
-- errorGADT = processEntityGADT versionedGADT
-- Error: Couldn't match type ''VersionedGrain' with ''EntityGrain'

-- ✓ Type checks: grain transformation
exampleAggregateGADT :: DataFrameGADT 'EntityGrain Customer
exampleAggregateGADT = aggregateGADT versionedGADT
```

**Benefits**:
- **Grain proof in constructor**: Cannot construct DataFrame with wrong grain
- **Pattern matching reveals grain**: Type information flows from pattern match
- **Maximum type safety**: Grain verified at construction time

**Limitations**:
- More verbose (need separate constructor per grain)
- Cannot easily add new grains without modifying GADT

---

### Summary: Haskell Approaches

| Approach | Power Level | Type Safety | Flexibility | Complexity |
|----------|-------------|-------------|-------------|------------|
| **Type classes** | Low | Medium | High (extensible) | Low |
| **Phantom types + DataKinds** | Medium | High | Medium | Medium |
| **GADTs** | High | Maximum | Low (fixed grains) | High |

**Recommended**:
- **Production code**: Phantom types + DataKinds (good balance)
- **Research/verification**: GADTs (maximum guarantees)
- **Quick prototyping**: Type classes (simplest)

---

## Progressive Power Spectrum: Cross-Language Comparison

This table shows how grain encoding power increases across type systems:

| Feature | Python/PySpark | dbt | SQL | Haskell | Lean 4 / Agda |
|---------|---------------|-----|-----|---------|---------------|
| **Runtime grain validation** | ✓ | ✗ | ✗ | ✗ | ✗ |
| **Compile-time type checking** | ✓ (mypy) | ✓ (dbt compile) | ✗ | ✓ | ✓ |
| **Grain as type parameter** | ✓ | ✗ | ✗ | ✓ | ✓ |
| **Type-level grain computation** | ✗ | ✗ | ✗ | ✓ (type families) | ✓ (computation) |
| **Grain relation with proofs** | ✗ | ✗ | ✗ | ✗ | ✓ |
| **Formal verification** | ✗ | ✗ | ✗ | ✗ | ✓ |
| **Zero runtime overhead** | ✗ | N/A | N/A | ✓ | ✓ |
| **Mathematical rigor** | Low | Low | Low | Medium | Maximum |

### Power Hierarchy

1. **SQL (weakest)**: No type system support, relies on external analyzers
2. **dbt**: Compile-time macros, but limited type system
3. **Python**: Gradual typing, runtime validation, optional static checking
4. **Haskell**: Strong static typing, type-level computation, phantom types
5. **Lean 4 / Agda (strongest)**: Dependent types, formal proofs, mathematical rigor

### When to Use Each Approach

| Use Case | Recommended Language | Approach |
|----------|---------------------|----------|
| **Production data pipelines** | Python/PySpark | `GrainedDataFrame[G]` with mypy |
| **dbt transformations** | dbt | Grain config + custom tests |
| **Legacy SQL** | SQL | Comment annotations + static analyzer |
| **Research prototype** | Haskell | Phantom types + DataKinds |
| **Formal verification** | Lean 4 / Agda | IsGrainOf relation + proofs |
| **Academic paper** | Lean 4 / Agda | Full formalization |

---

## Key Takeaways

1. **Grain applies to ANY data type**, not just tables/DataFrames
   - BankAccountSnapshot with external grain (Month)
   - Customer with multiple grain semantics (entity/versioned/event)

2. **Same fundamental approach across dependent type systems**
   - Lean 4 and Agda use identical concepts (just different syntax)
   - `IsGrainOf` relation contains grain function, inverse, and proofs

3. **Progressive power spectrum**
   - Simple: Parametric types (`DataFrame[G]`)
   - Medium: Type classes (automatic inference)
   - Advanced: Type relations with proofs (formal verification)

4. **Compile-time verification enables "verify and deploy"**
   - Type checker catches grain mismatches before execution
   - Zero computational cost (proofs erased in compiled code)

5. **Trade-offs matter**
   - Production systems: Balance type safety with practicality (Python/Haskell)
   - Research/verification: Maximum rigor (Lean 4/Agda)
   - Legacy systems: External tools (SQL static analyzers)

---

## References

- Python typing documentation: https://docs.python.org/3/library/typing.html
- PySpark API: https://spark.apache.org/docs/latest/api/python/
- dbt documentation: https://docs.getdbt.com/
- Haskell wiki (GADTs): https://wiki.haskell.org/GADTs_for_dummies
- Lean 4 documentation: https://lean-lang.org/documentation/
- Agda documentation: https://agda.readthedocs.io/
- Paper: "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost" (VLDB 2026)
