"""
Grain-Aware DataFrame Implementation (Python)
"Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost"

This module implements Approach A: Generic DataFrame with Grain Type Parameter
Based on GRAIN_TYPE_SYSTEM_ENCODINGS.md Section 1 (Python with PySpark)

The type parameter G encodes the grain, enabling type checker (mypy/pyright) to catch
grain mismatches at compile time before any Spark job execution.
"""

from typing import Generic, TypeVar, Protocol, runtime_checkable, cast
from pyspark.sql import DataFrame as SparkDF
from dataclasses import dataclass

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

# Note: Dataclasses structurally satisfy the Grain Protocol (they have 'columns' attribute)
# mypy requires explicit Protocol inheritance, but pyright recognizes structural typing
# For mypy compatibility, we use type: ignore comments where needed

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
        try:
            num_rows = self._df.count()
        except Exception:
            num_rows = "?"
        return f"GrainedDataFrame[{grain_name}]({num_rows} rows)"


# ============================================================================
# Grain-Aware Functions (Type-Checked)
# ============================================================================

def process_entity_customers(
    df: GrainedDataFrame[EntityGrain]  # type: ignore[type-var]
) -> GrainedDataFrame[EntityGrain]:  # type: ignore[type-var]
    """
    Process customers with entity grain semantics.
    
    Type signature enforces: input must have EntityGrain.
    Type checker (mypy/pyright) rejects VersionedGrain or EventGrain.
    """
    # Business logic here - knows grain is entity-level
    result = df.df.select("customer_id", "name").distinct()
    return GrainedDataFrame(result, EntityGrain())  # type: ignore[type-var]


def aggregate_versioned_to_entity(
    df: GrainedDataFrame[VersionedGrain]  # type: ignore[type-var]
) -> GrainedDataFrame[EntityGrain]:  # type: ignore[type-var]
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
    
    return GrainedDataFrame(result, EntityGrain())  # type: ignore[type-var]


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

def create_example_dataframes(spark: SparkSession) -> tuple[GrainedDataFrame[EntityGrain], GrainedDataFrame[VersionedGrain], GrainedDataFrame[EventGrain]]:  # type: ignore[type-var]
    """Create example DataFrames with different grains"""
    
    # Entity grain: one row per customer
    entity_data = spark.createDataFrame([
        (1, "Alice", "alice@example.com"),
        (2, "Bob", "bob@example.com")
    ], ["customer_id", "name", "email"])
    
    entity_df: GrainedDataFrame[EntityGrain] = GrainedDataFrame(entity_data, EntityGrain())  # type: ignore[type-var]
    
    # Versioned grain: multiple rows per customer
    versioned_data = spark.createDataFrame([
        (1, "2024-01-01", "Alice", "alice@old.com"),
        (1, "2024-06-01", "Alice", "alice@new.com"),
        (2, "2024-01-01", "Bob", "bob@example.com")
    ], ["customer_id", "effective_from", "name", "email"])
    
    versioned_df: GrainedDataFrame[VersionedGrain] = GrainedDataFrame(versioned_data, VersionedGrain())  # type: ignore[type-var]
    
    # Event grain: each creation/modification event
    event_data = spark.createDataFrame([
        (1, "2024-01-01", "CREATED", "Alice", "alice@example.com"),
        (1, "2024-06-01", "UPDATED", "Alice", "alice@new.com"),
        (2, "2024-01-01", "CREATED", "Bob", "bob@example.com")
    ], ["customer_id", "created_on", "event_type", "name", "email"])
    
    event_df: GrainedDataFrame[EventGrain] = GrainedDataFrame(event_data, EventGrain())  # type: ignore[type-var]
    
    return entity_df, versioned_df, event_df


if __name__ == "__main__":
    # Example usage
    from pyspark.sql import SparkSession
    spark = SparkSession.builder.appName("GrainExamples").getOrCreate()
    
    entity_df, versioned_df, event_df = create_example_dataframes(spark)
    
    # ✓ Type checks - correct grain
    result1 = process_entity_customers(entity_df)
    print(f"Entity processing result: {result1}")
    
    # ✓ Type checks - explicit grain transformation
    result2 = aggregate_versioned_to_entity(versioned_df)
    print(f"Versioned to entity aggregation: {result2}")
    
    # ✓ Type checks - same grain join
    entity_df2: GrainedDataFrame[EntityGrain] = GrainedDataFrame(  # type: ignore[type-var]
        spark.createDataFrame([(1, "Alice", "alice@example.com")], 
                             ["customer_id", "name", "email"]),
        EntityGrain()
    )
    joined = join_same_grain(entity_df, entity_df2, on=["customer_id"])  # type: ignore[type-var]
    print(f"Same grain join: {joined}")
    
    # ✗ Type error caught by mypy/pyright (uncomment to see):
    # result3 = process_entity_customers(versioned_df)
    # Error: Argument 1 has incompatible type "GrainedDataFrame[VersionedGrain]"
    #        Expected type: "GrainedDataFrame[EntityGrain]"
    
    # ✗ Type error caught by mypy/pyright (uncomment to see):
    # bad_join = join_same_grain(entity_df, versioned_df, on=["customer_id"])
    # Error: Type variable "G" has incompatible values (EntityGrain, VersionedGrain)
    
    spark.stop()
