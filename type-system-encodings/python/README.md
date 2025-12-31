# Python Grain Encoding Implementation

This folder contains the Python implementation of grain-aware type checking using Approach A: Generic DataFrame with Grain Type Parameter.

## Files

- `grained_dataframe.py`: Main implementation with `GrainedDataFrame[G]` generic type

## Requirements

- Python 3.9+
- PySpark
- mypy (for type checking)

## Type Checking

Run mypy to verify grain-aware type checking:

```bash
mypy grained_dataframe.py
```

## Example Usage

```python
from grained_dataframe import GrainedDataFrame, EntityGrain, VersionedGrain
from pyspark.sql import SparkSession

spark = SparkSession.builder.getOrCreate()

# Create entity grain DataFrame
entity_data = spark.createDataFrame([
    (1, "Alice", "alice@example.com"),
    (2, "Bob", "bob@example.com")
], ["customer_id", "name", "email"])

entity_df = GrainedDataFrame(entity_data, EntityGrain())

# Type checker enforces grain compatibility
result = process_entity_customers(entity_df)  # ✓ Type checks
# result = process_entity_customers(versioned_df)  # ✗ Type error
```

## Grain Examples

Based on the paper (Section 3.2: Grain Determines Data Semantics):

1. **Entity Grain** (`EntityGrain`): `G[Customer] = CustomerId`
   - One distinct customer per `CustomerId`
   - No inherent ordering

2. **Versioned Grain** (`VersionedGrain`): `G[Customer] = CustomerId × EffectiveFrom`
   - Multiple time-stamped versions per customer
   - Causal ordering among versions

3. **Event Grain** (`EventGrain`): `G[Customer] = CustomerId × CreatedOn × EventType`
   - Each creation/modification event
   - Allows `CustomerId` reuse across events

