# Grain Encoding Implementations

This directory contains implementations of grain encoding in type systems across three languages, demonstrating the progressive power spectrum discussed in the paper (Section 6.1.4: Encoding Grain in the Type System).

## Structure

Each language has its own folder with a complete implementation:

- **`python/`**: Approach A - Generic DataFrame with Grain Type Parameter
- **`lean4/`**: Approach B - Type Class for Grained Data  
- **`agda/`**: Approach B - Type Class for Grained Data (equivalent to Lean 4)

## Grain Examples

All implementations include examples based on the paper (Section 3.2: Grain Determines Data Semantics):

1. **Entity Grain**: `G[Customer] = CustomerId`
   - One distinct customer per `CustomerId`
   - No inherent ordering

2. **Versioned Grain**: `G[Customer] = CustomerId × EffectiveFrom`
   - Multiple time-stamped versions per customer
   - Causal ordering among versions

3. **Event Grain**: `G[Customer] = CustomerId × CreatedOn × EventType`
   - Each creation/modification event
   - Allows `CustomerId` reuse across events

## Language-Specific Details

### Python (`python/`)

- **Approach**: Generic DataFrame with Grain Type Parameter
- **Type Checking**: mypy/pyright (optional static checking)
- **Runtime Validation**: Yes (defensive programming)
- **Files**: `grained_dataframe.py`, `requirements.txt`, `README.md`

### Lean 4 (`lean4/`)

- **Approach**: Type Class for Grained Data
- **Type Checking**: Compile-time (automatic)
- **Formal Proofs**: Yes (with mathematical rigor)
- **Files**: `GrainDefinitions.lean`, `GrainedData.lean`, `lakefile.lean`, `README.md`

### Agda (`agda/`)

- **Approach**: Type Class for Grained Data (fully equivalent to Lean 4)
- **Type Checking**: Compile-time (automatic)
- **Formal Proofs**: Yes (with mathematical rigor)
- **Files**: `GrainDefinitions.agda`, `GrainedData.agda`, `README.md`

## Equivalence

The Lean 4 and Agda implementations are **fully equivalent**:
- Same type class pattern (`GrainedData` / `IsData`)
- Same grain types and functions
- Same namespace/module structure for disambiguation
- Same grain-aware functions
- Only syntactic differences (Agda's mixfix notation vs Lean 4's notation)

## Building

### Python
```bash
cd python
pip install -r requirements.txt
mypy grained_dataframe.py
```

### Lean 4
```bash
cd lean4
lake build
```

### Agda
```bash
cd agda
agda GrainedData.agda
```

## References

Based on:
- Paper: "Grain-Aware Data Transformations: Type-Level Correctness Verification at Zero Computational Cost" (VLDB 2026)
- Section 3.2: Grain Determines Data Semantics
- Section 6.1.4: Encoding Grain in the Type System
- `GRAIN_TYPE_SYSTEM_ENCODINGS.md`: Detailed implementation patterns

