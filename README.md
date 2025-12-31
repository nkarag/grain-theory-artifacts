# Grain Theory Artifacts

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

This repository contains all artifacts supporting the VLDB 2026 paper:

**"Grain-Aware Data Transformations: Type-Level Formal Verification at Zero Computational Cost"**
by Nikos Karayannidis

## Overview

This repository provides comprehensive artifacts demonstrating grain theory's implementation and formal verification capabilities:

1. **Lean 4 Formalization** - Machine-checkable formal proofs of pipeline correctness
2. **Type System Encodings** - Grain encoding implementations across three type systems (Python/mypy, Lean 4, Agda)
3. **SQL Validation** - 100 equi-join examples validating the grain inference formulas

All artifacts are fully functional and demonstrate that grain theory enables systematic verification of data transformation correctness through type-level reasoning.

## Repository Structure

```
grain-theory-artifacts/
├── lean4-formalization/       # Machine-checkable formal verification
│   ├── Pipeline1.lean         # Correct pipeline (type-checks)
│   ├── Pipeline2.lean         # Incorrect pipeline A (type error)
│   ├── Pipeline3.lean         # Incorrect pipeline B (type error)
│   ├── GrainDefinitions.lean  # Core grain theory definitions
│   ├── GrainInference.lean    # Grain inference rules
│   └── README.md              # Detailed verification guide
│
├── type-system-encodings/     # Cross-language grain encodings
│   ├── python/                # Python/mypy implementation
│   │   ├── grained_dataframe.py
│   │   ├── requirements.txt
│   │   └── README.md
│   ├── lean4/                 # Lean 4 implementation
│   │   ├── GrainDefinitions.lean
│   │   ├── GrainedData.lean
│   │   └── README.md
│   └── agda/                  # Agda implementation
│       ├── GrainDefinitions.agda
│       ├── GrainedData.agda
│       └── README.md
│
└── sql-validation/            # Experimental validation
    ├── dbscripts/
    │   ├── 00_setup.sql       # Database schema setup
    │   ├── 01_main_theorem_examples.sql
    │   ├── 02_equal_grains.sql
    │   ├── 03_ordered_grains.sql
    │   ├── 04_incomparable_grains.sql
    │   ├── 05_natural_join.sql
    │   └── additional_examples/
    ├── EXPERIMENT_RESULTS.md  # Validation results
    └── README.md
```

## Quick Start

### 1. Lean 4 Formal Verification

Demonstrates machine-checkable formal proofs of the three pipeline alternatives from the illustrative example in the paper (Section 3).

**Prerequisites:**
- Lean 4 (version specified in `lean-toolchain`)
- Lake (Lean build tool, included with Lean 4)

**Instructions:**
```bash
cd lean4-formalization
lake build  # Builds all Lean files and verifies proofs

# To check individual pipelines:
lean Pipeline1.lean  # ✓ Type-checks (correct pipeline)
lean Pipeline2.lean  # ✗ Type error (fan trap detected)
lean Pipeline3.lean  # ✗ Type error (grain mismatch detected)
```

**What to observe:**
- `Pipeline1.lean` type-checks successfully, proving correctness
- `Pipeline2.lean` produces a type error at the aggregation step, detecting the fan trap
- `Pipeline3.lean` produces a type error at the final step, detecting the grain mismatch

See `lean4-formalization/README.md` for detailed explanation of the verification methodology.

### 2. Type System Encodings

Demonstrates grain encoding across type systems with varying expressiveness.

#### Python/mypy (Gradual Typing)

```bash
cd type-system-encodings/python
pip install -r requirements.txt
mypy grained_dataframe.py  # Type-check grain-encoded transformations
python grained_dataframe.py  # Run examples with runtime validation
```

#### Lean 4 (Dependent Types)

```bash
cd type-system-encodings/lean4
lake build
```

#### Agda (Dependent Types)

```bash
cd type-system-encodings/agda
agda GrainDefinitions.agda  # Verify grain definitions
agda GrainedData.agda       # Verify grain-aware data structures
```

### 3. SQL Validation Experiments

100 PostgreSQL examples validating the grain inference formulas across all cases.

**Prerequisites:**
- PostgreSQL 12 or later

**Instructions:**
```bash
cd sql-validation/dbscripts

# Run all validation examples (100 total)
psql -U your_username -d your_database -f run_all.sql

# Or run individual test suites:
psql -U your_username -d your_database -f 00_setup.sql
psql -U your_username -d your_database -f 01_main_theorem_examples.sql
psql -U your_username -d your_database -f 02_equal_grains.sql
# ... etc
```

**Expected results:** All queries execute successfully, with output demonstrating the grain inference formulas correctly predict join result grains. See `sql-validation/EXPERIMENT_RESULTS.md` for detailed analysis.

## Key Contributions Demonstrated

### 1. Compile-Time Verification (Lean 4 Formalization)

The Lean 4 formalization demonstrates that:
- **Correct pipelines type-check automatically** - No manual proof writing required
- **Incorrect pipelines produce type errors** - Fan traps and grain mismatches detected at compile-time
- **Proofs are machine-checkable** - Independent verification by Lean's proof checker

This proves that grain theory enables zero-cost verification: all checking happens at compile-time through type analysis alone.

### 2. Cross-Language Applicability (Type System Encodings)

Three implementations demonstrate grain encoding across different type system paradigms:

- **Python/mypy**: Practical gradual typing with protocols and generics
  - `GrainedDataFrame[G]` provides compile-time grain checking via mypy
  - Runtime validation ensures correctness even in untyped code
  - Integrates with production data frameworks (PySpark, pandas)

- **Lean 4**: Full dependent types with automatic grain inference
  - Type classes enable automatic grain computation
  - Proof-carrying types provide mathematical certainty
  - Demonstrates theoretical foundations

- **Agda**: Alternative dependent type implementation
  - Record-based type classes
  - Demonstrates cross-language equivalence of grain concepts

### 3. Empirical Validation (SQL Experiments)

100 PostgreSQL examples covering all grain inference formula cases:
- **15 examples**: Main theorem (comparable and incomparable grain portions)
- **20 examples**: Equal grains (one-to-one relationships)
- **20 examples**: Ordered grains (one-to-many relationships)
- **20 examples**: Incomparable grains (many-to-many relationships)
- **25 examples**: Natural joins (special cases)
- **85 additional examples**: Extended coverage

All examples validate that the grain inference formulas correctly predict join result grains.

## Paper Reference

When using these artifacts, please cite:

```bibtex
@article{karayannidis2025grain,
  author    = {Nikos Karayannidis},
  title     = {Grain-Aware Data Transformations: Type-Level Formal Verification
               at Zero Computational Cost},
  journal   = {Proceedings of the VLDB Endowment},
  volume    = {19},
  year      = {2026}
}
```

## License

This work is licensed under the MIT License. See `LICENSE` file for details.

## Contact

For questions or issues regarding these artifacts:
- **Email**: nkarag@gmail.com
- **GitHub Issues**: Please open an issue in this repository

## Reproducibility Notes

### Environment Tested

- **Lean 4**: Version specified in `lean-toolchain` files (leanprover/lean4:v4.13.0)
- **Python**: 3.9+
- **mypy**: 1.0+
- **Agda**: 2.6.3
- **PostgreSQL**: 12+

### Expected Runtime

- **Lean 4 verification**: ~30 seconds (all proofs)
- **Python type checking**: ~5 seconds
- **SQL validation**: ~2 minutes (all 100 examples)

### Known Issues

None currently. If you encounter issues:
1. Check that you're using the specified tool versions
2. Ensure all dependencies are installed
3. Open an issue with error details and environment information

## Acknowledgments

This work was developed to demonstrate that formal verification can be practical and accessible for data engineers, not just theorem-proving experts. The Lean 4 formalization proves that grain theory enables machine-checkable correctness guarantees at zero computational cost.
