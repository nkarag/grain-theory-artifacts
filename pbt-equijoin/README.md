# Equi-Join Grain Inference — Property-Based Testing

Property-based testing suite for the corrected equi-join grain inference theorem:

$$G[\text{Res}] \equiv_g G[R_1] \cup_{typ} (G[R_2] -_{typ} J_k)$$

with naming convention: $R_1$ denotes the input with $G_1^{J_k} \subseteq_{typ} G_2^{J_k}$ when comparable.

## Prerequisites

- Python 3.10+
- PostgreSQL running locally (database `postgres`)
- pip

## Setup

```bash
pip install -r requirements.txt
```

## Running tests

```bash
# Smoke test (100 random configs)
pytest test_equijoin_grain.py -v

# Mode A: exhaustive small-model checking
pytest test_equijoin_grain.py -v -k mode_a

# Mode B: random PBT (10,000 examples)
pytest test_equijoin_grain.py -v -k mode_b

# Mode C: targeted edge cases
pytest test_equijoin_grain.py -v -k mode_c

# All modes
pytest test_equijoin_grain.py -v

# Mode D: declared FDs inside and across the inputs (the second hypothesis
# of the theorem violated on purpose; the reduction of prop:grain-reduction-fd checked)
python run_mode_d.py --max-type-size 4 --random-examples 5000 --n-rows 30
pytest test_mode_d.py -v
```

## Structure

| File | Description |
|------|-------------|
| `config.py` | `Config` dataclass, `JkRelation` enum, `make_config()` |
| `generators.py` | Hypothesis `@st.composite` strategies (TASK 03) |
| `data_gen.py` | FD-respecting data generation (TASK 04) |
| `sql_runner.py` | PostgreSQL helpers: table creation, join, uniqueness/minimality checks |
| `conftest.py` | Pytest fixtures (PostgreSQL connection, schema lifecycle) |
| `test_equijoin_grain.py` | Property assertions and test modes |
| `fd_config.py` | Declared dependency on top of a config; admissibility; the closure reduction (mode D) |
| `data_gen_fd.py` | Data generation that enforces the declared dependency (mode D) |
| `properties_fd.py` | Properties D1–D6 (mode D) |
| `run_mode_d.py`, `test_mode_d.py` | Mode D runner and smoke tests |

## Properties tested

1. **Uniqueness (both directions):** F1 and F2 both produce unique identifiers
2. **Minimality (convention):** Convention-compliant grain is irreducible
3. **Wrong direction non-minimal:** Comparable + non-equal Jk-portions -> wrong direction is NOT minimal
4. **Incomparable both minimal:** Both directions minimal when Jk-portions are incomparable
5. **Size relationship:** |F1| - |F2| = |G1^Jk| - |G2^Jk|
6. **Convention is smallest:** |convention_grain| <= min(|F1|, |F2|)

Mode D (declared dependencies, `PBT_RESULTS.md` Section 7b): with a further FD U -> v declared inside or across the inputs, the theorem's candidate is a superkey (D2) but reducible (D3), and the closure reduction of the paper's grain-reduction proposition is a key (D4), minimal where the data allows the check (D6).

## Reference

- `BULLETPROOF_EQUIJOIN_PLAN.md` — Full verification plan
- `THEORY_GAP_CASE_B_v2.md` — Theory gap analysis and corrected proof
