"""
Declared functional dependencies on top of an equi-join configuration (Mode D).

The equi-join theorem (arXiv v4 `thm:equijoin-grain`) assumes two things of the
declaration set: the inputs are independent outside the join key, and no
declared determination other than the two input grains acts among the
candidate's fields. When a schema declares a further functional dependency
U -> v whose determinant is not a whole input grain, the candidate
K = G[R1] u (G[R2] \\ Jk) is still a superkey of the result but need not be
irreducible; `prop:grain-reduction-fd` says the grain is obtained from K by
deleting every attribute determined, through the closure of the declared
dependencies, by the remaining ones, iterated to a fixpoint.

This module represents such a declared dependency, decides whether it is
admissible for a configuration (it must not contradict the premise that each
input grain is a grain of its input), and computes the reduction.

Field names are the base names of the configuration (``j0``, ``a1``, ``b2``);
the result-table suffixes are added by ``sql_runner._resolve_grain_cols``.
"""

from dataclasses import dataclass
from itertools import combinations
from typing import FrozenSet, Iterator, List, Sequence, Tuple

from config import Config


@dataclass(frozen=True)
class DeclaredFD:
    """A declared functional dependency ``lhs -> rhs`` over the inputs' fields.

    ``kind`` is ``"within"`` when every field of ``lhs`` and ``rhs`` belongs to
    one input, and ``"cross"`` when the determinant spans both inputs (the
    paper's ``{StoreId, Season} -> Discount``).
    """
    lhs: Tuple[str, ...]
    rhs: str
    kind: str  # "within" | "cross"
    target_input: int  # 1 or 2: the input that holds ``rhs``


@dataclass(frozen=True)
class FDConfig:
    """An equi-join configuration together with one declared dependency.

    ``candidate`` is the type the theorem returns (the convention grain);
    ``reduced`` is its reduction under the declared dependencies, the grain
    `prop:grain-reduction-fd` asserts; ``removed`` is what the reduction
    deleted.
    """
    config: Config
    fd: DeclaredFD
    candidate: Tuple[str, ...]
    reduced: Tuple[str, ...]
    removed: Tuple[str, ...]


# ---------------------------------------------------------------------------
# Attribute closure and the reduction of prop:grain-reduction-fd
# ---------------------------------------------------------------------------

def base_fds(config: Config) -> List[Tuple[FrozenSet[str], FrozenSet[str]]]:
    """The dependencies the theorem itself assumes: each grain determines its input."""
    return [
        (frozenset(config.g1), frozenset(config.r1_fields)),
        (frozenset(config.g2), frozenset(config.r2_fields)),
    ]


def closure(attrs: Sequence[str],
            fds: Sequence[Tuple[FrozenSet[str], FrozenSet[str]]]) -> FrozenSet[str]:
    """Standard attribute closure of ``attrs`` under ``fds``."""
    result = set(attrs)
    changed = True
    while changed:
        changed = False
        for lhs, rhs in fds:
            if lhs <= result and not rhs <= result:
                result |= rhs
                changed = True
    return frozenset(result)


def reduce_candidate(candidate: Sequence[str],
                     fds: Sequence[Tuple[FrozenSet[str], FrozenSet[str]]]
                     ) -> Tuple[Tuple[str, ...], Tuple[str, ...]]:
    """The reduction of `prop:grain-reduction-fd`.

    Deletes any attribute determined by the remaining attributes through the
    closure, iterated to a fixpoint, in a fixed order (the candidate's order),
    so the result is reproducible. Returns ``(reduced, removed)``.
    """
    current = list(candidate)
    removed: List[str] = []
    changed = True
    while changed:
        changed = False
        for a in list(current):
            rest = [x for x in current if x != a]
            if a in closure(rest, fds):
                current = rest
                removed.append(a)
                changed = True
                break
    return tuple(current), tuple(removed)


# ---------------------------------------------------------------------------
# Admissible declared dependencies for a configuration
# ---------------------------------------------------------------------------

def _input_of(config: Config, field: str) -> int:
    """1 if the field is R1-only, 2 if R2-only, 0 if a join-key field."""
    if field in config.jk:
        return 0
    if field in config.r1_fields:
        return 1
    return 2


def admissible_fds(config: Config, max_lhs: int = 3) -> Iterator[DeclaredFD]:
    """Enumerate the declared dependencies Mode D tests for ``config``.

    The target ``v`` is a non-join-key grain field of one input, so that it
    sits in the candidate and the dependency can make the candidate
    reducible. The determinant is a nonempty set of other candidate fields,
    of size at most ``max_lhs``, subject to two conditions that keep the
    dependency consistent with the theorem's premises:

    * it is not a subset of the target's own grain (a grain is irreducible
      by definition, so no part of it determines another part), and
    * when it spans both inputs (``cross``), its R1-side fields are grain
      fields of R1 outside the join key, so that the data generator can
      realize the dependency through the join key (see ``data_gen_fd``).

    A dependency whose fields all lie in the target's input is ``within``;
    its determinant must then contain a join-key field that is not in the
    target's grain (the only candidate fields of that input outside the
    grain), which is the shape of the paper's example read inside one
    input.
    """
    cand = list(config.convention_grain)
    cand_set = set(cand)
    for v in cand:
        tin = _input_of(config, v)
        if tin == 0:
            continue  # join-key fields are shared; the target must be one input's own
        own_fields = set(config.r1_fields if tin == 1 else config.r2_fields)
        own_grain = set(config.g1 if tin == 1 else config.g2)
        others = [x for x in cand if x != v]
        for k in range(1, min(max_lhs, len(others)) + 1):
            for lhs in combinations(others, k):
                lhs_set = set(lhs)
                if lhs_set <= own_grain:
                    continue  # would contradict irreducibility of the target's grain
                if lhs_set <= own_fields:
                    yield DeclaredFD(lhs=tuple(lhs), rhs=v, kind="within",
                                     target_input=tin)
                else:
                    # Cross: R1-side part must be R1-only grain fields; the
                    # target must be on the R2 side (the paper's shape).
                    if tin != 2:
                        continue
                    r1_side = [x for x in lhs if _input_of(config, x) == 1]
                    r2_side = [x for x in lhs if _input_of(config, x) != 1]
                    if not r1_side:
                        continue
                    if not set(r1_side) <= set(config.g1_rest):
                        continue
                    if set(r2_side) <= own_grain and not r1_side:
                        continue
                    yield DeclaredFD(lhs=tuple(lhs), rhs=v, kind="cross",
                                     target_input=2)


def make_fd_config(config: Config, fd: DeclaredFD) -> FDConfig:
    """Attach a declared dependency to a configuration and compute the reduction."""
    fds = base_fds(config) + [(frozenset(fd.lhs), frozenset([fd.rhs]))]
    candidate = tuple(config.convention_grain)
    reduced, removed = reduce_candidate(candidate, fds)
    return FDConfig(config=config, fd=fd, candidate=candidate,
                    reduced=reduced, removed=removed)


def all_fd_configs(configs: Iterator[Config], max_lhs: int = 3) -> Iterator[FDConfig]:
    """Every admissible (configuration, declared dependency) pair."""
    for config in configs:
        for fd in admissible_fds(config, max_lhs=max_lhs):
            yield make_fd_config(config, fd)
