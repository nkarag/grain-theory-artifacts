"""
Smoke tests for Mode D (declared dependencies inside and across the inputs).

    pytest test_mode_d.py -v

Pure-Python checks of the reduction run without PostgreSQL; the SQL-backed
check uses the ``db`` fixture of conftest.py.
"""

import pytest
from hypothesis import given, settings

from config import make_config
from fd_config import (DeclaredFD, admissible_fds, all_fd_configs, closure,
                       make_fd_config, reduce_candidate)
from generators import all_configs_up_to
from properties_fd import run_all_fd_properties
from run_mode_d import fd_config_strategy


def test_paper_example_store_season_discount():
    """The example of the paper's reduction subsection: {StoreId, Season} -> Discount."""
    cfg = make_config(
        r1_fields=["StoreId", "RegionId"], r2_fields=["RegionId", "Season", "Discount"],
        jk=["RegionId"], g1=["StoreId", "RegionId"], g2=["RegionId", "Season", "Discount"])
    assert set(cfg.convention_grain) == {"RegionId", "StoreId", "Season", "Discount"}
    fd = DeclaredFD(lhs=("StoreId", "Season"), rhs="Discount", kind="cross", target_input=2)
    fdc = make_fd_config(cfg, fd)
    assert set(fdc.reduced) == {"RegionId", "StoreId", "Season"}
    assert fdc.removed == ("Discount",)
    assert any(set(a.lhs) == set(fd.lhs) and a.rhs == fd.rhs and a.kind == fd.kind
               for a in admissible_fds(cfg))


def test_reduction_is_fixpoint_and_key_symbolically():
    """Every admissible pair up to size 3: the reduction determines the candidate
    and no further attribute is extraneous."""
    for fdc in all_fd_configs(all_configs_up_to(3)):
        from fd_config import base_fds
        fds = base_fds(fdc.config) + [(frozenset(fdc.fd.lhs), frozenset([fdc.fd.rhs]))]
        assert set(fdc.candidate) <= closure(fdc.reduced, fds)
        again, removed = reduce_candidate(fdc.reduced, fds)
        assert again == fdc.reduced and removed == ()
        assert fdc.fd.rhs in fdc.removed


@given(fdc=fd_config_strategy(max_jk=4, max_r_only=3))
@settings(max_examples=50, deadline=None, database=None)
def test_random_fd_config_wellformed(fdc):
    assert set(fdc.fd.lhs) <= set(fdc.candidate) - {fdc.fd.rhs}
    assert fdc.fd.rhs in fdc.candidate and fdc.fd.rhs not in fdc.reduced


@pytest.mark.parametrize("n", [1, 2, 3])
def test_properties_on_small_configs(db, n):
    """D1-D6 on the first few admissible pairs, against PostgreSQL."""
    conn = db
    pairs = list(all_fd_configs(all_configs_up_to(3)))
    step = max(1, len(pairs) // 10)
    for i, fdc in enumerate(pairs[::step]):
        results = run_all_fd_properties(conn, fdc, n_rows=20, seed=n, config_id=i + 1)
        for prop, (ok, msg) in results.items():
            assert ok, f"{prop}: {msg}"
