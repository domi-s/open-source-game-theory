from __future__ import annotations

import json
import math
from collections import Counter

import pytest

from distillation.fidelity import (check_same_model, compare, confidence_radius, format_report,
                                   load_revealed, load_stated)


def stated(c=0, d=0, open=0):
    return Counter(C=c, D=d, open=open)


def revealed(c=0, d=0):
    return Counter(C=c, D=d)


def test_all_programs_proved_gives_their_c_rate():
    result = compare({"A": stated(c=3, d=1)}, {"A": revealed(c=5, d=5)})
    assert result.states == {"A": 0.75}
    assert result.eps == pytest.approx(0.25)


def test_open_programs_are_left_out_of_the_rate():
    result = compare({"A": stated(c=1, d=1, open=6)}, {"A": revealed(c=10)})
    assert (result.states["A"], result.proved["A"]) == (0.5, 2)
    assert result.eps == pytest.approx(0.5)


def test_an_opponent_with_no_proved_program_is_open_and_not_averaged():
    result = compare({"A": stated(open=4), "B": stated(d=4)},
                     {"A": revealed(c=10), "B": revealed(c=5, d=5)})
    assert result.states == {"A": None, "B": 0.0}
    assert result.eps == pytest.approx(0.5)


def test_eps_is_open_when_no_opponent_has_a_proved_program():
    result = compare({"A": stated(open=4)}, {"A": revealed(c=10)})
    assert result.eps is None and result.confident is None


def test_opponents_without_replies_are_skipped():
    result = compare({"A": stated(c=4), "B": stated(c=4)}, {"A": revealed(d=10), "B": revealed()})
    assert list(result.plays) == ["A"]


def test_compare_needs_a_shared_opponent():
    with pytest.raises(ValueError):
        compare({"A": stated(c=1)}, {"B": revealed(c=1)})


def test_radius_matches_the_hand_computed_value_when_everything_is_proved():
    expected = math.sqrt((1 / 20 + 9 / (81 * 20)) * math.log(40) / 2)
    assert confidence_radius(20, [20] * 9, [20] * 9, 0.05) == pytest.approx(expected)


def test_radius_grows_when_fewer_programs_are_proved():
    assert confidence_radius(20, [5] * 9, [20] * 9, 0.05) > confidence_radius(20, [20] * 9, [20] * 9, 0.05)


def test_confidence_interval_is_clamped_to_0_1():
    assert compare({"A": stated(c=1)}, {"A": revealed(c=1)}).confident == (0.0, 1.0)


def test_loaders_read_saved_runs(tmp_path):
    (tmp_path / "bots.json").write_text(json.dumps([
        {"valid": True, "count": 3, "cells": [
            {"opponent": "A", "verdict": "stable", "my_action": "C"},
            {"opponent": "B", "verdict": "undetermined", "my_action": None}]},
        {"valid": True, "cells": [
            {"opponent": "A", "verdict": "stable", "my_action": "D"},
            {"opponent": "B", "verdict": "stable", "my_action": "D"}]},
        {"valid": False, "cells": []},
    ]))
    (tmp_path / "raw_responses.json").write_text(json.dumps(
        {"A": [{"action": "C"}, {"action": None}, {"action": "D"}]}))

    assert load_stated(tmp_path) == {"A": stated(c=3, d=1), "B": stated(d=1, open=3)}
    assert load_revealed(tmp_path) == {"A": revealed(c=1, d=1)}


def test_different_models_are_refused(tmp_path):
    for name, model in (("s", "m1"), ("r", "m2")):
        (tmp_path / name).mkdir()
        (tmp_path / name / "metadata.json").write_text(json.dumps({"model": model}))
    with pytest.raises(ValueError):
        check_same_model(tmp_path / "s", tmp_path / "r")


def test_report_marks_open_opponents_and_counts_proved_programs():
    report = format_report("m", compare({"A": stated(open=4), "B": stated(c=1, d=1, open=2)},
                                        {"A": revealed(c=10), "B": revealed(c=10)}))
    a_row = next(line for line in report.splitlines() if line.startswith("A "))
    assert a_row.split()[2:] == ["open", "open", "0/4"]
    assert "2/4" in report and "over 1 of 2 opponents" in report
