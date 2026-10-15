"""Validate the actual #print axioms output, not comments in source files."""
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text()
expected = {
    "Erdos728.erdos_728", "Erdos728.exists_windowTriple_above",
    "Erdos728.window_n_gt_one", "Erdos728.window_gap_pos",
    "Erdos728.window_nontrivial", "Erdos728b.erdos_728_fc",
    "Erdos728.factorial_dvd_iff_choose_dvd", "Erdos728.interval_valuation_bound",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
seen = set()
for name, raw in reports:
    axioms = {x.strip() for x in raw.split(",") if x.strip()}
    if axioms - allowed:
        raise SystemExit(f"Unexpected axioms for {name}: {axioms - allowed}")
    seen.add(name)
if expected - seen:
    raise SystemExit(f"Missing axiom reports: {expected - seen}")
print(f"Axiom audit passed: {len(expected)} declarations use only standard Lean axioms.")
