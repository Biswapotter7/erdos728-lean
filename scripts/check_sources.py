"""Reject proof placeholders and kernel-bypassing declarations in project sources."""
from pathlib import Path
from hashlib import sha256
import re

upstream = Path("Erdos728/Upstream/Erdos728b.lean")
expected = "40f4cbf2ccaefa5d84fc44ece63d1e4c3fed3e47b631057ef337fc92465d7b9f"
if sha256(upstream.read_bytes()).hexdigest() != expected:
    raise SystemExit("Upstream proof differs from the documented source pin")

paths = sorted(Path("Erdos728").rglob("*.lean")) + [Path("Erdos728.lean"), Path("Audit.lean")]
for path in paths:
    text = path.read_text()
    # Deliberately conservative: even a forbidden token in a comment fails.
    match = re.search(r"\b(sorry|admit|sorryAx|native_decide|axiom)\b", text)
    if match:
        raise SystemExit(f"Forbidden token {match[0]!r} in {path}")
print(f"Source audit passed: {len(paths)} Lean files, no forbidden tokens.")
