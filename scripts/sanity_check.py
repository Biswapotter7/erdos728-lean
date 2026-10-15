"""Finite arithmetic checks only; infinitude is established by the Lean theorem."""
from math import comb, factorial

checks = 0
for m in range(81):
    for k in range(41):
        lhs = factorial(m + k) * factorial(m)
        rhs = factorial(2 * m) * factorial(k)
        assert (rhs % lhs == 0) == (comb(2 * m, m) % comb(m + k, k) == 0)
        assert (m + k) + m - 2 * m == k
        checks += 1
assert comb(28, 14) % comb(21, 7) == 0
print(f"Passed {checks} exact-integer checks of the factorial/binomial equivalence.")
print(f"Example: choose(28,14) / choose(21,7) = {comb(28, 14) // comb(21, 7)}.")
