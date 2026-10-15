# Erdős Problem 728 in Lean

A reproducible Lean project for the logarithmic-window formulation of
[Erdős Problem 728](https://www.erdosproblems.com/728).

For every real `0 < C₁ < C₂` and `0 < ε < 1/2`, the main theorem proves that
infinitely many triples `(a, b, n) : ℕ × ℕ × ℕ` satisfy

```text
ε n ≤ a, b ≤ (1 − ε) n
a! b! ∣ n! (a + b − n)!
C₁ log n < a + b − n < C₂ log n.
```

The declaration is `Erdos728.erdos_728` in `Erdos728/Main.lean`. The logarithm
is the natural logarithm. Factorials and subtraction are on natural numbers;
inequalities involving logarithms are on real numbers with explicit coercions.

**Verified locally and on GitHub Actions:** the complete build, all eight axiom
audits, and 3,321 arithmetic checks passed with Lean 4.24.0. The
[first successful CI run](https://github.com/Biswapotter7/erdos728-lean/actions/runs/38721976399)
checked proof commit `d793e39`. See [VERIFICATION.txt](VERIFICATION.txt) for
local compiler output, the theorem type, and source checksums. The project
Lean sources contain no `sorry`, `admit`, or `native_decide`.

## Run it

Requirements: Linux/macOS, Git, curl, Python 3, and sufficient disk space for
Lean and Mathlib. The first setup downloads several gigabytes. No Python
packages are needed.

```bash
bash scripts/bootstrap.sh
bash scripts/verify.sh
```

The bootstrap installs elan locally under `.tools/elan` if no elan is available.
It does not change your shell profile. Existing elan installations are also
supported. `scripts/lake.sh` selects the project-local installation when present.

To run the individual Lean commands:

```bash
bash scripts/lake.sh build
bash scripts/lake.sh env lean Audit.lean
```

The project pins **Lean 4.24.0** and Mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The complete dependency lockfile is
committed. Keep the toolchain, Mathlib revision, and lockfile synchronized when
upgrading; then rerun the verification script.

## What is proved here

- `exists_windowTriple_above` constructs a witness beyond every prescribed `N`,
  simultaneously satisfying both logarithmic bounds and the range constraints.
- `erdos_728` converts these unbounded witnesses into the exact set infinitude
  statement from the project plan.
- `factorial_dvd_iff_choose_dvd` proves the factorial/binomial equivalence for
  all natural `m` and `k`, including zero.
- `valuation_reduction` exposes the prime valuation equivalence.
- `interval_valuation_bound` exposes the interval estimate for arbitrary `k`
  in its own file, extracted from the upstream small-prime argument.
- `window_n_gt_one`, `window_gap_pos`, and `window_nontrivial` prove that every
  window witness has `n > 1`, `a + b > n`, and `a, b < n`. Thus natural
  subtraction is not silently truncating the gap, and `a = b = n` is excluded.
- The example `(a,b,n) = (21,14,28)` is checked by kernel reduction in Lean.

`scripts/verify.sh` compiles the project, scans all project Lean files for
proof placeholders and bypasses, runs `#print axioms`, and rejects any axiom
outside `propext`, `Classical.choice`, and `Quot.sound`. It also performs 3,321
exact-integer Python checks of the algebraic reduction. The numerical checks
are supplementary; they do not establish the infinitude theorem.

Generated version, build, axiom, and arithmetic logs go into `artifacts/`.
`.github/workflows/lean.yml` runs the same verification on every push and pull
request and supports manual runs. Each run uploads its logs as the
`lean-verification` artifact. View the
[verification runs](https://github.com/Biswapotter7/erdos728-lean/actions/workflows/lean.yml)
for the current GitHub status.

## Provenance and proof structure

This project reuses the published proof; it does not claim a new solution to
the Erdős problem. The hard valuation, carry, counting, and asymptotic arguments
are preserved byte-for-byte in `Erdos728/Upstream/Erdos728b.lean`, from
[Boris Alexeev's lean-proofs repository](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.24.0/ErdosProblems/Erdos728b.lean).
The new assembly proves the exact two-sided infinite-family statement, which
is stronger than either of the two final theorem statements in that file
taken individually. The interval proof is an extracted generalization; the
upstream original remains unchanged.

The proof and its origins are described in Nat Sothanaphan's
[writeup, arXiv:2601.07421v5](https://arxiv.org/html/2601.07421v5).
Credit for the original development belongs to its authors and contributors,
including Kevin Barreto, Boris Alexeev, GPT-5.2 Pro, and Aristotle, as described
in that writeup. No repository-level license was present in the checked
upstream repository; this project does not assign a new license to that code.

The paper's lemmas can be located as follows (upstream names have namespace
`Erdos728b`):

1. Binomial reformulation: `Erdos728.factorial_dvd_iff_choose_dvd`.
2. Valuation reduction: `lemma_val_reduction`.
3. Kummer: Mathlib's `padicValNat_choose`.
4. Interval bound: `Erdos728.interval_valuation_bound`;
   underlying results `lemma_W_eq_sum_N_pj`, `lemma_N_pj_le_ceil`.
5. Large primes: `lemma_p_gt_2k`, `lemma_forced_carries_largep`.
6. Forced carries: `lemma_forced_carries_smallp`.
7. Uniform threshold: `lemma_threshold_weak_uniform`.
8. Residue counting: `lemma_residue_interval`.
9. Uniformity: `lemma_mod_uniform`, `lemma_Q_p_bound`.
10. Chernoff bound: `lemma_chernoff_inequality`, `lemma_chernoff_binomial`.
11. Carry failures: `lemma_bad_carries_bound`, `lemma_sum_bad_carries_small`.
12. Spike failures: `lemma_spike_count_bound`, `lemma_sum_bad_spikes_le_bound`.
13. Total bad-set estimate: inside `lemma_good_m_exists_any_c`.
14. Good integer existence: `lemma_good_m_exists_any_c`.

The source uses a slightly different sufficient threshold formulation and
includes the boundary in its bad-carry set; these are the actual checked
statements, not literal restatements of every displayed formula in the paper.

## Comparison with Formal Conjectures

The [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/728.lean)
asks for existence for sufficiently small positive `ε`, with strict lower
range bounds and a logarithmic window expressed as real sums. The imported,
proved `Erdos728b.erdos_728_fc` has that statement and is included in the axiom
audit. Our main theorem additionally establishes infinitude, works for every
`0 < ε < 1/2`, and records both upper range bounds. The formal-conjectures file
is a statement reference only and is not imported into the proof.

## Source pin

- Upstream repository: `https://github.com/plby/lean-proofs`
- Upstream commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`
- Upstream path: `src/v4.24.0/ErdosProblems/Erdos728b.lean`
- Source SHA-256: `40f4cbf2ccaefa5d84fc44ece63d1e4c3fed3e47b631057ef337fc92465d7b9f`

Toolchains, caches, build outputs, and local logs are excluded from Git.
