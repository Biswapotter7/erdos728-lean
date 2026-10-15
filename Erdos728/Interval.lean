import Erdos728.Upstream.Erdos728b

/-!
The interval valuation estimate, extracted from the proof of the upstream
`lemma_small_primes_good` and generalized from `k_val c M` to arbitrary k.
The upstream file is preserved unchanged. See README.md for attribution.
-/

namespace Erdos728

open Erdos728b
open scoped Nat

set_option maxHeartbeats 0 in
/-- Lemma 4: valuation of a consecutive block is bounded by that of k! plus its peak. -/
theorem interval_valuation_bound (p m k : ℕ) (hp : p.Prime) :
    W p m k ≤ padicValNat p (k !) + V_p p m k := by
  have h_w_le_kappa : W p m k ≤ ∑ j ∈ Finset.Icc 1 (V_p p m k), N_pj p m k j := by
    rw [ ← lemma_W_eq_sum_N_pj p m k hp ];
  have h_w_le_kappa : ∑ j ∈ Finset.Icc 1 (V_p p m k), N_pj p m k j ≤ ∑ j ∈ Finset.Icc 1 (V_p p m k), Nat.ceil ((k : ℝ) / (p ^ j : ℝ)) := by
    exact Finset.sum_le_sum fun j hj => lemma_N_pj_le_ceil p m k j hp;
  have h_w_le_kappa : ∑ j ∈ Finset.Icc 1 (V_p p m k), Nat.ceil ((k : ℝ) / (p ^ j : ℝ)) ≤ ∑ j ∈ Finset.Icc 1 (V_p p m k), (Nat.floor ((k : ℝ) / (p ^ j : ℝ)) + 1) := by
    exact Finset.sum_le_sum fun _ _ => Nat.ceil_le_floor_add_one _;
  have h_w_le_kappa : ∑ j ∈ Finset.Icc 1 (V_p p m k), Nat.floor ((k : ℝ) / (p ^ j : ℝ)) ≤ padicValNat p (Nat.factorial k) := by
    have h_w_le_kappa : padicValNat p (Nat.factorial k) = ∑ j ∈ Finset.Icc 1 (Nat.log p k), (k / p ^ j) := by
      haveI := Fact.mk hp; rw [ padicValNat_factorial ] ; aesop;
      norm_num;
    rw [h_w_le_kappa];
    by_cases hV : V_p p m k ≤ Nat.log p k;
    · refine' le_trans ( Finset.sum_le_sum_of_subset ( Finset.Icc_subset_Icc_right hV ) ) _;
      exact Finset.sum_le_sum fun _ _ => Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod k ( p ^ ‹_› ), Nat.mod_lt k ( pow_pos hp.pos ‹_› ), pow_pos hp.pos ‹_› ] ;
    · rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( le_of_not_ge hV ) ) ];
      · exact Finset.sum_le_sum fun _ _ => Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod k ( p ^ ‹_› ), Nat.mod_lt k ( pow_pos hp.pos ‹_› ), pow_pos hp.pos ‹_› ] ;
      · simp +zetaDelta at *;
        intro x hx₁ hx₂ hx₃; rw [ div_lt_one ( pow_pos ( Nat.cast_pos.mpr hp.pos ) _ ) ] ; exact_mod_cast Nat.lt_pow_of_log_lt hp.one_lt ( hx₃ hx₁ ) ;
  simp_all +decide [ Finset.sum_add_distrib ];
  grind;

end Erdos728
