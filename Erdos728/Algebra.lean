import Erdos728.Upstream.Erdos728b

open scoped Nat

namespace Erdos728

/-- Lemma 1: cancel the common nonzero product of three factorials. -/
theorem factorial_dvd_iff_choose_dvd (m k : ℕ) :
    (m + k)! * m ! ∣ (2 * m)! * k ! ↔
      Nat.choose (m + k) k ∣ Nat.choose (2 * m) m := by
  have hleft := Nat.choose_mul_factorial_mul_factorial (show k ≤ m + k by omega)
  have hright := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
  have hsub : 2 * m - m = m := by omega
  simp only [Nat.add_sub_cancel_right, hsub] at hleft hright
  have hl : (m + k)! * m ! = Nat.choose (m + k) k * (k ! * m ! * m !) := by
    rw [← hleft]
    ring
  have hr : (2 * m)! * k ! = Nat.choose (2 * m) m * (k ! * m ! * m !) := by
    rw [← hright]
    ring
  rw [hl, hr]
  exact Nat.mul_dvd_mul_iff_right (by positivity)

/-- Lemma 2: rewrite the binomial valuation using the consecutive product. -/
theorem valuation_reduction (p m k : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.choose (m + k) k) ≤ Erdos728b.kappa p m ↔
      Erdos728b.W p m k ≤ Erdos728b.kappa p m + padicValNat p (k !) := by
  exact Erdos728b.lemma_val_reduction p m k hp

end Erdos728
