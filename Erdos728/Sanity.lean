import Erdos728.Main

open scoped Nat

namespace Erdos728

/-- The substitution has exactly gap k; natural subtraction does not truncate it. -/
theorem construction_gap (m k : ℕ) : (m + k) + m - 2 * m = k := by omega

/-- Every window witness has n > 1, so log n is strictly positive. -/
theorem window_n_gt_one {C₁ C₂ ε : ℝ} (h₂ : 0 < C₂)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ WindowTriples C₁ C₂ ε) : 1 < t.2.2 := by
  have hupper := ht.2.2.2.2.2.2
  have hnonneg : (0 : ℝ) ≤ ((t.1 + t.2.1 - t.2.2 : ℕ) : ℝ) := by positivity
  have hlog : 0 < Real.log (t.2.2 : ℝ) := by nlinarith
  have hn : t.2.2 ≠ 0 := by intro h; simp [h] at hlog
  have hn' : t.2.2 ≠ 1 := by intro h; simp [h] at hlog
  omega

/-- In particular, the natural-number gap is positive, not truncated to zero. -/
theorem window_gap_pos {C₁ C₂ ε : ℝ} (h₁ : 0 < C₁) (h₂ : 0 < C₂)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ WindowTriples C₁ C₂ ε) :
    t.2.2 < t.1 + t.2.1 := by
  have hn := window_n_gt_one h₂ ht
  have hlog : 0 < Real.log (t.2.2 : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hgap : (0 : ℝ) < ((t.1 + t.2.1 - t.2.2 : ℕ) : ℝ) :=
    lt_trans (mul_pos h₁ hlog) ht.2.2.2.2.2.1
  have : 0 < t.1 + t.2.1 - t.2.2 := by exact_mod_cast hgap
  omega

/-- The upper range constraints exclude a = n and b = n. -/
theorem window_nontrivial {C₁ C₂ ε : ℝ} (h₂ : 0 < C₂) (hε : 0 < ε)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ WindowTriples C₁ C₂ ε) :
    t.1 < t.2.2 ∧ t.2.1 < t.2.2 := by
  have hn := window_n_gt_one h₂ ht
  have hnpos : (0 : ℝ) < t.2.2 := by exact_mod_cast (show 0 < t.2.2 by omega)
  have ha := ht.2.2.1
  have hb := ht.2.2.2.1
  have ha' : (t.1 : ℝ) < t.2.2 := by nlinarith [mul_pos hε hnpos]
  have hb' : (t.2.1 : ℝ) < t.2.2 := by nlinarith [mul_pos hε hnpos]
  exact ⟨by exact_mod_cast ha', by exact_mod_cast hb'⟩

/-- The concrete example from the plan, checked by Lean's kernel. -/
example : Nat.choose (14 + 7) 7 ∣ Nat.choose (2 * 14) 14 := by decide
example : 21 ! * 14 ! ∣ 28 ! * (21 + 14 - 28)! := by decide

end Erdos728
