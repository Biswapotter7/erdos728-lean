import Erdos728.Upstream.Erdos728b

/-!
The logarithmic window formulation of Erdős Problem 728.

The counting and valuation results are the published development in
`Upstream/Erdos728b.lean`. Here we assemble them with an arbitrary lower bound
on n, obtaining infinitude with BOTH sides of the logarithmic window.
-/

open scoped Nat

namespace Erdos728

/-- The exact nontrivial, two-sided statement requested in the project plan. -/
def WindowTriples (C₁ C₂ ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | ε * t.2.2 ≤ t.1 ∧ ε * t.2.2 ≤ t.2.1 ∧
    (t.1 : ℝ) ≤ (1 - ε) * t.2.2 ∧
    (t.2.1 : ℝ) ≤ (1 - ε) * t.2.2 ∧
    t.1 ! * t.2.1 ! ∣ t.2.2 ! * (t.1 + t.2.1 - t.2.2)! ∧
    C₁ * Real.log t.2.2 < ((t.1 + t.2.1 - t.2.2 : ℕ) : ℝ) ∧
    ((t.1 + t.2.1 - t.2.2 : ℕ) : ℝ) < C₂ * Real.log t.2.2}

/-- Witnesses exist beyond every prescribed n, with n at least 2. -/
theorem exists_windowTriple_above (C₁ C₂ ε : ℝ)
    (h₁ : 0 < C₁) (h₁₂ : C₁ < C₂)
    (hε : 0 < ε) (hε' : ε < 1 / 2) (N : ℕ) :
    ∃ t ∈ WindowTriples C₁ C₂ ε, N ≤ t.2.2 ∧ 2 ≤ t.2.2 := by
  let c : ℝ := (C₁ + C₂) / 2
  have hc₁ : C₁ < c := by dsimp [c]; linarith
  have hc₂ : c < C₂ := by dsimp [c]; linarith
  have hc : 0 < c := lt_trans h₁ hc₁
  have h₂ : 0 < C₂ := lt_trans h₁ h₁₂
  obtain ⟨M₁, hM₁⟩ := Erdos728b.lemma_k_val_lower_bound_eventually c C₁ hc₁
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
    (Erdos728b.lemma_k_val_lt_C'_log_pos c C₂ hc₂ h₂)
  obtain ⟨M₃, hM₃⟩ := Erdos728b.lemma_k_val_upper_bound_eventually c ε hε'
  obtain ⟨M₄, hM₄⟩ := Erdos728b.lemma_threshold_weak_uniform c hc
  obtain ⟨M₅, hM₅⟩ := Erdos728b.lemma_good_m_exists_any_c c hc
  let M := N + M₁ + M₂ + M₃ + M₄ + M₅ + 2
  have hMN : N ≤ M := by omega
  have hMpos : 2 ≤ M := by omega
  have hlow := hM₁ M (by omega : M₁ ≤ M)
  have hupp := hM₂ M (by omega : M₂ ≤ M)
  have hrange := hM₃ M (by omega : M₃ ≤ M)
  have hthreshold := hM₄ M (by omega : M₄ ≤ M)
  obtain ⟨m, hm⟩ := hM₅ M (by omega : M₅ ≤ M)
  obtain ⟨hm_mem, hm_good⟩ := Finset.mem_sdiff.mp hm
  obtain ⟨hm_lower, hm_upper⟩ := Finset.mem_Icc.mp hm_mem
  have ht := Erdos728b.lemma_good_triple_construction_final
    C₁ ε c M m h₁ hε hε' hthreshold hrange hlow hm_mem hm_good
  dsimp only at ht
  have hgap : m + Erdos728b.k_val c M + m - 2 * m = Erdos728b.k_val c M := by
    omega
  have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_le_log
    · have : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      positivity
    · exact_mod_cast (show 2 * M ≤ 2 * m by omega)
  refine ⟨(m + Erdos728b.k_val c M, m, 2 * m), ?_, by dsimp; omega, by dsimp; omega⟩
  change ε * (2 * m : ℕ) ≤ (m + Erdos728b.k_val c M : ℕ) ∧ _
  refine ⟨ht.1, ht.2.2.1, ht.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ?_, ?_⟩
  · rw [hgap]
    have h := ht.2.2.2.2.2
    push_cast at h ⊢
    linarith
  · rw [hgap]
    push_cast
    exact lt_of_lt_of_le hupp (mul_le_mul_of_nonneg_left hlog h₂.le)

/-- Infinitely many triples satisfy both logarithmic bounds and the range constraints. -/
theorem erdos_728 (C₁ C₂ ε : ℝ) (h₁ : 0 < C₁) (h₁₂ : C₁ < C₂)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    {t : ℕ × ℕ × ℕ | ε * t.2.2 ≤ t.1 ∧ ε * t.2.2 ≤ t.2.1 ∧
      (t.1 : ℝ) ≤ (1 - ε) * t.2.2 ∧ (t.2.1 : ℝ) ≤ (1 - ε) * t.2.2 ∧
      t.1 ! * t.2.1 ! ∣ t.2.2 ! * (t.1 + t.2.1 - t.2.2)! ∧
      C₁ * Real.log t.2.2 < ((t.1 + t.2.1 - t.2.2 : ℕ) : ℝ) ∧
      ((t.1 + t.2.1 - t.2.2 : ℕ) : ℝ) < C₂ * Real.log t.2.2}.Infinite := by
  apply Erdos728b.infinite_of_unbounded_n
  intro N
  obtain ⟨t, ht, hN, _⟩ := exists_windowTriple_above C₁ C₂ ε h₁ h₁₂ hε hε' N
  exact ⟨t, ht, hN⟩

end Erdos728
