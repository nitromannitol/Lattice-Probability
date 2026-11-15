import LatticeProb.Euclidean.ParentBlockAbsorbedComparison

/-! # Parent-block collars for clock plateaus -/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- Collars on the strictly increasing stages extend to clock plateaus by
centering each plateau at the value of the path at its sole time. -/
theorem exists_parentBlock_collars_of_strict_stages
    (f : ℝ≥0 → ℂ) (τ : ℕ → ℝ≥0) (K : ℕ) (s r : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hτ : Monotone τ)
    (hstrict : ∀ n < K, τ n < τ (n + 1) → ∃ c : ℂ,
      f (τ n) ∈ closedSquare c s ∧
      ∀ t ∈ Icc (τ n) (τ (n + 1)), f t ∈ Metric.cthickening r (parentBlock c s)) :
    ∃ c : ℕ → ℂ, (∀ n < K, f (τ n) ∈ closedSquare (c n) s) ∧
      ∀ n < K, ∀ t ∈ Icc (τ n) (τ (n + 1)),
        f t ∈ Metric.cthickening r (parentBlock (c n) s) := by
  classical
  have h : ∀ n : ℕ, ∃ c : ℂ, n < K →
      f (τ n) ∈ closedSquare c s ∧
      ∀ t ∈ Icc (τ n) (τ (n + 1)), f t ∈ Metric.cthickening r (parentBlock c s) := by
    intro n
    by_cases hn : n < K
    · by_cases hlt : τ n < τ (n + 1)
      · obtain ⟨c, hc, hcollar⟩ := hstrict n hn hlt
        exact ⟨c, fun _ => ⟨hc, hcollar⟩⟩
      · have heq : τ n = τ (n + 1) := le_antisymm (hτ (Nat.le_succ n)) (le_of_not_gt hlt)
        refine ⟨f (τ n), fun _ => ⟨?_, ?_⟩⟩
        · simp only [closedSquare, mem_ofPred_eq, sub_self, abs_zero]
          constructor <;> positivity
        · intro t ht
          have ht' : t = τ n := le_antisymm (by simpa only [← heq] using ht.2) ht.1
          subst t
          apply Metric.mem_cthickening_of_dist_le _ (f (τ n)) r _ ?_ (by simpa using hr)
          rw [parentBlock_eq hs]
          simp only [closedSquare, mem_ofPred_eq, sub_self, abs_zero]
          constructor <;> positivity
    · exact ⟨0, fun hn' => (hn hn').elim⟩
  choose c hc using h
  exact ⟨c, fun n hn => (hc n hn).1, fun n hn => (hc n hn).2⟩

/-- Terminal-clock comparison requires collar data only on strictly
increasing stages; plateaus are handled at their common time. -/
theorem exists_orderIso_dist_le_of_strict_parentBlock_collars
    (f g : ℝ≥0 → ℂ) (τ σ : ℕ → ℝ≥0) (K : ℕ)
    (s r u v δ : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hτmono : Monotone τ) (hσmono : Monotone σ)
    (hτ : ∀ n < K, τ n < τ K → τ n < τ (n + 1))
    (hσ : ∀ n < K, σ n < σ K → σ n < σ (n + 1))
    (hf : ∀ n < K, τ n < τ (n + 1) → ∃ c : ℂ,
      f (τ n) ∈ closedSquare c s ∧ ∀ t ∈ Icc (τ n) (τ (n + 1)),
        f t ∈ Metric.cthickening r (parentBlock c s))
    (hg : ∀ n < K, σ n < σ (n + 1) → ∃ c : ℂ,
      g (σ n) ∈ closedSquare c u ∧ ∀ t ∈ Icc (σ n) (σ (n + 1)),
        g t ∈ Metric.cthickening v (parentBlock c u))
    (hanchors : ∀ n ≤ K, dist (f (τ n)) (g (σ n)) ≤ δ) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t,
      dist (f (min t (τ K))) (g (min (φ t) (σ K))) ≤
        max (r + 4 * s) (v + 4 * u) + δ + max (r + 4 * s) (v + 4 * u) := by
  obtain ⟨c, hc, hfc⟩ := exists_parentBlock_collars_of_strict_stages f τ K s r hs hr hτmono hf
  obtain ⟨d, hd, hgc⟩ := exists_parentBlock_collars_of_strict_stages g σ K u v hu hv hσmono hg
  exact exists_orderIso_dist_le_of_parentBlock_collars_terminal_clocks f g τ σ K
    c d s r u v δ hs hr hu hv hτ0 hσ0 hτmono hσmono hτ hσ hc hd hfc hgc hanchors

end LatticeProb.ParentBlock
end
