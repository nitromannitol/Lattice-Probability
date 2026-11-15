import LatticeProb.Prob.BinomialDomination

/-! # Repeated conditional trials -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset

namespace LatticeProb

/-- A uniform lower bound on conditional success probabilities gives an exponential bound
for the probability that all of finitely many adapted trials fail. -/
theorem measureReal_no_success_le_of_condExp_ge
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (A : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, ∀ᵐ ω ∂μ, p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω)
    (n : ℕ) :
    μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} ≤
      Real.exp (-(p ^ 2 / 2) * n) := by
  have hmain := measureReal_binomDom_hoeffding ℱ (G := fun _ => Set.univ) (A := A)
    (fun _ => MeasurableSet.univ) hA hp0 hp1 (show 0 ≤ p / 2 by positivity)
    (fun k => (hp k).mono fun _ h _ => h) n n
  have hsub : {ω | ∀ k ∈ Finset.range n, ω ∉ A k} ⊆
      {ω | (n : ℝ) ≤ binomDomCount (fun _ => Set.univ) n ω ∧
        binomDomHits (fun _ => Set.univ) A n ω ≤ (p - p / 2) * n} := by
    intro ω hω
    have hhits : binomDomHits (fun _ => Set.univ) A n ω = 0 := by
      simp only [binomDomHits, Set.univ_inter]
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Set.indicator_of_notMem (hω k hk)]
    constructor
    · simp [binomDomCount]
    · rw [hhits]
      exact mul_nonneg (by linarith) (Nat.cast_nonneg n)
  calc
    μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} ≤
        Real.exp (-2 * (p / 2) ^ 2 * n) := (measureReal_mono hsub).trans hmain
    _ = Real.exp (-(p ^ 2 / 2) * n) := by congr 1; ring

end LatticeProb
