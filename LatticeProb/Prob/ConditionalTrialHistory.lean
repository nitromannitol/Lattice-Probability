import LatticeProb.Prob.ConditionalTrialFailure

/-! # Conditional trials with a larger history -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- A conditional lower bound persists when conditioning on a smaller sigma algebra. -/
theorem condExp_const_le_of_le_of_condExp_const_le
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F G : MeasurableSpace Ω} (hFG : F ≤ G) (hG : G ≤ m)
    {f : Ω → ℝ} {p : ℝ}
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[f | G] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[f | F] ω := by
  have hmono := condExp_mono (m := F) (integrable_const p) (integrable_condExp (f := f)) hp
  have htower := condExp_condExp_of_le (f := f) (μ := μ) hFG hG
  rw [condExp_const (hFG.trans hG) p] at hmono
  filter_upwards [hmono, htower] with ω hω ht
  exact ht ▸ hω

/-- Conditional success bounds for a larger history bound the failure of adapted trials. -/
theorem measureReal_no_success_le_of_larger_history
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ 𝒢 : Filtration ℕ m) (hFG : ∀ k, ℱ k ≤ 𝒢 k) (A : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, ∀ᵐ ω ∂μ, p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | 𝒢 k] ω)
    (n : ℕ) :
    μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} ≤
      Real.exp (-(p ^ 2 / 2) * n) := by
  apply measureReal_no_success_le_of_condExp_ge ℱ A hA hp0 hp1 ?_ n
  intro k
  exact condExp_const_le_of_le_of_condExp_const_le (hFG k) (𝒢.le k)
    (hp k)

end LatticeProb
