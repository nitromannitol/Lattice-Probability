import LatticeProb.LQG.RandomDiscreteFieldCode

/-! # Shift invariance of discrete-period field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- Integer-period shifts of a field preserve its random-neighborhood code
when every anchor has unit integral. -/
theorem randomDiscreteFieldCode_eq_of_period_shift {Ω I J : Type*}
    (K : Ω → NonemptyCompacts ℂ) (g h : Ω → DistC)
    (S : I → Set ℂ) (φ : I → TestC) (ψ : J → TestC) (r : J → ℝ)
    {p : ℝ} (hp : 0 < p) (hψ : ∀ j, ∫ z, ψ j z = 1)
    (n : Ω → ℤ)
    (hshift : ∀ ω θ, h ω θ = g ω θ + ((n ω : ℝ) * p) * (∫ z, θ z)) :
    randomDiscreteFieldCode K h S φ ψ r hp =
      randomDiscreteFieldCode K g S φ ψ r hp := by
  funext ω
  apply Prod.ext
  · funext j i
    dsimp only [randomDiscreteFieldCode]
    apply Prod.ext
    · rfl
    · by_cases hmem : ω ∈ {ω | S i ⊆ thickening (r j) (K ω : Set ℂ)}
      · simp only [Set.indicator_of_mem hmem]
        rw [hshift ω (φ i), hshift ω (ψ j), hψ j]
        ring
      · simp only [Set.indicator_of_notMem hmem]
  · funext j
    dsimp only [randomDiscreteFieldCode]
    rw [hshift ω (ψ j), hψ j, mul_one]
    simpa only [zsmul_eq_mul] using (toIcoMod_add_zsmul hp 0 (g ω (ψ j)) (n ω))

end LatticeProb.LQG
