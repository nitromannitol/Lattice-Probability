import LatticeProb.LQG.SelectedHullFieldCode

/-! # Shift invariance of selected hull field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A common integer-period shift preserves the selected hull field code when
its selected anchor has unit integral. -/
theorem selectedHullFieldCode_eq_of_period_shift {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : Ω → ℕ) (hψ : ∀ ω, ∫ z, ψ (f ω) z = 1)
    (k : Ω → ℤ)
    (hshift : ∀ ω θ, h ω θ = g ω θ + ((k ω : ℝ) * p) * (∫ z, θ z)) :
    selectedHullFieldCode h A n φ ψ hp f = selectedHullFieldCode g A n φ ψ hp f := by
  funext ω i
  dsimp only [selectedHullFieldCode]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · by_cases hmem : ω ∈ {ω' | tsupport (φ i : ℂ → ℝ) ∪
          tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))}
      · simp only [Set.indicator_of_mem hmem]
        rw [hshift ω (φ i), hshift ω (ψ (f ω)), hψ ω]
        ring
      · simp only [Set.indicator_of_notMem hmem]
    · by_cases hmem : ω ∈ {ω' | tsupport (φ i : ℂ → ℝ) ∪
          tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))}
      · simp only [Set.indicator_of_mem hmem]
        rw [hshift ω (ψ (f ω)), hψ ω, mul_one]
        simpa only [zsmul_eq_mul] using (toIcoMod_add_zsmul hp 0 (g ω (ψ (f ω))) (k ω))
      · simp only [Set.indicator_of_notMem hmem]

end LatticeProb.LQG
