import LatticeProb.LQG.SelectedHullFieldCodeReadout

/-! # Equality of selected hull field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- If a joint support gate is enabled, equality of selected field codes is
characterized by one integer-period shift of the anchor and all enabled test
pairings. -/
theorem selectedHullFieldCode_eq_iff {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : Ω → ℕ) (ω : Ω)
    (henabled : ∃ i, tsupport (φ i : ℂ → ℝ) ∪
      tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))) :
    selectedHullFieldCode g A n φ ψ hp f ω =
        selectedHullFieldCode h A n φ ψ hp f ω ↔
      ∃ k : ℤ, h ω (ψ (f ω)) = g ω (ψ (f ω)) + (k : ℝ) * p ∧
        ∀ i, tsupport (φ i : ℂ → ℝ) ∪
          tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
          h ω (φ i) = g ω (φ i) + ((k : ℝ) * p) * (∫ z, φ i z) := by
  constructor
  · exact selectedHullFieldCode_pairings_of_eq g h A n φ ψ hp f ω henabled
  · rintro ⟨k, ha, hc⟩
    funext i
    dsimp only [selectedHullFieldCode]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · by_cases hm : ω ∈ {ω' | tsupport (φ i : ℂ → ℝ) ∪
            tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))}
        · simp only [Set.indicator_of_mem hm]
          rw [ha, hc i hm]
          ring
        · simp only [Set.indicator_of_notMem hm]
      · by_cases hm : ω ∈ {ω' | tsupport (φ i : ℂ → ℝ) ∪
            tsupport (ψ (f ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω'))}
        · simp only [Set.indicator_of_mem hm]
          rw [ha]
          symm
          simpa only [zsmul_eq_mul] using
            (toIcoMod_add_zsmul hp 0 (g ω (ψ (f ω))) k)
        · simp only [Set.indicator_of_notMem hm]

end LatticeProb.LQG
