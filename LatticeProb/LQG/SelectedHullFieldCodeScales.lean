import LatticeProb.LQG.SelectedHullFieldCodeReadout

/-! # Compatibility of selected field observations across scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Equal selected codes at every scale have one common integer-period shift
when a fixed unit-integral test has its joint support gate enabled at every
scale. The selected anchor may depend on the scale. -/
theorem selectedHullFieldCode_pairings_of_eq_all_scales {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (A : Ω → Set ℂ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : ℕ → Ω → ℕ) (ω : Ω) (i₀ : I)
    (hunit : ∫ z, φ i₀ z = 1)
    (hgate : ∀ n, tsupport (φ i₀ : ℂ → ℝ) ∪
      tsupport (ψ (f n ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)))
    (heq : ∀ n, selectedHullFieldCode g A n φ ψ hp (f n) ω =
      selectedHullFieldCode h A n φ ψ hp (f n) ω) :
    ∃ k : ℤ, ∀ n,
      h ω (ψ (f n ω)) = g ω (ψ (f n ω)) + (k : ℝ) * p ∧
      ∀ i, tsupport (φ i : ℂ → ℝ) ∪
        tsupport (ψ (f n ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
        h ω (φ i) = g ω (φ i) + ((k : ℝ) * p) * (∫ z, φ i z) := by
  obtain ⟨k, _, hbase⟩ := selectedHullFieldCode_pairings_of_eq g h A 0 φ ψ hp
    (f 0) ω ⟨i₀, hgate 0⟩ (heq 0)
  have hbase' := hbase i₀ (hgate 0)
  simp only [hunit, mul_one] at hbase'
  refine ⟨k, fun n => ?_⟩
  obtain ⟨j, hjanchor, hjpair⟩ := selectedHullFieldCode_pairings_of_eq g h A n φ ψ hp
    (f n) ω ⟨i₀, hgate n⟩ (heq n)
  have hj := hjpair i₀ (hgate n)
  simp only [hunit, mul_one] at hj
  have hshift : (j : ℝ) * p = (k : ℝ) * p := by linarith
  rw [hshift] at hjanchor hjpair
  exact ⟨hjanchor, hjpair⟩

end LatticeProb.LQG
