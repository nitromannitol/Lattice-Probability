import LatticeProb.LQG.SelectedHullFieldCodeReadout

/-! # Compatibility of selected field observations at adjacent scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Equal selected codes at every scale have one common integer-period shift
when each pair of adjacent scales shares a unit-integral test whose joint
support gate is enabled at both scales. The test and anchor may vary with the
scale. -/
theorem selectedHullFieldCode_pairings_of_eq_adjacent_scales {Ω : Type} {I : Type*}
    (g h : Ω → DistC) (A : Ω → Set ℂ)
    (φ : I → TestC) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : ℕ → Ω → ℕ) (ω : Ω)
    (hoverlap : ∀ n, ∃ i : I, (∫ z, φ i z) = 1 ∧
      tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ (f n ω) : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω)) ∧
      tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ (f (n + 1) ω) : ℂ → ℝ) ⊆
        interior (dyadicHull (n + 1) (A ω)))
    (heq : ∀ n, selectedHullFieldCode g A n φ ψ hp (f n) ω =
      selectedHullFieldCode h A n φ ψ hp (f n) ω) :
    ∃ k : ℤ, ∀ n,
      h ω (ψ (f n ω)) = g ω (ψ (f n ω)) + (k : ℝ) * p ∧
      ∀ i, tsupport (φ i : ℂ → ℝ) ∪
        tsupport (ψ (f n ω) : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
        h ω (φ i) = g ω (φ i) + ((k : ℝ) * p) * (∫ z, φ i z) := by
  obtain ⟨i₀, _, hgate₀, _⟩ := hoverlap 0
  obtain ⟨k, hkanchor, hkpair⟩ := selectedHullFieldCode_pairings_of_eq g h A 0 φ ψ hp
    (f 0) ω ⟨i₀, hgate₀⟩ (heq 0)
  refine ⟨k, fun n => ?_⟩
  induction n with
  | zero => exact ⟨hkanchor, hkpair⟩
  | succ n ih =>
    obtain ⟨i, hunit, hgate, hgate'⟩ := hoverlap n
    obtain ⟨j, hjanchor, hjpair⟩ := selectedHullFieldCode_pairings_of_eq g h A (n + 1)
      φ ψ hp (f (n + 1)) ω ⟨i, hgate'⟩ (heq (n + 1))
    have hk := ih.2 i hgate
    have hj := hjpair i hgate'
    simp only [hunit, mul_one] at hk hj
    have hshift : (j : ℝ) * p = (k : ℝ) * p := by linarith
    rw [hshift] at hjanchor hjpair
    exact ⟨hjanchor, hjpair⟩

end LatticeProb.LQG
