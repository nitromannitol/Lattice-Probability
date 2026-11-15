import LatticeProb.LQG.HullLocalFieldDetermination
import LatticeProb.LQG.SelectedHullFieldCodeEquiv

/-! # Local field pairings and anchored hull observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Equality of all anchored hull codes is equivalent to equality of local
pairings up to one integer-period shift shared across all scales. -/
theorem eq_anchored_codes_iff_pairings_on_hulls {Ω : Type}
    (g h : Ω → DistC) (A : Ω → Set ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (ω : Ω)
    (hunit : ∀ n, ∫ x, ψ n x = 1)
    (hsupport : ∀ n, tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))) :
    (∀ n, selectedHullFieldCode g A n
      (adjoinTestSequence localDenseTest ψ) ψ hp (fun _ => n) ω =
      selectedHullFieldCode h A n
      (adjoinTestSequence localDenseTest ψ) ψ hp (fun _ => n) ω) ↔
    ∃ k : ℤ, ∀ n (φ : TestC),
      tsupport (φ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) →
      h ω φ = g ω φ + ((k : ℝ) * p) * (∫ z, φ z) := by
  constructor
  · exact pairings_on_hulls_of_eq_anchored_codes g h A ψ hp ω hunit hsupport
  · rintro ⟨k, hk⟩ n
    have henabled : ∃ i, tsupport (adjoinTestSequence localDenseTest ψ i : ℂ → ℝ) ∪
        tsupport (ψ ((fun _ : Ω => n) ω) : ℂ → ℝ) ⊆
          interior (dyadicHull n (A ω)) := by
      refine ⟨Sum.inr n, ?_⟩
      simpa only [adjoinTestSequence_inr] using union_subset (hsupport n) (hsupport n)
    apply (selectedHullFieldCode_eq_iff g h A n (adjoinTestSequence localDenseTest ψ)
      ψ hp (fun _ => n) ω henabled).2
    refine ⟨k, ?_, ?_⟩
    · simpa only [hunit n, mul_one] using hk n (ψ n) (hsupport n)
    · intro i hi
      exact hk n _ (Subset.trans (subset_union_left) hi)

end LatticeProb.LQG
