import LatticeProb.LQG.DyadicHullAnchors
import LatticeProb.LQG.MeasurableHullCollar

/-! # Normalized anchors for measurable collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A measurable reciprocal-radius collar around sets containing a common point
admits a measurable index into the normalized bumps centered at that point. -/
theorem exists_measurable_bump_index_in_thickening {Ω : Type}
    (A : Ω → Set ℂ) (z : ℂ) (hz : ∀ ω, z ∈ A ω)
    (f : Ω → ℕ) (hf : Measurable[setSigma A] f) :
    ∃ g : Ω → ℕ, Measurable[setSigma A] g ∧ ∀ ω,
      (∫ x, bumpTest (g ω) z x) = 1 ∧
      tsupport (bumpTest (g ω) z : ℂ → ℝ) ⊆
        thickening (1 / ((f ω : ℝ) + 1)) (A ω) := by
  classical
  have hex : ∀ k : ℕ, ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < 1 / ((k : ℝ) + 1) := by
    intro k
    exact exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  let q : ℕ → ℕ := fun k => Nat.find (hex k)
  refine ⟨q ∘ f, (measurable_of_countable q).comp hf, ?_⟩
  intro ω
  refine ⟨GFFLaw.integral_bumpTest _ _, ?_⟩
  rw [GM.tsupport_bumpTest]
  exact (closedBall_subset_ball (Nat.find_spec (hex (f ω)))).trans
    (ball_subset_thickening (hz ω) _)

/-- Compact sets with a common point admit a measurable collar inside a
specified hull and a measurable unit-integral bump supported in that collar. -/
theorem exists_measurable_collar_bump {Ω : Type}
    (A : Ω → Set ℂ) (hA : ∀ ω, IsCompact (A ω)) (n : ℕ)
    (z : ℂ) (hz : ∀ ω, z ∈ A ω) :
    ∃ f g : Ω → ℕ, Measurable[setSigma A] f ∧ Measurable[setSigma A] g ∧
      ∀ ω, thickening (1 / ((f ω : ℝ) + 1)) (A ω) ⊆
          interior (dyadicHull n (A ω)) ∧
        (∫ x, bumpTest (g ω) z x) = 1 ∧
        tsupport (bumpTest (g ω) z : ℂ → ℝ) ⊆
          thickening (1 / ((f ω : ℝ) + 1)) (A ω) := by
  obtain ⟨f, hf, hcollar⟩ := exists_measurable_thickening_subset_interior_dyadicHull A hA n
  obtain ⟨g, hg, hanchor⟩ := exists_measurable_bump_index_in_thickening A z hz f hf
  exact ⟨f, g, hf, hg, fun ω => ⟨hcollar ω, hanchor ω⟩⟩

end LatticeProb.LQG
