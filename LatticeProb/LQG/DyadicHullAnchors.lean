import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2FiltA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

/-! # Normalized test functions on dyadic hull neighborhoods -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric LQGMetric LQGMetric.Blueprint
open LQGMetric.LocalEvent

namespace LatticeProb.LQG

/-- For each scale one can choose a unit-integral test function whose support
lies in the hull interior of every set containing a given point. -/
theorem exists_dyadicHull_anchors (z : ℂ) :
    ∃ ψ : ℕ → TestC, ∀ n,
      (∫ x, ψ n x) = 1 ∧ ∀ A : Set ℂ, z ∈ A →
        tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n A) := by
  have h : ∀ n : ℕ, ∃ ψ : TestC, (∫ x, ψ x) = 1 ∧
      ∀ A : Set ℂ, z ∈ A → tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n A) := by
    intro n
    have hz : z ∈ interior (dyadicHull n ({z} : Set ℂ)) :=
      subset_interior_dyadicHull n {z} (mem_singleton z)
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨bumpTest m z, GFFLaw.integral_bumpTest m z, ?_⟩
    intro A hzA
    have hsub : ({z} : Set ℂ) ⊆ A := singleton_subset_iff.mpr hzA
    rw [GM.tsupport_bumpTest]
    exact (closedBall_subset_ball hm).trans
      (hrsub.trans (interior_mono (GM.gm_dyadicHull_mono n hsub)))
  choose ψ hψ using h
  exact ⟨ψ, hψ⟩

/-- Adjacent normalized anchors furnish a jointly supported unit-integral test
for each pair of successive hulls. -/
theorem dyadicHull_anchor_adjacent_overlap (A : Set ℂ) (ψ : ℕ → TestC)
    (hunit : ∀ n, ∫ x, ψ n x = 1)
    (hsupport : ∀ n, tsupport (ψ n : ℂ → ℝ) ⊆ interior (dyadicHull n A)) :
    ∀ n, ∃ i : ℕ, (∫ x, ψ i x) = 1 ∧
      tsupport (ψ i : ℂ → ℝ) ∪ tsupport (ψ n : ℂ → ℝ) ⊆
        interior (dyadicHull n A) ∧
      tsupport (ψ i : ℂ → ℝ) ∪ tsupport (ψ (n + 1) : ℂ → ℝ) ⊆
        interior (dyadicHull (n + 1) A) := by
  intro n
  refine ⟨n + 1, hunit (n + 1), ?_, ?_⟩
  · exact union_subset ((hsupport (n + 1)).trans
      (interior_mono (hull_succ_subset n A))) (hsupport n)
  · exact union_subset (hsupport (n + 1)) (hsupport (n + 1))

end LatticeProb.LQG
