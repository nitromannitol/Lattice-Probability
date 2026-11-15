import LatticeProb.LQG.CollarCodeGerm

/-! # Normalized anchors for reciprocal collars -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A common point determines unit-integral test functions supported in the
corresponding reciprocal collar of every set containing that point. -/
theorem exists_reciprocal_collar_anchors (z : ℂ) :
    ∃ ψ : ℕ → TestC, ∀ k,
      (∫ x, ψ k x) = 1 ∧ ∀ A : Set ℂ, z ∈ A →
        tsupport (ψ k : ℂ → ℝ) ⊆ thickening (1 / ((k : ℝ) + 1)) A := by
  have hex : ∀ k : ℕ, ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < 1 / ((k : ℝ) + 1) := by
    intro k
    exact exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  let ψ : ℕ → TestC := fun k => bumpTest (Nat.find (hex k)) z
  refine ⟨ψ, fun k => ⟨GFFLaw.integral_bumpTest _ _, ?_⟩⟩
  intro A hz
  change tsupport (bumpTest (Nat.find (hex k)) z : ℂ → ℝ) ⊆ _
  rw [GM.tsupport_bumpTest]
  exact (closedBall_subset_ball (Nat.find_spec (hex k))).trans
    (ball_subset_thickening hz _)

/-- A single family of reciprocal-collar anchors makes the germ of the
collar codes observable in each enclosing hull with a suitable fixed anchor. -/
theorem exists_collarFieldCode_germ_le_localHullFieldSigma {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ)) (φ : I → TestC)
    {p : ℝ} (hp : 0 < p) :
    ∃ ψ : ℕ → TestC, (∀ k, ∫ x, ψ k x = 1) ∧
      (∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
        thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)) ∧
      ∀ n, ∃ a : TestC, (∫ x, a x) = 1 ∧
        (∀ ω, tsupport (a : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ))) ∧
        (⨅ k, MeasurableSpace.comap (collarFieldCode h K φ ψ hp k) inferInstance) ≤
          localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n a hp := by
  obtain ⟨ψ, hψ⟩ := exists_reciprocal_collar_anchors z
  have hunit : ∀ k, ∫ x, ψ k x = 1 := fun k => (hψ k).1
  have hsupp : ∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) :=
    fun k ω => (hψ k).2 _ (hz ω)
  exact ⟨ψ, hunit, hsupp, fun n =>
    iInf_collarFieldCode_le_localHullFieldSigma h K n z hz φ ψ hunit hsupp hp⟩

end LatticeProb.LQG
