import LatticeProb.Prob.CorrelatedBMConeDimensionFromSurvival
import LatticeProb.Analysis.ConeVectorHorizonDimension

/-! # A countable decomposition of Brownian cone vectors -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A joint survival estimate bounds the dimension of all backward cone vectors
whose two time coordinates lie in the unit interval, in either time orientation. -/
theorem ae_dimH_unit_backwardConeVectors_le_of_joint_survival
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C p direction : ℝ) (hC : 0 < C)
    (hdir : direction = 1 ∨ direction = -1)
    (hslack : 2 < (β : ℝ) + (α : ℝ) * (p + 2))
    (hJ : ∀ h : ℝ, 0 < h → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (ν : Measure Path2), IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier (C * (factorialGridMesh n) ^ (α : ℝ)) h) ≤
          ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ (α : ℝ)) ^ p)) :
    ∀ᵐ ω ∂μ,
      dimH {z : ℝ × ℝ |
        let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
        let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
        z ∈ backwardConeVectors X Y ∧ 0 < z.1 ∧ z.2 < 1} ≤ β := by
  have hdim (j k : ℕ) := ae_dimH_backwardConeVectors_le_of_joint_survival
    hμ α β hα hβ C (1 / (j + 1 : ℝ)) (1 / (k + 1 : ℝ)) p direction
    hC (by positivity) (by positivity) hdir hslack hJ
  filter_upwards [ae_all_iff.2 fun j => ae_all_iff.2 (hdim j)] with ω hω
  let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
  let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
  let S : ℕ → Set (ℝ × ℝ) := fun j =>
    {z | z ∈ backwardConeVectors X Y ∧ 0 < z.1 ∧ z.2 < 1 ∧
      1 / (j + 1 : ℝ) < z.2 - z.1}
  have hS (j : ℕ) : dimH (S j) ≤ β := by
    have hsub : S j = backwardConeVectors X Y ∩ S j := by
      ext z
      simp only [S, mem_ofPred_eq, mem_inter_iff]
      tauto
    rw [hsub]
    apply dimH_backwardConeVectors_inter_le_of_horizons
    intro k
    apply (dimH_mono ?_).trans (hω j k)
    intro z hz
    exact ⟨hz.1.1, hz.1.2.2.1, hz.1.2.2.2.1, hz.1.2.2.2.2, hz.2⟩
  change dimH {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧ 0 < z.1 ∧ z.2 < 1} ≤ β
  apply le_trans (dimH_mono (show {z : ℝ × ℝ |
    z ∈ backwardConeVectors X Y ∧ 0 < z.1 ∧ z.2 < 1} ⊆ ⋃ j, S j from ?_))
  · rw [dimH_iUnion]
    exact iSup_le hS
  · intro z hz
    have hgap : 0 < z.2 - z.1 := by
      have h := hz.1
      change z.1 = coneJointExitBackward X Y z.2 ∧ _ at h
      linarith [h.2.1, h.2.2.1]
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hgap
    exact mem_iUnion.mpr ⟨j, hz.1, hz.2.1, hz.2.2, hj⟩

end LatticeProb.CorrelatedBM
