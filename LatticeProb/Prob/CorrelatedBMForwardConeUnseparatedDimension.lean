import LatticeProb.Prob.CorrelatedBMForwardConeDimensionFromSurvival

/-! # A countable decomposition of forward Brownian cone vectors -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A joint survival estimate bounds the dimension of all forward cone vectors
whose two time coordinates lie in the negative unit interval, in either time orientation. -/
theorem ae_dimH_neg_unit_forwardConeVectors_le_of_joint_survival
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
        z ∈ forwardConeVectors X Y ∧ -1 < z.2 ∧ z.1 < 0} ≤ β := by
  have hdim (j : ℕ) := ae_dimH_forwardConeVectors_neg_unit_le_of_joint_survival
    hμ α β hα hβ C (1 / (j + 1 : ℝ)) p direction
    hC (by positivity) hdir hslack hJ
  filter_upwards [ae_all_iff.2 hdim] with ω hω
  let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
  let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
  let S : ℕ → Set (ℝ × ℝ) := fun j =>
    {z | z ∈ forwardConeVectors X Y ∧ -1 < z.2 ∧ z.1 < 0 ∧
      1 / (j + 1 : ℝ) < z.1 - z.2}
  change dimH {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧ -1 < z.2 ∧ z.1 < 0} ≤ β
  apply le_trans (dimH_mono (show {z : ℝ × ℝ |
    z ∈ forwardConeVectors X Y ∧ -1 < z.2 ∧ z.1 < 0} ⊆ ⋃ j, S j from ?_))
  · rw [dimH_iUnion]
    exact iSup_le hω
  · intro z hz
    have hgap : 0 < z.1 - z.2 := by
      have h := hz.1
      change z.1 = coneFirstExit X Y z.2 ∧ _ at h
      linarith [h.1, h.2.1]
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hgap
    exact mem_iUnion.mpr ⟨j, hz.1, hz.2.1, hz.2.2, hj⟩

end LatticeProb.CorrelatedBM
