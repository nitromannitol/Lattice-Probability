import LatticeProb.Prob.BrownianDriftRestartHit
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation

/-! # First-passage conventions for drifted paths -/

open MeasureTheory Set LatticeProb
open scoped NNReal ENNReal

namespace QuantumZipper.WedgeTrans

/-- When the level is reached, the real first-passage time of the negated path
agrees with the extended nonnegative first-passage time of the original path. -/
theorem ofReal_hitTime_eq_hitDrift {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (μ a : ℝ) (ω : Ω) {g : ℝ → ℝ}
    (hg : ∀ t : ℝ, 0 ≤ t → g t = -(B t.toNNReal ω + μ * t))
    (hhit : ∃ t : ℝ≥0, a ≤ B t ω + μ * t) :
    ENNReal.ofReal (hitTime g a) = hitDrift B μ a ω := by
  let S : Set ℝ≥0 := {t | a ≤ B t ω + μ * t}
  have hset : {t : ℝ | 0 ≤ t ∧ g t ≤ -a} = ((↑) : ℝ≥0 → ℝ) '' S := by
    ext t
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨t.toNNReal, ?_, Real.coe_toNNReal t ht⟩
      rw [hg t ht] at h
      dsimp [S]
      rw [max_eq_left ht]
      linarith
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s.coe_nonneg, ?_⟩
      rw [hg s s.coe_nonneg, Real.toNNReal_coe]
      dsimp [S] at hs
      linarith
  rw [hitTime, hset, ← NNReal.coe_sInf]
  unfold hitDrift
  simp only [hhit, dite_true]
  simp only [ENNReal.ofReal_coe_nnreal]
  rfl

end QuantumZipper.WedgeTrans
