import LatticeProb.Analysis.ConeVectorMembership

/-! # Cone vectors under positive coordinate scaling -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Positive scaling of each coordinate preserves the forward first exit. -/
theorem coneFirstExit_mul_pos (X Y : ℝ → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (s : ℝ) :
    coneFirstExit (fun t => c * X t) (fun t => d * Y t) s =
      coneFirstExit X Y s := by
  simp only [coneFirstExit, mul_lt_mul_iff_right₀ hc, mul_lt_mul_iff_right₀ hd]

/-- Positive scaling of each coordinate preserves the forward joint exit. -/
theorem coneJointExit_mul_pos (X Y : ℝ → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (s : ℝ) :
    coneJointExit (fun t => c * X t) (fun t => d * Y t) s =
      coneJointExit X Y s := by
  simp only [coneJointExit, mul_lt_mul_iff_right₀ hc, mul_lt_mul_iff_right₀ hd]

/-- Positive scaling of each coordinate preserves the backward first exit. -/
theorem coneFirstExitBackward_mul_pos (X Y : ℝ → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (s : ℝ) :
    coneFirstExitBackward (fun t => c * X t) (fun t => d * Y t) s =
      coneFirstExitBackward X Y s := by
  simp only [coneFirstExitBackward, mul_lt_mul_iff_right₀ hc, mul_lt_mul_iff_right₀ hd]

/-- Positive scaling of each coordinate preserves the backward joint exit. -/
theorem coneJointExitBackward_mul_pos (X Y : ℝ → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (s : ℝ) :
    coneJointExitBackward (fun t => c * X t) (fun t => d * Y t) s =
      coneJointExitBackward X Y s := by
  simp only [coneJointExitBackward, mul_lt_mul_iff_right₀ hc, mul_lt_mul_iff_right₀ hd]

/-- Forward cone-vector membership is unchanged by positive coordinate scaling. -/
theorem forwardConeVectors_mul_pos (X Y : ℝ → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    forwardConeVectors (fun t => c * X t) (fun t => d * Y t) =
      forwardConeVectors X Y := by
  ext ⟨a, s⟩
  simp only [forwardConeVectors, mem_ofPred_eq, coneFirstExit_mul_pos X Y hc hd,
    coneJointExit_mul_pos X Y hc hd, mul_le_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hd]

/-- Backward cone-vector membership is unchanged by positive coordinate scaling. -/
theorem backwardConeVectors_mul_pos (X Y : ℝ → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    backwardConeVectors (fun t => c * X t) (fun t => d * Y t) =
      backwardConeVectors X Y := by
  ext ⟨a, s⟩
  simp only [backwardConeVectors, mem_ofPred_eq, coneFirstExitBackward_mul_pos X Y hc hd,
    coneJointExitBackward_mul_pos X Y hc hd, mul_le_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hd]

end LatticeProb
