import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Admissible intermediate radii -/

set_option autoImplicit false

namespace LatticeProb

/-- For small positive `d`, the intermediate radius `d ^ a / 2` lies between
`d` and `1 / 2`, uniformly in `d`. -/
theorem exists_intermediate_radius_threshold {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ {d : ℝ}, 0 < d → d < δ →
      d ≤ d ^ a / 2 ∧ 4 * (d ^ a / 2) ^ 2 ≤ 1 := by
  have hlim : Filter.Tendsto (fun d : ℝ => d ^ (1 - a)) (nhds 0) (nhds 0) :=
    Filter.Tendsto.rpow_const_nhds_zero Filter.tendsto_id (by linarith)
  obtain ⟨δ, hδ, hδlim⟩ := (Metric.tendsto_nhds_nhds.mp hlim) (1 / 2) (by norm_num)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro d hd hdδ
  have hd1 : d ≤ 1 := le_trans hdδ.le (min_le_right _ _)
  have hdδ' : dist d 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hd]
    exact lt_of_lt_of_le hdδ (min_le_left _ _)
  have hsmall : d ^ (1 - a) < 1 / 2 := by
    have h := hδlim hdδ'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg hd.le _)] at h
    exact h
  have hpow : d ^ (1 - a) * d ^ a = d := by
    rw [← Real.rpow_add hd]
    simp only [sub_add_cancel, Real.rpow_one]
  have hpos : 0 < d ^ a := Real.rpow_pos_of_pos hd _
  have hle : d ^ a ≤ 1 := Real.rpow_le_one hd.le hd1 ha.le
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (d ^ a), sq_nonneg (1 - d ^ a)]

end LatticeProb
