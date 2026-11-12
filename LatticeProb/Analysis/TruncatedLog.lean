import Mathlib

/-!
# The truncated logarithmic kernel

For a point `z` of a seminormed group, constants `C ≥ 0` and `M > 0`, the function
`w ↦ max 0 (C * log (1 / max ‖z - w‖ M⁻¹) + C)` is the logarithmic kernel `C log (1/‖z - w‖) + C`
truncated at distance `M⁻¹` from the pole and clipped at `0`. It agrees with the clipped kernel when
`‖z - w‖ ≥ M⁻¹`, it is dominated by the clipped kernel away from the pole, it is bounded by
`C (log M + 1)` and it is `C M`-Lipschitz. These are the properties needed to compare a sum of a
logarithmically bounded Green function over the vertices of a cell decomposition with an integral
against a measure (a Lipschitz test function is required there).

The Lipschitz bound rests on `abs_log_sub_log_le_div`: on `[m, ∞)` with `m > 0` the logarithm is
`m⁻¹`-Lipschitz, a consequence of `log x ≤ x - 1`.
-/

namespace LatticeProb.TruncatedLog

open Real

/-- On `[m, ∞)` with `0 < m` the logarithm is `m⁻¹`-Lipschitz. -/
theorem abs_log_sub_log_le_div {m a b : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have key : ∀ {x y : ℝ}, 0 < x → m ≤ y → Real.log x - Real.log y ≤ |x - y| / m := by
    intro x y hx hy
    have hy0 : 0 < y := hm.trans_le hy
    rw [← Real.log_div hx.ne' hy0.ne']
    calc Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy0)
      _ = (x - y) / y := by field_simp
      _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
      _ ≤ |x - y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hy
  rw [abs_sub_le_iff]
  refine ⟨key ha0 hb, ?_⟩
  rw [abs_sub_comm]
  exact key hb0 ha

/-- `t ↦ log (max t m)` is `m⁻¹`-Lipschitz on `ℝ` for `0 < m`. -/
theorem abs_log_max_sub_log_max_le {m : ℝ} (hm : 0 < m) (s t : ℝ) :
    |Real.log (max s m) - Real.log (max t m)| ≤ |s - t| / m :=
  (abs_log_sub_log_le_div hm (le_max_right _ _) (le_max_right _ _)).trans
    (div_le_div_of_nonneg_right (abs_max_sub_max_le_abs _ _ _) hm.le)

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The logarithmic kernel `w ↦ C log (1/‖z - w‖) + C`, truncated at distance `M⁻¹` from the pole
`z` and clipped at `0`. -/
noncomputable def truncLogKernel (C M : ℝ) (z w : E) : ℝ :=
  max 0 (C * Real.log (max ‖z - w‖ M⁻¹)⁻¹ + C)

theorem truncLogKernel_nonneg (C M : ℝ) (z w : E) : 0 ≤ truncLogKernel C M z w :=
  le_max_left _ _

/-- Away from the truncation radius the truncated kernel is the clipped logarithmic kernel. -/
theorem truncLogKernel_eq_of_inv_le {C M : ℝ} {z w : E} (h : M⁻¹ ≤ ‖z - w‖) :
    truncLogKernel C M z w = max 0 (C * Real.log ‖z - w‖⁻¹ + C) := by
  rw [truncLogKernel, max_eq_left h]

/-- The truncated kernel dominates the logarithmic kernel away from the truncation radius. -/
theorem le_truncLogKernel_of_inv_le {C M : ℝ} {z w : E} (h : M⁻¹ ≤ ‖z - w‖) :
    C * Real.log ‖z - w‖⁻¹ + C ≤ truncLogKernel C M z w := by
  rw [truncLogKernel_eq_of_inv_le h]
  exact le_max_right _ _

/-- Off the pole the truncated kernel is at most the clipped logarithmic kernel. -/
theorem truncLogKernel_le_of_pos {C M : ℝ} (hC : 0 ≤ C) {z w : E}
    (hzw : 0 < ‖z - w‖) :
    truncLogKernel C M z w ≤ max 0 (C * Real.log ‖z - w‖⁻¹ + C) := by
  refine max_le_max le_rfl ?_
  have hlog : Real.log (max ‖z - w‖ M⁻¹)⁻¹ ≤ Real.log ‖z - w‖⁻¹ := by
    rw [Real.log_inv, Real.log_inv, neg_le_neg_iff]
    exact Real.log_le_log hzw (le_max_left _ _)
  linarith [mul_le_mul_of_nonneg_left hlog hC]

/-- The truncated kernel is bounded by `C (log M + 1)`. -/
theorem truncLogKernel_le {C M : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M) (z w : E) :
    truncLogKernel C M z w ≤ C * (Real.log M + 1) := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  refine max_le (mul_nonneg hC (by linarith)) ?_
  have hlog : Real.log (max ‖z - w‖ M⁻¹)⁻¹ ≤ Real.log M := by
    rw [Real.log_inv, neg_le, ← Real.log_inv]
    exact Real.log_le_log (inv_pos.2 hM0) (le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_left hlog hC]

/-- The truncated kernel is `C M`-Lipschitz. -/
theorem abs_truncLogKernel_sub_le {C M : ℝ} (hC : 0 ≤ C) (hM : 0 < M) (z w w' : E) :
    |truncLogKernel C M z w - truncLogKernel C M z w'| ≤ C * M * ‖w - w'‖ := by
  have hMi : 0 < M⁻¹ := inv_pos.2 hM
  have hlog := abs_log_max_sub_log_max_le hMi ‖z - w'‖ ‖z - w‖
  have hnorm : |‖z - w'‖ - ‖z - w‖| ≤ ‖w - w'‖ := by
    have := abs_norm_sub_norm_le (z - w') (z - w)
    rwa [show z - w' - (z - w) = w - w' by abel] at this
  calc |truncLogKernel C M z w - truncLogKernel C M z w'|
      ≤ |(C * Real.log (max ‖z - w‖ M⁻¹)⁻¹ + C) - (C * Real.log (max ‖z - w'‖ M⁻¹)⁻¹ + C)| :=
        by rw [truncLogKernel, truncLogKernel, max_comm (0 : ℝ), max_comm (0 : ℝ)]
           exact abs_max_sub_max_le_abs _ _ _
    _ = C * |Real.log (max ‖z - w'‖ M⁻¹) - Real.log (max ‖z - w‖ M⁻¹)| := by
        rw [Real.log_inv, Real.log_inv, ← abs_of_nonneg hC, ← abs_mul, abs_of_nonneg hC]
        congr 1
        ring
    _ ≤ C * (|‖z - w'‖ - ‖z - w‖| / M⁻¹) := mul_le_mul_of_nonneg_left hlog hC
    _ = C * M * |‖z - w'‖ - ‖z - w‖| := by rw [div_inv_eq_mul]; ring
    _ ≤ C * M * ‖w - w'‖ := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC hM.le)

theorem continuous_truncLogKernel {C M : ℝ} (hM : 0 < M) (z : E) :
    Continuous (truncLogKernel C M z) := by
  have hpos : ∀ w : E, max ‖z - w‖ M⁻¹ ≠ 0 := fun w =>
    (lt_max_of_lt_right (inv_pos.2 hM)).ne'
  have hc : Continuous fun w : E => max ‖z - w‖ M⁻¹ :=
    (continuous_const.sub continuous_id).norm.max continuous_const
  exact continuous_const.max
    ((continuous_const.mul ((hc.inv₀ hpos).log fun w => inv_ne_zero (hpos w))).add continuous_const)

end LatticeProb.TruncatedLog
