import LatticeProb.LQG.ConeScaleCountDecay

/-! # Scale counts for power-law windows -/

set_option autoImplicit false
open Filter Set
open scoped Topology ENNReal

namespace LatticeProb.LQG

/-- A power-law inner scale is positive and tends to zero if its total exponent is positive. -/
theorem tendsto_power_window_inner_scale {k a : ℝ} (hka : 0 < k + a) :
    Tendsto (fun δ : ℝ => (δ ^ k / 4) * δ ^ a) (𝓝[>] 0) (𝓝[>] 0) := by
  have hp : Tendsto (fun δ : ℝ => δ ^ (k + a)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (k + a) (Or.inr hka.le)).tendsto
    simpa [Real.zero_rpow hka.ne'] using h.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun δ : ℝ => δ ^ (k + a) / 4) (𝓝[>] 0) (𝓝 0) := by
    simpa using hp.div_const 4
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [Real.rpow_add hδ]
    ring
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_pos (div_pos (Real.rpow_pos_of_pos hδ k) (by norm_num))
      (Real.rpow_pos_of_pos hδ a)

/-- A logarithmic count at a power-law inner scale is absorbed by every
positive power of the window parameter. -/
theorem tendsto_power_window_logarithmic_count {k a C p : ℝ}
    (hka : 0 < k + a) (hC : 0 < C) (hp : 0 < p) :
    Tendsto (fun δ : ℝ =>
      (⌈C * (-Real.log ((δ ^ k / 4) * δ ^ a)) + 3⌉₊ : ℝ) * δ ^ p)
      (𝓝[>] 0) (𝓝 0) := by
  have hp' : Tendsto (fun δ : ℝ => δ ^ p) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
    simpa [Real.zero_rpow hp.ne'] using h.mono_left nhdsWithin_le_nhds
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hp
  have hupper : Tendsto (fun δ : ℝ =>
      (C * ((k + a) * (-Real.log δ) + Real.log 4) + 4) * δ ^ p)
      (𝓝[>] 0) (𝓝 0) := by
    have h := ((hlog.neg).const_mul (C * (k + a))).add
      (hp'.const_mul (C * Real.log 4 + 4))
    convert h using 1 <;> ext δ <;> ring
  apply squeeze_zero' _ _ hupper
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hδ p).le
  · filter_upwards [self_mem_nhdsWithin,
        (tendsto_power_window_inner_scale hka).eventually (Ioo_mem_nhdsGT one_pos)] with δ hδ hb
    have hcount := (logarithmic_scale_count_bounds hC hb).2.le
    have hlogb : Real.log ((δ ^ k / 4) * δ ^ a) =
        (k + a) * Real.log δ - Real.log 4 := by
      have heq : (δ ^ k / 4) * δ ^ a = δ ^ (k + a) / 4 := by
        rw [Real.rpow_add hδ]
        ring
      rw [heq, Real.log_div (Real.rpow_pos_of_pos hδ _).ne' (by norm_num),
        Real.log_rpow hδ]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hδ p).le
    refine hcount.trans_eq ?_
    rw [hlogb]
    ring

end LatticeProb.LQG
