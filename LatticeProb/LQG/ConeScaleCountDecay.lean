import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! # Logarithmic scale counts -/

set_option autoImplicit false
open Filter Set
open scoped Topology ENNReal

namespace LatticeProb.LQG

/-- A logarithmic time cutoff admits a natural scale count within one unit. -/
theorem logarithmic_scale_count_bounds {C b : ℝ} (hC : 0 < C)
    (hb : b ∈ Ioo (0 : ℝ) 1) :
    C * (-Real.log b) + 3 ≤ (⌈C * (-Real.log b) + 3⌉₊ : ℝ) ∧
      (⌈C * (-Real.log b) + 3⌉₊ : ℝ) < C * (-Real.log b) + 4 := by
  have hlog : 0 < -Real.log b := neg_pos.mpr (Real.log_neg hb.1 hb.2)
  constructor
  · exact Nat.le_ceil _
  · have h := Nat.ceil_lt_add_one (show 0 ≤ C * (-Real.log b) + 3 by positivity)
    linarith

/-- Any positive power absorbs the logarithmic number of scales. -/
theorem tendsto_logarithmic_scale_count_mul_rpow {C p : ℝ}
    (hC : 0 < C) (hp : 0 < p) :
    Tendsto (fun b : ℝ => (⌈C * (-Real.log b) + 3⌉₊ : ℝ) * b ^ p)
      (𝓝[>] 0) (𝓝 0) := by
  have hp' : Tendsto (fun b : ℝ => b ^ p) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
    simpa [Real.zero_rpow hp.ne'] using h.mono_left nhdsWithin_le_nhds
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hp
  have hupper : Tendsto (fun b : ℝ => (C * (-Real.log b) + 4) * b ^ p)
      (𝓝[>] 0) (𝓝 0) := by
    have h := ((hlog.neg).const_mul C).add (hp'.const_mul 4)
    convert h using 1 <;> ext b <;> ring
  apply squeeze_zero' _ _ hupper
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hb p).le
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with b hb
    exact mul_le_mul_of_nonneg_right (logarithmic_scale_count_bounds hC hb).2.le
      (Real.rpow_pos_of_pos hb.1 p).le

/-- The scale-count decay also holds for extended nonnegative bounds. -/
theorem tendsto_ofReal_logarithmic_scale_count_mul_rpow {C p : ℝ}
    (hC : 0 < C) (hp : 0 < p) :
    Tendsto (fun b : ℝ => ENNReal.ofReal
      ((⌈C * (-Real.log b) + 3⌉₊ : ℝ) * b ^ p)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (tendsto_logarithmic_scale_count_mul_rpow hC hp)

end LatticeProb.LQG
