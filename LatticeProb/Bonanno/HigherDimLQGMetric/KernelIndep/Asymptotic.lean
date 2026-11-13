/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.Asymptotic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Transfer
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.GenericSup
import LatticeProb.Bonanno.HigherDimLFPP.Exist.CrudeBounds

/-! Sublinear growth of the fixed-variance Gaussian supremum estimate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Real
namespace HigherDimLQGMetric

theorem sqrt_affine_div_tendsto_zero (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Tendsto (fun x : ℝ => Real.sqrt (A + B * x) / x) atTop (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt (A + B) / Real.sqrt x) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul
      (Real.sqrt (A + B))
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have harg : A + B * x ≤ (A + B) * x := by nlinarith
    have hroot := Real.sqrt_le_sqrt harg
    rw [Real.sqrt_mul (by positivity : 0 ≤ A + B)] at hroot
    have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    apply (div_le_div_of_nonneg_right hroot hx0.le).trans_eq
    rw [div_eq_div_iff hx0.ne' (Real.sqrt_pos.2 hx0).ne']
    calc Real.sqrt (A + B) * Real.sqrt x * Real.sqrt x =
        Real.sqrt (A + B) * (Real.sqrt x ^ 2) := by ring
      _ = Real.sqrt (A + B) * x := by rw [hsq]

private theorem supMean_affine_div_tendsto_zero (d : ℕ) (L V A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Tendsto (fun x : ℝ => HigherDimLFPP.SupB.supMean d L V (A + B * x) / x)
      atTop (𝓝 0) := by
  have hs := sqrt_affine_div_tendsto_zero (1 + A) B (by linarith) hB
  have hi : Tendsto (fun x : ℝ => (1 / x : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have h1 := hs.const_mul (2 * Real.sqrt (V / 2))
  have h2 := hs.const_mul
    (2 * Real.sqrt (Real.pi ^ 2 * (Real.sqrt (d : ℝ) ^ 2 * L) / 8))
  have h3 := hi.const_mul (HigherDimLFPP.Osc.blockConst d L (Real.sqrt (d : ℝ)))
  convert (h1.add h2).add h3 using 1
  · funext x
    unfold HigherDimLFPP.SupB.supMean
    ring_nf
  · ring_nf

/-- The positive logarithmic scale diverges at zero. -/
theorem log_inv_tendsto_atTop :
    Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def, Real.log_inv] using
      (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)

/-- A fixed variance supremum threshold is negligible compared with `log ε⁻¹`. -/
theorem supMean_fixedVar_sublinear (d : ℕ) (L V : ℝ) :
    Tendsto (fun ε : ℝ => HigherDimLFPP.SupB.supMean d L V
      (d * Real.log (4 / ε + 1)) / Real.log ε⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hlog := log_inv_tendsto_atTop
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ (d : ℝ) * Real.log 5 := mul_nonneg (Nat.cast_nonneg _) hlog5
  have h := supMean_affine_div_tendsto_zero d L V (d * Real.log 5) d hA (Nat.cast_nonneg _)
  have hupper := h.comp hlog
  have hlow : Tendsto (fun ε : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupper ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hℓ : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 hε)
    exact div_nonneg (by
      unfold HigherDimLFPP.SupB.supMean
      have harg1 : 1 ≤ 4 / ε + 1 := by
        have hq : 0 ≤ 4 / ε := div_nonneg (by norm_num) hε.1.le
        linarith
      have hlog0 : 0 ≤ Real.log (4 / ε + 1) := Real.log_nonneg harg1
      have hblock := HigherDimLFPP.Osc.blockConst_nonneg d (L := L)
        (Real.sqrt_nonneg (d : ℝ))
      positivity) hℓ.le
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hℓ : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 hε)
    have harg : 4 / ε + 1 ≤ 5 / ε := by
      apply (le_div_iff₀ hε.1).2
      rw [add_mul, div_mul_cancel₀ _ hε.1.ne']
      linarith [hε.2.le]
    have hlg : Real.log (4 / ε + 1) ≤ Real.log 5 + Real.log ε⁻¹ := by
      calc Real.log (4 / ε + 1) ≤ Real.log (5 / ε) :=
        Real.log_le_log (by
          have hq : 0 ≤ 4 / ε := div_nonneg (by norm_num) hε.1.le
          linarith) harg
        _ = Real.log 5 + Real.log ε⁻¹ := by
          rw [div_eq_mul_inv, Real.log_mul (by norm_num : (5 : ℝ) ≠ 0)
            (inv_ne_zero hε.1.ne'), add_comm]
    apply div_le_div_of_nonneg_right _ hℓ.le
    apply HigherDimLFPP.SupB.supMean_mono d le_rfl
    nlinarith [mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.2 hlg)]

theorem supMean_plus_sqrt_sublinear (d : ℕ) (L V : ℝ) :
    Tendsto (fun ε : ℝ =>
      (HigherDimLFPP.SupB.supMean d L V (d * Real.log (4 / ε + 1)) +
        Real.sqrt (Real.log ε⁻¹)) / Real.log ε⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hs := (sqrt_affine_div_tendsto_zero 0 1 (by norm_num) (by norm_num)).comp
    log_inv_tendsto_atTop
  have h := (supMean_fixedVar_sublinear d L V).add hs
  convert h using 1
  · funext ε
    simp only [zero_add, one_mul, Function.comp_def, add_div]
  · simp

end HigherDimLQGMetric
