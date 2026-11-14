/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBQuantileSandwich at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Window

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneB_quantile_sandwich
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ p : ℝ) (hp0 : 0 < p) (hp : p < 2⁻¹) (m : ℕ) :
    let K := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p
    Real.exp (-K * Real.sqrt m) * lambdaN ξ W P m ≤
      ellN ξ W P m (ENNReal.ofReal p) ∧
    ellBarN ξ W P m (ENNReal.ofReal p) ≤
      Real.exp (K * Real.sqrt m) * lambdaN ξ W P m ∧
    LambdaN ξ W P m (ENNReal.ofReal p) ≤
      Real.exp (K * Real.sqrt m) := by
  letI := hW.isProbabilityMeasure
  dsimp
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hq0 : 0 < q := ENNReal.ofReal_pos.mpr hp0
  have hqhalf : q ≤ 2⁻¹ := by
    have heq : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal (by norm_num at hp ⊢; linarith)
  have hq1 : q < 1 := hqhalf.trans_lt (by norm_num)
  have hlow : 0 < ellN ξ W P m q := T20B.ellN_pos hW hq0 hq1 m
  have hLoMed : ellN ξ W P m q ≤ lambdaN ξ W P m :=
    T20B.ellN_le_lambdaN hq0 hqhalf m
  have hMedHi : lambdaN ξ W P m ≤ ellBarN ξ W P m q :=
    T20B.lambdaN_le_ellBarN hq0 hqhalf m
  let K : ℝ := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p
  let e : ℝ := Real.exp (K * Real.sqrt m)
  have he : 0 < e := Real.exp_pos _
  have hΛ : LambdaN ξ W P m q ≤ e :=
    Exponent.Inputs.Gaussian.quantile_ratio_sqrt hW ξ hp0
      (by simpa only [inv_eq_one_div] using hp) m
  have hratio : ellBarN ξ W P m q / ellN ξ W P m q ≤ e := by
    have hpoint : ellBarN ξ W P m q / ellN ξ W P m q ≤
        LambdaN ξ W P m q := Finset.le_sup'
          (fun k => ellBarN ξ W P k q / ellN ξ W P k q)
          (Finset.mem_range.mpr (Nat.lt_succ_self m))
    exact hpoint.trans hΛ
  have hHiLo : ellBarN ξ W P m q ≤ e * ellN ξ W P m q :=
    (div_le_iff₀ hlow).mp hratio
  have hMedLo : lambdaN ξ W P m ≤ e * ellN ξ W P m q :=
    hMedHi.trans hHiLo
  refine ⟨?_, ?_, hΛ⟩
  · change Real.exp (-K * Real.sqrt m) * lambdaN ξ W P m ≤ ellN ξ W P m q
    calc
      Real.exp (-K * Real.sqrt m) * lambdaN ξ W P m =
          lambdaN ξ W P m / e := by
            rw [show -K * Real.sqrt m = -(K * Real.sqrt m) by ring, Real.exp_neg]
            simp only [e, div_eq_mul_inv, mul_comm]
      _ ≤ ellN ξ W P m q := (div_le_iff₀ he).mpr (by simpa [mul_comm] using hMedLo)
  · change ellBarN ξ W P m q ≤ Real.exp (K * Real.sqrt m) * lambdaN ξ W P m
    exact hHiLo.trans (mul_le_mul_of_nonneg_left hLoMed he.le)

end SupercriticalLQGUniqueness.B2.DG20Conc
