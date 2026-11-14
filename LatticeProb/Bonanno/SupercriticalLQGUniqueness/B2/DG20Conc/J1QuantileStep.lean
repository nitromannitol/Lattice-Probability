/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1QuantileStep at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Zero
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2QuantileBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Bridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteExitMeet
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom
import Mathlib.Data.Fintype.EquivFin
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BBlocks
import Mathlib.Data.Int.Interval
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineCross

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_quantile_sandwich_of_induction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ξ : ℝ) {p B : ℝ} (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    {m : ℕ} (hH : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B) :
    lambdaN ξ W P m ≤ B * ellN ξ W P m (ENNReal.ofReal p) ∧
    LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) ≤
      B * lambdaN ξ W P m := by
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hlow := laneA2_lambdaN_le_B_ellN P hW ξ hp hpHalf hH
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.mpr hp
  have hpq : ENNReal.ofReal p ≤ (2⁻¹ : ℝ≥0∞) := by
    have he : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hpHalf
  have hmed : ellN ξ W P m (ENNReal.ofReal p) ≤ lambdaN ξ W P m :=
    T20B.ellN_le_lambdaN hpq0 hpq m
  have hℓ0 : 0 ≤ ellN ξ W P m (ENNReal.ofReal p) :=
    (T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq (by norm_num)) m).le
  have hB0 : 0 ≤ B := by
    have hratio : 0 ≤ LambdaN ξ W P m (ENNReal.ofReal p) :=
      (T20B.LambdaN_pos hW hpq0 hpq m).le
    linarith
  constructor
  · exact hlow
  · exact (mul_le_mul_of_nonneg_right hH hℓ0).trans
      (mul_le_mul_of_nonneg_left hmed hB0)

theorem j1_lower_threshold_of_quantile
    {ell lam B T : ℝ} (hB : 0 < B) (hT : 0 < T)
    (hmed : lam ≤ B * ell) :
    T⁻¹ * lam ≤ (T / B)⁻¹ * ell := by
  have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  have h := mul_le_mul_of_nonneg_left hmed hTinv
  calc
    _ ≤ T⁻¹ * (B * ell) := h
    _ = (T / B)⁻¹ * ell := by field_simp [hB.ne', hT.ne']

theorem j1_upper_threshold_of_quantile
    {upper lam B T : ℝ} (hB : 0 < B) (hT : 0 < T)
    (hupper : upper ≤ B * lam) :
    (T / B) * upper ≤ T * lam := by
  have hTB : 0 ≤ T / B := (div_pos hT hB).le
  have h := mul_le_mul_of_nonneg_left hupper hTB
  calc
    _ ≤ (T / B) * (B * lam) := h
    _ = T * lam := by field_simp [hB.ne']

end SupercriticalLQGUniqueness.B2.DG20Conc
