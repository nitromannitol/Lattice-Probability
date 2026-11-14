/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFineLongFiniteTail at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareFieldSplit
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
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitLong

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

theorem laneB_fine_long_finite_tail
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ p Cneg cNeg Cpos cPos : ℝ}
    (hunit : LaneA2UnitTails.{u} ξ p Cneg cNeg Cpos cPos)
    (K n : ℕ) (hKn : K ≤ n)
    {ι : Type*} (J : Finset ι) (rot : ι → Circle) (center : ι → ℂ)
    (T : ℝ) (hT : 3 < T) :
    P {ω | ∃ j ∈ J,
      T * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
        ellN ξ W P (n - K) (ENNReal.ofReal p) *
          (2 : ℝ)⁻¹ ^ K <
        T20B.mrectLen ξ (fun z => phiMN W P K n z ω)
          K (rot j) (center j) 3 1} ≤
      J.card * ENNReal.ofReal (Cpos * Real.exp
        (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  let v : ℝ := T * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
    ellN ξ W P (n - K) (ENNReal.ofReal p)
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have hset : {ω : Ω | ∃ j ∈ J,
      v * (2 : ℝ)⁻¹ ^ K <
        T20B.mrectLen ξ (fun z => phiMN W P K n z ω)
          K (rot j) (center j) 3 1} =
      ⋃ j ∈ J, {ω | T20B.mrectLen ξ
        (fun z => phiMN W P K n z ω) K (rot j) (center j) 3 1 ∈
          Set.Ioi (v * (2 : ℝ)⁻¹ ^ K)} := by
    ext ω
    simp
  change P {ω | ∃ j ∈ J, v * (2 : ℝ)⁻¹ ^ K <
    T20B.mrectLen ξ (fun z => phiMN W P K n z ω)
      K (rot j) (center j) 3 1} ≤ _
  rw [hset]
  refine (measure_biUnion_finset_le J _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro j hj
  rw [T20B.law_mrectLen (ξ := ξ) hW hKn (rot j) (center j)
    3 1 measurableSet_Ioi]
  have heq : {ω : Ω |
      (2 : ℝ)⁻¹ ^ K * lenObs ξ (phiMN W P 0 (n - K))
        (rectAB 3 1) ω ∈ Set.Ioi (v * (2 : ℝ)⁻¹ ^ K)} =
      {ω : Ω | v < lenObs ξ (phiMN W P 0 (n - K))
        (rectAB 3 1) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
    rw [mul_comm v, mul_lt_mul_iff_right₀ hr]
  rw [heq]
  exact (hunit P W hW (n - K) T hT).2

end SupercriticalLQGUniqueness.B2.DG20Conc
