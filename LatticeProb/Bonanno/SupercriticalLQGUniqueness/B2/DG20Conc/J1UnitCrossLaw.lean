/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1UnitCrossLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UnitCompact
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFieldScale

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_unit_cross_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ) (i : Bool) (c : ℂ)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | crossLenIn ξ (fun z => phiMN W P K n
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
      (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) ∈ S} =
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - K) z ω)
      (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) ∈ S} := by
  have hφ := isPhiVersion_phiMN hW hKn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - K))
  have hc : Continuous (fun z : ℂ =>
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) := by fun_prop
  apply measure_crossLenIn_eq (j1_unit_cross_isCompact i)
    (fun ω => (hφ.cont ω).comp hc)
    (fun z => hφ.meas _)
    hφ0.cont hφ0.meas
    ?_ hS
  simpa only [Function.comp_def, Circle.coe_one, one_mul, add_comm] using
    laneB_fine_field_scale_motion P W hW hKn (1 : Circle) c

end SupercriticalLQGUniqueness.B2.DG20Conc
