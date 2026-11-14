/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RectLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UnitCrossLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_mrectLen_field_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ) (k : ℕ)
    (u : Circle) (d c : ℂ) (a b : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | T20B.mrectLen ξ (fun z => phiMN W P K n
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω) k u d a b ∈ S} =
    P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 (n - K) z ω)
      k u d a b ∈ S} := by
  have hφ := isPhiVersion_phiMN hW hKn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - K))
  have hc : Continuous (fun z : ℂ =>
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) := by fun_prop
  have hK : IsCompact (T20B.mot k u d '' (rectAB a b).toSet) :=
    (rectAB a b).isCompact_toSet.image (by unfold T20B.mot; fun_prop)
  unfold T20B.mrectLen
  apply measure_crossLenIn_eq hK
    (fun ω => (hφ.cont ω).comp hc) (fun z => hφ.meas _)
    hφ0.cont hφ0.meas ?_ (ENNReal.measurable_toReal hS)
  simpa only [Function.comp_def, Circle.coe_one, one_mul, add_comm] using
    laneB_fine_field_scale_motion P W hW hKn (1 : Circle) c

end SupercriticalLQGUniqueness.B2.DG20Conc
