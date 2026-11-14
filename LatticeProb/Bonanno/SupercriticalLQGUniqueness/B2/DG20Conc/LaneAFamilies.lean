/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneAFamilies at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ} {ξ p C c : ℝ}

 

theorem laneA_short_family_tail (hW : IsWhiteNoise P W)
    (hlow : ∀ (m : ℕ) (T : ℝ), 3 < T →
      P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
        T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (C * Real.exp (-c * (Real.log T)^2)))
    (m : ℕ) {ι : Type*} (J : Finset ι) (u : ι → Circle) (cc : ι → ℂ)
    (T : ℝ) (hT : 3 < T) :
    P {ω | ∃ j ∈ J,
      T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 0 (u j) (cc j) 1 3 <
        T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
      J.card * ENNReal.ofReal (C * Real.exp (-c * (Real.log T)^2)) := by
  let v := T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)
  have hevent : {ω | ∃ j ∈ J,
      T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 0 (u j) (cc j) 1 3 < v} =
      ⋃ j ∈ J, {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
        0 (u j) (cc j) 1 3 ∈ Set.Iio v} := by
    ext ω; simp
  change P {ω | ∃ j ∈ J,
      T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 0 (u j) (cc j) 1 3 < v} ≤ _
  rw [hevent]
  refine (measure_biUnion_finset_le J _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [T20B.law_mrectLen hW (Nat.zero_le m) (u j) (cc j) 1 3 measurableSet_Iio]
  simpa only [Nat.sub_zero, pow_zero, one_mul, Set.mem_Iio, v] using hlow m T hT

 

theorem laneA_long_family_tail (hW : IsWhiteNoise P W)
    (hupp : ∀ (m : ℕ) (T : ℝ), 3 < T →
      P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C * Real.exp
          (-c * (Real.log T)^2 / Real.log (Real.log T))))
    (m : ℕ) {ι : Type*} (J : Finset ι) (u : ι → Circle) (cc : ι → ℂ)
    (T : ℝ) (hT : 3 < T) :
    P {ω | ∃ j ∈ J,
      T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 0 (u j) (cc j) 3 1} ≤
      J.card * ENNReal.ofReal (C * Real.exp
        (-c * (Real.log T)^2 / Real.log (Real.log T))) := by
  let v := T * LambdaN ξ W P m (ENNReal.ofReal p) *
    ellN ξ W P m (ENNReal.ofReal p)
  have hevent : {ω | ∃ j ∈ J, v <
      T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 0 (u j) (cc j) 3 1} =
      ⋃ j ∈ J, {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
        0 (u j) (cc j) 3 1 ∈ Set.Ioi v} := by
    ext ω; simp
  change P {ω | ∃ j ∈ J, v <
      T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω) 0 (u j) (cc j) 3 1} ≤ _
  rw [hevent]
  refine (measure_biUnion_finset_le J _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [T20B.law_mrectLen hW (Nat.zero_le m) (u j) (cc j) 3 1 measurableSet_Ioi]
  simpa only [Nat.sub_zero, pow_zero, one_mul, Set.mem_Ioi, v] using hupp m T hT

end SupercriticalLQGUniqueness.B2.DG20Conc
