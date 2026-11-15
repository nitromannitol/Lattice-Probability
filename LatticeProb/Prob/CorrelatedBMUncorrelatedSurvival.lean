import LatticeProb.Prob.CorrelatedBMIndependentHalves
import LatticeProb.Prob.CorrelatedBMJointWindowTransfer
import LatticeProb.Prob.CorrelatedBMWindowSurvival

/-! # Joint survival for independent Brownian coordinates -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- At zero correlation, the two coordinate barriers are independent and
satisfy the product of the one-dimensional survival estimates. -/
theorem measure_jointZeroBarrier_sqrt_two_le {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) {q h : ℝ}
    (hq : 0 ≤ q) (hh : 0 < h) :
    μ (jointZeroBarrier q h) ≤ ENNReal.ofReal (3 * q / Real.sqrt h) ^ 2 := by
  let W : Fin 2 → Path2 → ℝ≥0 → ℝ := fun i ω s => halfPath (i, true) s ω
  let A : Fin 2 → Set Path2 := fun i =>
    {ω | ∀ t ∈ Icc 0 h, -q ≤ coneIncr i t 0 ω}
  have hA (i : Fin 2) : MeasurableSet[MeasurableSpace.comap (W i) inferInstance] (A i) := by
    let : MeasurableSpace Path2 := MeasurableSpace.comap (W i) inferInstance
    have heval (t : ℝ) (ht : 0 ≤ t) :
        Measurable (fun ω : Path2 => lrCoord i t ω) := by
      have hm := (measurable_pi_apply t.toNNReal).comp (comap_measurable (W i))
      simpa [Function.comp_def, W, halfPath, halfTime, Real.coe_toNNReal _ ht] using hm
    apply measurableSet_closedBarrier_of_local_evaluations
      (fun ω t => coneIncr i t 0 ω) (fun _ => -q) hh.le
    · intro ω
      unfold coneIncr lrCoord
      split_ifs <;> fun_prop
    · intro t ht
      exact (heval t ht.1).sub (heval 0 le_rfl)
    · exact measurable_const
  have hind : IndepFun (W 0) (W 1) μ := by
    exact (iIndepFun_halfPath hμ).indepFun (by decide : ((0 : Fin 2), true) ≠ ((1 : Fin 2), true))
  have hindSet : IndepSet (A 0) (A 1) μ :=
    ProbabilityTheory.Indep.indepSet_of_measurableSet hind (hA 0) (hA 1)
  have hprod : μ (A 0 ∩ A 1) = μ (A 0) * μ (A 1) :=
    ProbabilityTheory.IndepSet.measure_inter_eq_mul hindSet
  change μ (A 0 ∩ A 1) ≤ _
  rw [hprod, pow_two]
  apply mul_le_mul'
  · simpa only [A, zero_add] using measure_forward_window_survival_le hμ 0 0 hh hq
  · simpa only [A, zero_add] using measure_forward_window_survival_le hμ 1 0 hh hq

/-- At unit time, the joint barrier probability has quadratic decay, uniformly
in the law of the uncorrelated Brownian pair. -/
theorem measure_jointZeroBarrier_sqrt_two_unit_le {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) {q : ℝ} (hq : 0 ≤ q) :
    μ (jointZeroBarrier q 1) ≤ ENNReal.ofReal (9 * q ^ (2 : ℝ)) := by
  have h := measure_jointZeroBarrier_sqrt_two_le hμ hq (h := 1) (by norm_num)
  rw [Real.sqrt_one, div_one, ← ENNReal.ofReal_pow (by positivity)] at h
  convert h using 1
  congr 1
  rw [Real.rpow_two]
  ring

end LatticeProb.CorrelatedBM
