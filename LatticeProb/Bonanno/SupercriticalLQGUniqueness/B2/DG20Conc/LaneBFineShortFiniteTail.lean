/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFineShortFiniteTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFineLongFiniteTail

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

theorem laneB_fine_short_finite_tail
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ p Cneg cNeg Cpos cPos : ℝ}
    (hunit : LaneA2UnitTails.{u} ξ p Cneg cNeg Cpos cPos)
    (K n : ℕ) (hKn : K ≤ n)
    {ι : Type*} (J : Finset ι) (rot : ι → Circle) (center : ι → ℂ)
    (T : ℝ) (hT : 3 < T) :
    P {ω | ∃ j ∈ J,
        T20B.mrectLen ξ (fun z => phiMN W P K n z ω)
          K (rot j) (center j) 1 3 <
          T⁻¹ * ellN ξ W P (n - K) (ENNReal.ofReal p) *
            (2 : ℝ)⁻¹ ^ K} ≤
      J.card * ENNReal.ofReal (Cneg * Real.exp
        (-cNeg * (Real.log T)^2)) := by
  let v : ℝ := T⁻¹ * ellN ξ W P (n - K) (ENNReal.ofReal p)
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have hset : {ω : Ω | ∃ j ∈ J,
      T20B.mrectLen ξ (fun z => phiMN W P K n z ω)
        K (rot j) (center j) 1 3 < v * (2 : ℝ)⁻¹ ^ K} =
      ⋃ j ∈ J, {ω | T20B.mrectLen ξ
        (fun z => phiMN W P K n z ω) K (rot j) (center j) 1 3 ∈
          Set.Iio (v * (2 : ℝ)⁻¹ ^ K)} := by
    ext ω
    simp
  change P {ω | ∃ j ∈ J,
    T20B.mrectLen ξ (fun z => phiMN W P K n z ω)
      K (rot j) (center j) 1 3 < v * (2 : ℝ)⁻¹ ^ K} ≤ _
  rw [hset]
  refine (measure_biUnion_finset_le J _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro j hj
  rw [T20B.law_mrectLen (ξ := ξ) hW hKn (rot j) (center j)
    1 3 measurableSet_Iio]
  have heq : {ω : Ω |
      (2 : ℝ)⁻¹ ^ K * lenObs ξ (phiMN W P 0 (n - K))
        (rectAB 1 3) ω ∈ Set.Iio (v * (2 : ℝ)⁻¹ ^ K)} =
      {ω : Ω | lenObs ξ (phiMN W P 0 (n - K))
        (rectAB 1 3) ω < v} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_Iio]
    rw [mul_comm v, mul_lt_mul_iff_right₀ hr]
  rw [heq]
  exact (hunit P W hW (n - K) T hT).1

end SupercriticalLQGUniqueness.B2.DG20Conc
