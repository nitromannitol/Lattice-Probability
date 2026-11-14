/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BoundedRange

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_cross_range_extension
    (A C CN cN : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hCN : 0 < CN) (hcN : 0 < cN) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (K : ℕ) (hK : 64 ≤ K)
        (T : ℝ) (hT : 3 < T) (E : Set Ω),
        (Real.exp (A * (C + 1) * Real.sqrt ((K : ℝ) + 1)) ≤ T →
          P E ≤ ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2))) →
          P E ≤ ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (C' * Real.exp (-c' * (Real.log T)^2)) := by
  obtain ⟨d, hd, hbounded⟩ := j1_bounded_sqrt_range hA hC
  refine ⟨CN + 1, min cN d, by linarith, lt_min hcN hd, ?_⟩
  intro Ω _ P _ K hK T hT E hhigh
  have hq : 0 ≤ (Real.log T)^2 := sq_nonneg _
  have h5 : 0 ≤ (5 : ℝ)^K := by positivity
  have hrateN : CN * Real.exp (-cN * (Real.log T)^2) ≤
      (CN + 1) * Real.exp (-(min cN d) * (Real.log T)^2) := by
    have he : Real.exp (-cN * (Real.log T)^2) ≤
        Real.exp (-(min cN d) * (Real.log T)^2) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left cN d])
    calc
      _ ≤ CN * Real.exp (-(min cN d) * (Real.log T)^2) :=
          mul_le_mul_of_nonneg_left he hCN.le
      _ ≤ (CN + 1) * Real.exp (-(min cN d) * (Real.log T)^2) := by
          nlinarith [Real.exp_pos (-(min cN d) * (Real.log T)^2)]
  have hrateD : (5 : ℝ)^K * Real.exp (-d * (Real.log T)^2) ≤
      (5 : ℝ)^K * ((CN + 1) *
        Real.exp (-(min cN d) * (Real.log T)^2)) := by
    have he : Real.exp (-d * (Real.log T)^2) ≤
        Real.exp (-(min cN d) * (Real.log T)^2) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_right cN d])
    have hcoef : Real.exp (-d * (Real.log T)^2) ≤
        (CN + 1) * Real.exp (-(min cN d) * (Real.log T)^2) := by
      nlinarith [Real.exp_pos (-(min cN d) * (Real.log T)^2)]
    exact mul_le_mul_of_nonneg_left hcoef h5
  by_cases hbig : Real.exp (A * (C + 1) *
      Real.sqrt ((K : ℝ) + 1)) ≤ T
  · exact (hhigh hbig).trans
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrateN)
        (zero_le : (0 : ℝ≥0∞) ≤ _))
  · have hsmall : T ≤ Real.exp (A * (C + 1) *
        Real.sqrt ((K : ℝ) + 1)) := le_of_lt (lt_of_not_ge hbig)
    have h1 := hbounded K (by omega) T hT hsmall
    have h1' : 1 ≤ (5 : ℝ)^K * ((CN + 1) *
        Real.exp (-(min cN d) * (Real.log T)^2)) := h1.trans hrateD
    have hENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal ((CN + 1) *
          Real.exp (-(min cN d) * (Real.log T)^2)) := by
      rw [← ENNReal.ofReal_one]
      calc
        ENNReal.ofReal (1 : ℝ) ≤
            ENNReal.ofReal ((5 : ℝ)^K * ((CN + 1) *
              Real.exp (-(min cN d) * (Real.log T)^2))) :=
                ENNReal.ofReal_le_ofReal h1'
        _ = _ := ENNReal.ofReal_mul h5
    exact (prob_le_one).trans hENN

end SupercriticalLQGUniqueness.B2.DG20Conc
