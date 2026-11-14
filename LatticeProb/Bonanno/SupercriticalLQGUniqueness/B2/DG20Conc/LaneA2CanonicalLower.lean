/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CanonicalLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CoarseSup

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

theorem laneA2_canonical_lower_of_unit_tail {ξ p Cneg cNeg : ℝ}
    (htail : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (m : ℕ) (T : ℝ), 3 < T →
        P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
          T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (hm : 3 ≤ m) (M : ℝ) (hM : 0 < M)
        (T : ℝ) (hT : 3 < T),
        P {ω | lenObs ξ (phiMN W P 0 m) (rectAB (1 / 8) (3 / 8)) ω <
          Real.exp (-(|ξ| * M)) *
            ((1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p))} ≤
          ENNReal.ofReal (C * Real.exp (-((M / A)^2 * 3 / Real.log 4))) +
          ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) := by
  obtain ⟨C, A, hC, hA, hcoarse⟩ := laneA2_coarse_sup_three
  refine ⟨C, A, hC, hA, ?_⟩
  intro Ω _ P W hW m hm M hM T hT
  have hsplit := laneA2_dyadic_lower_split (ξ := ξ) hW hm
    (a := 1 / 8) (b := 3 / 8) (by norm_num) (by norm_num) M
    ((1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p))
  have hc := hcoarse P W hW (1 / 8) (3 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) M hM
  have hfine : P {ω | lenObs ξ (phiMN W P 3 m) (rectAB (1 / 8) (3 / 8)) ω <
      (1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p)} ≤
      ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) := by
    have hscale := laneA2_fine_scale_three (ξ := ξ) hW hm 1 3
      (S := Set.Iio ((1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p)))
      measurableSet_Iio
    simp only [mul_one] at hscale
    have he : (1 / 8 : ℝ) * (3 : ℝ) = 3 / 8 := by norm_num
    rw [he] at hscale
    change P {ω | lenObs ξ (phiMN W P 3 m) (rectAB (1 / 8) (3 / 8)) ω ∈
        Set.Iio ((1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p))} ≤ _
    rw [hscale]
    have hsets : {ω | (1 / 8 : ℝ) *
        lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 1 3) ω <
        (1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p)} ⊆
        {ω | lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 1 3) ω <
          T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p)} := by
      intro ω hω
      have hω' : (1 / 8 : ℝ) *
          lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 1 3) ω <
          (1 / 8) * (T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p)) := by
        change (1 / 8 : ℝ) *
          lenObs ξ (phiMN W P 0 (m - 3)) (rectAB 1 3) ω <
          (1 / 8) * T⁻¹ * ellN ξ W P (m - 3) (ENNReal.ofReal p) at hω
        convert hω using 1 <;> ring
      exact lt_of_mul_lt_mul_left hω' (by norm_num : (0 : ℝ) ≤ 1 / 8)
    exact (measure_mono hsets).trans (htail (Ω := Ω) P W hW (m - 3) T hT)
  exact hsplit.trans (add_le_add hc hfine)

end SupercriticalLQGUniqueness.B2.DG20Conc
