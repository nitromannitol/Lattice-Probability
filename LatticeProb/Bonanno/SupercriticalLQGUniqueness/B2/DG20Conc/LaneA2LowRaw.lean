/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowRaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowQuantile
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Motion3

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

theorem laneA2_low_raw {ξ p C A : ℝ} (hW : IsWhiteNoise P W)
    (htail : ∀ (m : ℕ), m ≤ 2 → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
      a ≤ 1 → b ≤ 1 → ∀ (M : ℝ), 0 < M →
      P {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} ≤
        ENNReal.ofReal (C * Real.exp (-(M / A)^2 / Real.log 4)))
    (m : ℕ) (hm : m ≤ 2) (B T M : ℝ) (hM : 0 < M)
    (hneg : (B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p) ≤
      (1/8) * Real.exp (-(|ξ| * M)))
    (hpos : (3/8) * Real.exp (|ξ| * M) ≤
      T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p))
    (v : Circle) (c : ℂ) :
    P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 1 3 <
      (B^4 * T)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
      ENNReal.ofReal (C * Real.exp (-(M / A)^2 / Real.log 4)) ∧
    P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 3 v c 3 1} ≤
      ENNReal.ofReal (C * Real.exp (-(M / A)^2 / Real.log 4)) := by
  constructor
  · change P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
      3 v c 1 3 ∈ Set.Iio ((B^4 * T)⁻¹ *
        ellN ξ W P m (ENNReal.ofReal p))} ≤ _
    rw [laneA2_mrectLen_law_three hW m v c 1 3 measurableSet_Iio]
    simp only [mul_one]
    have he : (1/8 : ℝ) * 3 = 3/8 := by norm_num
    rw [he]
    apply (measure_mono ?_).trans
      (htail m hm (1/8) (3/8) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) M hM)
    intro ω hω
    by_contra hnot
    change ¬ M < ⨆ z : (rectAB (1/8) (3/8)).toSet,
      |phiMN W P 0 m z ω| at hnot
    have hnot' := le_of_not_gt hnot
    have hg := laneA2_short_length_of_sup (ξ := ξ) hW m ω M hnot'
    exact (not_lt_of_ge (hneg.trans hg)) hω
  · change P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
      3 v c 3 1 ∈ Set.Ioi (T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p))} ≤ _
    rw [laneA2_mrectLen_law_three hW m v c 3 1 measurableSet_Ioi]
    simp only [mul_one]
    have he : (1/8 : ℝ) * 3 = 3/8 := by norm_num
    rw [he]
    apply (measure_mono ?_).trans
      (htail m hm (3/8) (1/8) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) M hM)
    intro ω hω
    by_contra hnot
    change ¬ M < ⨆ z : (rectAB (3/8) (1/8)).toSet,
      |phiMN W P 0 m z ω| at hnot
    have hg := laneA2_long_length_of_sup (ξ := ξ) hW m ω M (le_of_not_gt hnot)
    exact (not_lt_of_ge (hg.trans hpos)) hω

end SupercriticalLQGUniqueness.B2.DG20Conc
