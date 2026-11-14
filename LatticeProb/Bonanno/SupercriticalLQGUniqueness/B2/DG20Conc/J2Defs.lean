/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 










set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.J2Defs

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

def QuantileRatioAllP : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ p : ℝ, 0 < p → p < 2⁻¹ → ∃ B : ℝ,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ n : ℕ, LambdaN (ξ : ℝ) W P n (ENNReal.ofReal p) ≤ B

 
theorem dg20QuantileRatio_of_allP (h : QuantileRatioAllP) : Iface.DG20QuantileRatio := by
  intro ξ
  obtain ⟨B, hB⟩ := h ξ (1 / 4) (by norm_num) (by norm_num)
  refine ⟨⟨1 / 4, by norm_num, by norm_num⟩, max B 1, lt_max_of_lt_right one_pos, ?_⟩
  intro Ω _ P _ W hW n
  exact (hB P W hW n).trans (le_max_left _ _)

end SupercriticalLQGUniqueness.B2.DG20Conc.J2Defs
