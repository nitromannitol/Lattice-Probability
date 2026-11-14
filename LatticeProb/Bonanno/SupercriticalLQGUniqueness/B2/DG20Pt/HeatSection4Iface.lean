/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatSection4Iface at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointIface
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatScaleIface
import LatticeProb.Bonanno.NV1Evidence

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20Section4_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive) :
    SupercriticalLQGUniqueness.B2.Iface.DG20Section4 := by
  intro ξ Q hQ m hm
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, h₀, hh₀⟩ := exists_normalizedGFF
  let X₀ (ε : Ioi (0 : ℝ)) : Ω₀ → C(ℂ, ℝ) :=
    Classical.choose (exists_heatVersion hh₀ ε ε.property)
  have hX₀ : ∀ ε, IsHeatSmoothing P₀ h₀ ε (X₀ ε) := by
    intro ε
    exact (Classical.choose_spec (exists_heatVersion hh₀ ε ε.property)).2
  have hscale := dg20Section4_scale_of_inputs
    hPerc hExp ξ Q hQ m hm P₀ h₀ hh₀ X₀ hX₀
  refine ⟨?_, hscale.1, hscale.2⟩
  intro Ω _ P _ h hh X hX U hUc z w hz hw hzw
  have hpoint := dg20Section4_point_tight_of_inputs
    hPerc hExp hPos ξ Q hQ m hm P h hh X hX U hUc z w hz hw hzw
  exact hpoint

end SupercriticalLQGUniqueness.B2.DG20Pt
