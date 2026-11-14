/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointIface at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenTight

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20Section4_point_tight_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive) :
    ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ m : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistC),
          IsNormalizedWholePlaneGFF h P →
          ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
            (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) →
              ∀ z w : ℂ, z ∈ U → w ∈ U → z ≠ w →
                IsTwoSidedTight P (fun (ε : Ioo (0 : ℝ) 1) ω =>
                  ENNReal.ofReal (m ⟨ε, ε.property.1⟩ : ℝ)⁻¹ *
                    crossLenIn ξ (X ⟨ε, ε.property.1⟩ ω)
                      U {z} {w}) := by
  intro ξ Q hQ m hm Ω _ P _ h hh X hX U hUc z w hz hw hzw
  exact dg20_heat_point_open_two_sided_tight_of_inputs
    hPerc hExp hPos ξ Q hQ m hm P h hh X hX
    U U.isOpen hUc z w hz hw hzw

end SupercriticalLQGUniqueness.B2.DG20Pt
