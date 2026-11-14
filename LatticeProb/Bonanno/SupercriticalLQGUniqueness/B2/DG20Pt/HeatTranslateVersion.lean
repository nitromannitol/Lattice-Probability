/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateVersion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateNormalized
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_exists_translated_heat_family
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) (a : ℂ) :
    let g : Ω → DistC := fun ω =>
      addConst (affineComp 1 a (h ω)) (-circleAvg (h ω) 1 a)
    ∃ Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ ε, IsHeatSmoothing P g ε (Y ε)) ∧
      ∀ ε : Ioi (0 : ℝ), ∀ᵐ ω ∂P, ∀ z,
        Y ε ω z = X ε ω (z + a) - circleAvg (h ω) 1 a := by
  dsimp
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 a (h ω)) (-circleAvg (h ω) 1 a)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (dg20_heat_translate_normalized P h hh a 1 one_pos).1
  have hchoice : ∀ ε : Ioi (0 : ℝ), ∃ Z : Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ z, Z ω z = heatMollify ε (g ω) z) ∧
      IsHeatSmoothing P g ε Z := by
    intro ε
    exact exists_heatVersion hg ε ε.property
  let Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun ε => (hchoice ε).choose
  refine ⟨Y, (fun ε => (hchoice ε).choose_spec.2), ?_⟩
  intro ε
  have hYeq := (hchoice ε).choose_spec.1
  have hXeq := dg20_heat_smoothing_ae_heatMollify P h hh ε (X ε) (hX ε)
  have htr := (dg20_heat_translate_normalized P h hh a ε ε.property).2
  filter_upwards [hYeq, hXeq, htr] with ω hYω hXω htrω
  intro z
  rw [hYω z, htrω z, hXω (z + a)]

end SupercriticalLQGUniqueness.B2.DG20Pt
