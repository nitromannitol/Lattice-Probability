import LatticeProb.LQG.ShiftedSideStrictMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters

/-! # Shifted strict sides in mating-of-trees couplings -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A coupling sample and an independent absolutely continuous phase almost surely
satisfy the strict side conditions at a fixed positive mesh. -/
theorem ae_prod_shifted_sideStrict_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∀ᵐ p ∂P.prod Q, RouteM.SideStrict ε
      ⟨fun t => bm p.1 (t + p.2), (bm p.1).continuous.comp (by fun_prop)⟩ := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hm : Measurable (fun p : Ω × ℝ => (bm p.1, p.2)) :=
    (D.measurable_curves.2.2.2.comp measurable_fst).prodMk measurable_snd
  have hs := (RouteM.measurableSet_shifted_sideStrict ε).preimage hm
  apply (Measure.ae_prod_iff_ae_ae hs).2
  have hb := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
    (RouteM.ae_sideStrict_time_translate_of_correlatedBM D.boundaryLawBM hε)
  filter_upwards [hb, ae_peanosphere D] with ω hb hp
  exact hQ.ae_le (hb (η ω) hp)

end MatedCRTHarmonic.MoTInput
