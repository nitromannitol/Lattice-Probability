/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48LocalTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ThickLocal
import Mathlib.Probability.Independence.Basic

/-!
# Joint local-law transfer for Proposition 4.8

Equality in law of the restricted 0-cone and normalized whole-plane fields
extends to an independent IG coordinate. A measurable reconstruction then
transports any local configuration observable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MatedCRTHarmonic.GMS4

/-- The same product-law argument when the frozen IG phase and cone field are
only almost-everywhere measurable. -/
theorem prop48_jointLocalLaw_of_indep_ae
    {Ω₀ Ω₁ A B : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    [MeasurableSpace A] [MeasurableSpace B]
    {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {f₀ : Ω₀ → A} {f₁ : Ω₁ → A} {g₀ : Ω₀ → B} {g₁ : Ω₁ → B}
    (hf₀ : AEMeasurable f₀ P₀) (hf₁ : AEMeasurable f₁ P₁)
    (hg₀ : AEMeasurable g₀ P₀) (hg₁ : AEMeasurable g₁ P₁)
    (hfield : P₀.map f₀ = P₁.map f₁)
    (hIG : P₀.map g₀ = P₁.map g₁)
    (hind₀ : IndepFun f₀ g₀ P₀) (hind₁ : IndepFun f₁ g₁ P₁) :
    P₀.map (fun ω => (f₀ ω, g₀ ω)) =
      P₁.map (fun ω => (f₁ ω, g₁ ω)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map hf₀ hg₀).1 hind₀,
    (indepFun_iff_map_prod_eq_prod_map_map hf₁ hg₁).1 hind₁,
    hfield, hIG]

end MatedCRTHarmonic.GMS4

