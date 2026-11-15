import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Map

/-! # Measurable realization through a standard Borel parametrization -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A coded map has a measurable version when almost all its values lie in a
measurably parametrized standard Borel family on which the code is injective. -/
theorem exists_measurable_ae_eq_of_standardBorel_parametrization
    {Ω G C E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace C] [MeasurableSpace.CountablySeparated C]
    [MeasurableSpace E] [StandardBorelSpace E]
    {μ : Measure Ω} (x : Ω → G) (q : G → C) (g₀ : G) (e : E → G)
    (hq : Measurable q) (he : Measurable e)
    (hinj : Function.Injective (q ∘ e))
    (hcode : AEMeasurable (q ∘ x) μ)
    (hfamily : ∀ᵐ ω ∂μ, x ω ∈ Set.range e) :
    ∃ f : Ω → G, Measurable f ∧ f =ᵐ[μ] x := by
  have hemb : MeasurableEmbedding (q ∘ e) :=
    (hq.comp he).measurableEmbedding hinj
  obtain ⟨d, hd, hde⟩ := hemb.exists_measurable_extend he (fun _ => ⟨g₀⟩)
  refine ⟨d ∘ hcode.mk (q ∘ x), hd.comp hcode.measurable_mk, ?_⟩
  filter_upwards [hfamily, hcode.ae_eq_mk] with ω hω hωcode
  obtain ⟨t, ht⟩ := hω
  change d (hcode.mk (q ∘ x) ω) = x ω
  rw [← hωcode, ← ht]
  simpa only [Function.comp_apply, ht] using congrFun hde t

end LatticeProb
