import LatticeProb.ReflectedGMS.GMS.CellConfigSupportedRealization

/-! # Measurable realizations with almost-sure line connectivity -/

set_option autoImplicit false

open Set MeasureTheory

namespace ReflectedGMS.GMS

/-- Almost-sure line connectivity suffices for the measurable realization criterion:
the second-countable support may also contain other configurations. -/
theorem exists_measurable_ae_eq_of_support_ae_lineConnected
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [SFinite μ] (H : Ω → GMSSpace)
    (T : Set GMSSpace) [SecondCountableTopology T]
    (H₀ : T) (h₀ : H₀.1.1.LineConnected)
    (hT : ∀ᵐ ω ∂μ, H ω ∈ T)
    (hL : ∀ᵐ ω ∂μ, (H ω).1.LineConnected)
    (hcode : AEMeasurable (fun ω => (H ω).1.code) μ) :
    ∃ F : Ω → GMSSpace, Measurable F ∧ F =ᵐ[μ] H := by
  let U : Set GMSSpace := {K | K ∈ T ∧ K.1.LineConnected}
  let f : U → T := fun K => ⟨K.1, K.2.1⟩
  have hf : Topology.IsInducing f :=
    Topology.IsInducing.subtypeVal.codRestrict (s := T) (fun K : U => K.2.1)
  let : SecondCountableTopology U := hf.secondCountableTopology
  apply exists_measurable_ae_eq_of_lineConnected_support μ H U ⟨H₀.1, H₀.2, h₀⟩
  · filter_upwards [hT, hL] with ω hω hωL
    exact ⟨hω, hωL⟩
  · intro K hK
    exact hK.2
  · exact hcode

end ReflectedGMS.GMS
