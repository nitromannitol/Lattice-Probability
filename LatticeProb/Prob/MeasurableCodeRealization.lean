import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! # Measurable realization from a code -/

set_option autoImplicit false

open Filter MeasureTheory Set

namespace LatticeProb

/-- An almost everywhere measurable injective code admits a measurable realization
if its law is supported on a measurable set carrying a measurable right inverse. -/
theorem exists_measurable_ae_eq_of_code_decoder
    {Ω G C : Type*} [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace C]
    {μ : Measure Ω} (x : Ω → G) (q : G → C) (g₀ : G)
    (hq : Function.Injective q) (hcode : AEMeasurable (q ∘ x) μ)
    (B : Set C) (hB : MeasurableSet B) (hfull : μ.map (q ∘ x) Bᶜ = 0)
    (d : B → G) (hd : Measurable d) (hinv : ∀ c : B, q (d c) = c.1) :
    ∃ f : Ω → G, Measurable f ∧ f =ᵐ[μ] x := by
  obtain ⟨D, hD, hDeq⟩ :=
    (MeasurableEmbedding.subtype_coe hB).exists_measurable_extend hd (fun _ => ⟨g₀⟩)
  have hmem : ∀ᵐ ω ∂μ, (q ∘ x) ω ∈ B := by
    apply ae_of_ae_map hcode
    exact (ae_iff).2 hfull
  refine ⟨D ∘ hcode.mk (q ∘ x), hD.comp hcode.measurable_mk, ?_⟩
  filter_upwards [hmem, hcode.ae_eq_mk] with ω hω heq
  apply hq
  have hext : D ((q ∘ x) ω) = d ⟨(q ∘ x) ω, hω⟩ :=
    congrFun hDeq ⟨(q ∘ x) ω, hω⟩
  change q (D (hcode.mk (q ∘ x) ω)) = q (x ω)
  rw [← heq, hext]
  exact hinv ⟨(q ∘ x) ω, hω⟩

end LatticeProb
