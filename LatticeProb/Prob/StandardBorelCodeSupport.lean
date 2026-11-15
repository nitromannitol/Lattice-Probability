import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Almost everywhere measurable realizations from standard Borel support -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- An almost everywhere measurable injective code determines an almost everywhere
measurable map when its values lie almost everywhere in a standard Borel subspace. -/
theorem aemeasurable_of_code_of_ae_mem_standardBorel
    {Ω G C : Type*} [MeasurableSpace Ω] [MeasurableSpace G] [MeasurableSpace C]
    [MeasurableSpace.CountablySeparated C] {μ : Measure Ω}
    (x : Ω → G) (q : G → C) (hq : Measurable q) (hqinj : Function.Injective q)
    (S : Set G) [StandardBorelSpace S] (s₀ : S)
    (hs : ∀ᵐ ω ∂μ, x ω ∈ S) (hcode : AEMeasurable (q ∘ x) μ) :
    AEMeasurable x μ := by
  classical
  let y : Ω → S := fun ω => if h : x ω ∈ S then ⟨x ω, h⟩ else s₀
  have hy : (fun ω => (y ω : G)) =ᵐ[μ] x := by
    filter_upwards [hs] with ω hω
    simp [y, hω]
  have hqy : AEMeasurable ((q ∘ Subtype.val) ∘ y) μ :=
    hcode.congr (hy.mono fun _ h => by simp only [Function.comp_apply, h])
  have hqS : MeasurableEmbedding (q ∘ (Subtype.val : S → G)) :=
    (hq.comp measurable_subtype_coe).measurableEmbedding (hqinj.comp Subtype.val_injective)
  have hym : AEMeasurable y μ := hqS.aemeasurable_comp_iff.mp hqy
  exact (measurable_subtype_coe.comp_aemeasurable hym).congr hy

end LatticeProb
