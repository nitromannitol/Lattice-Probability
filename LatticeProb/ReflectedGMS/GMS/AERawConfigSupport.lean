import LatticeProb.ReflectedGMS.GMS.AELineConnectedSupport

/-! # Measurable realizations of almost surely valid configurations -/

set_option autoImplicit false

open Set MeasureTheory

namespace ReflectedGMS.GMS

/-- An almost surely valid and line-connected raw configuration has a measurable
version when its code is almost everywhere measurable and it is almost surely
supported on a second-countable family. -/
theorem exists_measurable_ae_eq_raw_of_support
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [SFinite μ] (C : Ω → CellConfig)
    (T : Set GMSSpace) [SecondCountableTopology T]
    (H₀ : T) (h₀ : H₀.1.1.LineConnected)
    (hvalid : ∀ᵐ ω ∂μ, (C ω).IsCellConfiguration ∧ (C ω).LineConnected)
    (hT : ∀ᵐ ω ∂μ, ∃ h : (C ω).IsCellConfiguration, (⟨C ω, h⟩ : GMSSpace) ∈ T)
    (hcode : AEMeasurable (fun ω => (C ω).code) μ) :
    ∃ F : Ω → GMSSpace, Measurable F ∧ ∀ᵐ ω ∂μ, (F ω).1 = C ω := by
  classical
  let H : Ω → GMSSpace := fun ω =>
    if h : (C ω).IsCellConfiguration then ⟨C ω, h⟩ else H₀.1
  have heq : ∀ᵐ ω ∂μ, (H ω).1 = C ω := by
    filter_upwards [hvalid] with ω hω
    simp [H, hω.1]
  have hHT : ∀ᵐ ω ∂μ, H ω ∈ T := by
    filter_upwards [hvalid, hT] with ω hv ⟨h, ht⟩
    simpa [H, hv.1] using ht
  have hHL : ∀ᵐ ω ∂μ, (H ω).1.LineConnected := by
    filter_upwards [hvalid, heq] with ω hv he
    simpa [he] using hv.2
  have hHcode : AEMeasurable (fun ω => (H ω).1.code) μ := by
    apply hcode.congr
    filter_upwards [heq] with ω he
    rw [he]
  obtain ⟨F, hF, heF⟩ :=
    exists_measurable_ae_eq_of_support_ae_lineConnected μ H T H₀ h₀ hHT hHL hHcode
  refine ⟨F, hF, ?_⟩
  filter_upwards [heF, heq] with ω hFω hω
  simpa [hFω] using hω

end ReflectedGMS.GMS
