import LatticeProb.Prob.EnumeratedCellCodeAEModification
import LatticeProb.Prob.CellConfigCodeInjective
import LatticeProb.Prob.MeasurableCodeRealization

/-! # Realization of enumerated cell configurations -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb

/-- A countably enumerated configuration has a measurable realization when its
code has a measurable right inverse on a measurable set of full code law. -/
theorem exists_measurable_ae_eq_enumerated_cell_config
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (H : Ω → GMSSpace) (H₀ : GMSSpace) (C : ι → Ω → Cell)
    (henum : ∀ᵐ ω ∂μ, (H ω).1.cells = Set.range (fun i => C i ω))
    (hC : ∀ i, AEMeasurable (C i) μ)
    (hc : ∀ i j, AEMeasurable (fun ω => (H ω).1.c (C i ω) (C j ω)) μ)
    (B : Set Code.RawCode) (hB : MeasurableSet B)
    (hfull : μ.map (fun ω => (H ω).1.code) Bᶜ = 0)
    (d : B → GMSSpace) (hd : Measurable d) (hinv : ∀ c : B, codeMap (d c) = c.1) :
    ∃ F : Ω → GMSSpace, Measurable F ∧ F =ᵐ[μ] H := by
  have hcode : AEMeasurable (codeMap ∘ H) μ := by
    apply aemeasurable_enumeratedCell_code_of_ae μ (fun ω => (H ω).1) C
    · filter_upwards [henum] with ω hω
      exact ⟨(H ω).2, hω⟩
    · exact hC
    · exact hc
  exact exists_measurable_ae_eq_of_code_decoder H codeMap H₀ codeMap_injective hcode
    B hB hfull d hd hinv

end LatticeProb
