import LatticeProb.Prob.EnumeratedCellCodeMeasurable

/-! # Almost-everywhere measurability of enumerated cell codes -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]

/-- A countable measurable enumeration gives an almost-everywhere measurable
code when it enumerates a valid configuration almost everywhere. -/
theorem aemeasurable_enumeratedCell_code (μ : Measure Ω)
    (H : Ω → CellConfig) (C : ι → Ω → Cell)
    (hgood : ∀ᵐ ω ∂μ, (H ω).IsCellConfiguration ∧
      (H ω).cells = Set.range (fun i => C i ω))
    (hC : ∀ i, Measurable (C i))
    (hc : ∀ i j, Measurable fun ω => (H ω).c (C i ω) (C j ω)) :
    AEMeasurable (fun ω => (H ω).code) μ := by
  classical
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hs : MeasurableSet Nᶜ := hNm.compl
  have hfull : ∀ᵐ ω ∂μ, ω ∈ Nᶜ := by
    apply ae_iff.mpr
    simpa only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq] using hN0
  have hvalid (ω : {ω // ω ∈ Nᶜ}) : (H ω).IsCellConfiguration ∧
      (H ω).cells = Set.range (fun i => C i ω) := by
    by_contra hn
    exact ω.property (hN hn)
  have hm : Measurable (fun ω : {ω // ω ∈ Nᶜ} => (H ω).code) := by
    apply measurable_enumeratedCell_code (fun ω : {ω // ω ∈ Nᶜ} => H ω)
      (fun i ω => C i ω)
    · exact fun ω => (hvalid ω).1
    · exact fun ω => (hvalid ω).2
    · exact fun i => (hC i).comp measurable_subtype_coe
    · exact fun i j => (hc i j).comp measurable_subtype_coe
  have ha := aemeasurable_restrict_of_measurable_subtype
    (f := fun ω => (H ω).code) (μ := μ) hs hm
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at ha

end LatticeProb
