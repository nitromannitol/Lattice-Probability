import LatticeProb.Prob.EnumeratedCellCodeMeasurable

/-! # Codes of almost-everywhere measurable enumerated cells -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]

/-- A countable almost-everywhere measurable enumeration and its conductances
produce an almost-everywhere measurable code on valid configurations. -/
theorem aemeasurable_enumeratedCell_code_of_ae (μ : Measure Ω)
    (H : Ω → CellConfig) (C : ι → Ω → Cell)
    (hgood : ∀ᵐ ω ∂μ, (H ω).IsCellConfiguration ∧
      (H ω).cells = Set.range (fun i => C i ω))
    (hC : ∀ i, AEMeasurable (C i) μ)
    (hc : ∀ i j, AEMeasurable (fun ω => (H ω).c (C i ω) (C j ω)) μ) :
    AEMeasurable (fun ω => (H ω).code) μ := by
  classical
  let c : ι → ι → Ω → ℝ := fun i j ω => (H ω).c (C i ω) (C j ω)
  have heqC : ∀ᵐ ω ∂μ, ∀ i, C i ω = (hC i).mk (C i) ω :=
    ae_all_iff.mpr fun i => (hC i).ae_eq_mk
  have heqc : ∀ᵐ ω ∂μ, ∀ i j, c i j ω = (hc i j).mk (c i j) ω :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (hc i j).ae_eq_mk
  have hall : ∀ᵐ ω ∂μ, ((H ω).IsCellConfiguration ∧
      (H ω).cells = Set.range (fun i => C i ω)) ∧
      (∀ i, C i ω = (hC i).mk (C i) ω) ∧
      (∀ i j, c i j ω = (hc i j).mk (c i j) ω) := by
    filter_upwards [hgood, heqC, heqc] with ω hg hC' hc'
    exact ⟨hg, hC', hc'⟩
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  have hs : MeasurableSet Nᶜ := hNm.compl
  have hfull : ∀ᵐ ω ∂μ, ω ∈ Nᶜ := by
    apply ae_iff.mpr
    simpa only [Set.mem_compl_iff, not_not, Set.ofPred_mem_eq] using hN0
  have hvalid (ω : {ω // ω ∈ Nᶜ}) := by
    by_contra hn
    exact ω.property (hN hn)
  have hm : Measurable (fun ω : {ω // ω ∈ Nᶜ} => (H ω).code) := by
    apply measurable_enumeratedCell_code (fun ω : {ω // ω ∈ Nᶜ} => H ω)
      (fun i ω => C i ω)
    · exact fun ω => (hvalid ω).1.1
    · exact fun ω => (hvalid ω).1.2
    · intro i
      have heq : (fun ω : {ω // ω ∈ Nᶜ} => C i ω) =
          (fun ω : {ω // ω ∈ Nᶜ} => (hC i).mk (C i) ω) := by
        funext ω
        exact (hvalid ω).2.1 i
      rw [heq]
      exact (hC i).measurable_mk.comp measurable_subtype_coe
    · intro i j
      have heq : (fun ω : {ω // ω ∈ Nᶜ} => (H ω).c (C i ω) (C j ω)) =
          (fun ω : {ω // ω ∈ Nᶜ} => (hc i j).mk (c i j) ω) := by
        funext ω
        exact (hvalid ω).2.2 i j
      rw [heq]
      exact (hc i j).measurable_mk.comp measurable_subtype_coe
  have ha := aemeasurable_restrict_of_measurable_subtype
    (f := fun ω => (H ω).code) (μ := μ) hs hm
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at ha

end LatticeProb
