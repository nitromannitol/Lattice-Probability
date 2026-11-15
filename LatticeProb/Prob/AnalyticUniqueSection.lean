import LatticeProb.Prob.AnalyticUniversalMeasurable
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Almost-everywhere unique sections of analytic sets -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- An analytic relation with almost surely exactly one point in each section
admits a measurable version of that point for the given finite measure. -/
theorem exists_measurable_of_ae_unique_analytic_section
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    (μ : Measure X) [IsFiniteMeasure μ] {G : Set (X × Y)} (hG : AnalyticSet G)
    (huniq : ∀ᵐ x ∂μ, ∃! y, (x, y) ∈ G) :
    ∃ f : X → Y, Measurable f ∧ ∀ᵐ x ∂μ, (x, f x) ∈ G := by
  classical
  let f : X → Y := fun x => if h : ∃ y, (x, y) ∈ G then Classical.choose h else Classical.choice ‹Nonempty Y›
  have hf : ∀ᵐ x ∂μ, (x, f x) ∈ G ∧ ∀ y, (x, y) ∈ G → y = f x := by
    filter_upwards [huniq] with x ⟨y, hy, hu⟩
    have he : ∃ y, (x, y) ∈ G := ⟨y, hy⟩
    have hm : (x, f x) ∈ G := by
      simp only [f, dite_eq_left he]
      exact Classical.choose_spec he
    exact ⟨hm, fun z hz => (hu z hz).trans (hu (f x) hm).symm⟩
  have hfm : NullMeasurable f μ := by
    intro T hT
    let A : Set (X × Y) := G ∩ Prod.snd ⁻¹' T
    have hA : AnalyticSet A := by
      change AnalyticSet (G ∩ Prod.snd ⁻¹' T)
      rw [Set.inter_eq_iInter]
      apply AnalyticSet.iInter
      intro b
      cases b
      · exact (hT.preimage measurable_snd).analyticSet
      · exact hG
    have hp : NullMeasurableSet (Prod.fst '' A) μ :=
      AnalyticSet.nullMeasurableSet μ (hA.image_of_continuous continuous_fst)
    apply hp.congr
    filter_upwards [hf] with x hx
    apply propext
    change (∃ p ∈ A, p.1 = x) ↔ f x ∈ T
    constructor
    · rintro ⟨⟨x', y⟩, ⟨hy, hT'⟩, rfl⟩
      change y ∈ T at hT'
      simpa only [hx.2 y hy] using hT'
    · intro hT'
      exact ⟨(x, f x), ⟨hx.1, hT'⟩, rfl⟩
  have hfa := hfm.aemeasurable
  refine ⟨hfa.mk f, hfa.measurable_mk, ?_⟩
  filter_upwards [hf, hfa.ae_eq_mk] with x hx he
  simpa only [← he] using hx.1

end LatticeProb
