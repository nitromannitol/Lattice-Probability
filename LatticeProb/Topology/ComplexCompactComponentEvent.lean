import LatticeProb.Topology.CompactIntersectionComponentEvent
import LatticeProb.Topology.CompactCurveRange
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Arcs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Components of intersections of random compact planar sets -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open scoped unitInterval

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- A homeomorphism preserves existence of a non-singleton component. -/
theorem exists_nonsubsingleton_component_image_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (S : Set X) :
    (∃ C ∈ connectedComponentIn (e '' S) '' (e '' S), ¬ C.Subsingleton) ↔
      ∃ C ∈ connectedComponentIn S '' S, ¬ C.Subsingleton := by
  constructor
  · rintro ⟨C, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, hn⟩
    refine ⟨connectedComponentIn S x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← e.image_connectedComponentIn hx, e.injective.subsingleton_image_iff] at hn
    exact hn
  · rintro ⟨C, ⟨x, hx, rfl⟩, hn⟩
    refine ⟨connectedComponentIn (e '' S) (e x), ⟨e x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    rw [← e.image_connectedComponentIn hx, e.injective.subsingleton_image_iff]
    exact hn

/-- A non-singleton component of the intersection of measurable random compact
sets is a null-measurable event for every finite measure. -/
theorem nullMeasurableSet_random_complex_compact_inter_component
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Ω → NonemptyCompacts ℂ) (hA : Measurable A) (hB : Measurable B)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ C ∈ connectedComponentIn
      ((A ω : Set ℂ) ∩ B ω) '' ((A ω : Set ℂ) ∩ B ω), ¬ C.Subsingleton} μ := by
  let e := MatedCRTHarmonic.Planar.Jordan.Arcs.complexLIE
  let f : NonemptyCompacts ℂ → ReflectedGMS.Code.CompactCell :=
    NonemptyCompacts.map e e.continuous
  have hf : Measurable f := e.isometry.uniformContinuous.nonemptyCompacts_map.continuous.measurable
  let g : Ω → ReflectedGMS.Code.CompactCell × ReflectedGMS.Code.CompactCell :=
    fun ω => (f (A ω), f (B ω))
  have hg : Measurable g := (hf.comp hA).prodMk (hf.comp hB)
  let : IsFiniteMeasure (μ.map g) := μ.isFiniteMeasure_map g
  have h := (nullMeasurableSet_exists_nonsubsingleton_inter_component (μ.map g)).preimage
    (hg.quasiMeasurePreserving μ)
  convert h using 1
  ext ω
  change (∃ C ∈ connectedComponentIn ((A ω : Set ℂ) ∩ B ω) ''
      ((A ω : Set ℂ) ∩ B ω), ¬ C.Subsingleton) ↔
    ∃ C ∈ connectedComponentIn ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ))) ''
      ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ))), ¬ C.Subsingleton
  rw [← image_inter e.injective]
  exact (exists_nonsubsingleton_component_image_iff e.toHomeomorph _).symm

/-- The same event for two measurable random continuous curves. -/
theorem nullMeasurableSet_random_complex_curve_inter_component
    {Ω : Type*} [MeasurableSpace Ω] (α β : Ω → C(unitInterval, ℂ))
    (hα : Measurable α) (hβ : Measurable β)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω | ∃ C ∈ connectedComponentIn
      (range (α ω) ∩ range (β ω)) '' (range (α ω) ∩ range (β ω)),
      ¬ C.Subsingleton} μ := by
  exact nullMeasurableSet_random_complex_compact_inter_component
    (fun ω => compactCurveRange (α ω)) (fun ω => compactCurveRange (β ω))
    (continuous_compactCurveRange.measurable.comp hα)
    (continuous_compactCurveRange.measurable.comp hβ) μ

end LatticeProb
