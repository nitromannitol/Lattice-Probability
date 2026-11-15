import LatticeProb.Topology.TwoCompactIntersectionComponentsEvent
import LatticeProb.Topology.ComplexCompactComponentEvent

/-! # Two components of intersections of random compact complex sets -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open scoped unitInterval

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- A homeomorphism preserves the existence of two distinct non-singleton components. -/
theorem exists_two_nonsubsingleton_components_image_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (S : Set X) :
    (∃ x ∈ e '' S, ∃ y ∈ e '' S,
      connectedComponentIn (e '' S) x ≠ connectedComponentIn (e '' S) y ∧
      ¬ (connectedComponentIn (e '' S) x).Subsingleton ∧
      ¬ (connectedComponentIn (e '' S) y).Subsingleton) ↔
    ∃ x ∈ S, ∃ y ∈ S,
      connectedComponentIn S x ≠ connectedComponentIn S y ∧
      ¬ (connectedComponentIn S x).Subsingleton ∧
      ¬ (connectedComponentIn S y).Subsingleton := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hne, hxns, hyns⟩
    simp only [← e.image_connectedComponentIn hx, ← e.image_connectedComponentIn hy] at hne hxns hyns
    exact ⟨x, hx, y, hy, fun h => hne (congrArg (fun C => e '' C) h),
      fun h => hxns (e.injective.subsingleton_image_iff.mpr h),
      fun h => hyns (e.injective.subsingleton_image_iff.mpr h)⟩
  · rintro ⟨x, hx, y, hy, hne, hxns, hyns⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, ?_, ?_, ?_⟩
    · rw [← e.image_connectedComponentIn hx, ← e.image_connectedComponentIn hy]
      exact fun h => hne (e.injective.image_injective h)
    · rw [← e.image_connectedComponentIn hx, e.injective.subsingleton_image_iff]
      exact hxns
    · rw [← e.image_connectedComponentIn hy, e.injective.subsingleton_image_iff]
      exact hyns

/-- Two distinct non-singleton intersection components form a null-measurable event
for measurable complex compact-valued random variables and every finite law. -/
theorem nullMeasurableSet_random_complex_compact_inter_two_components
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Ω → NonemptyCompacts ℂ) (hA : Measurable A) (hB : Measurable B)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      ∃ x ∈ (A ω : Set ℂ) ∩ B ω, ∃ y ∈ (A ω : Set ℂ) ∩ B ω,
        connectedComponentIn ((A ω : Set ℂ) ∩ B ω) x ≠
          connectedComponentIn ((A ω : Set ℂ) ∩ B ω) y ∧
        ¬ (connectedComponentIn ((A ω : Set ℂ) ∩ B ω) x).Subsingleton ∧
        ¬ (connectedComponentIn ((A ω : Set ℂ) ∩ B ω) y).Subsingleton} μ := by
  let e := MatedCRTHarmonic.Planar.Jordan.Arcs.complexLIE
  let f : NonemptyCompacts ℂ → ReflectedGMS.Code.CompactCell :=
    NonemptyCompacts.map e e.continuous
  have hf : Measurable f := e.isometry.uniformContinuous.nonemptyCompacts_map.continuous.measurable
  let g : Ω → ReflectedGMS.Code.CompactCell × ReflectedGMS.Code.CompactCell :=
    fun ω => (f (A ω), f (B ω))
  have hg : Measurable g := (hf.comp hA).prodMk (hf.comp hB)
  let : IsFiniteMeasure (μ.map g) := μ.isFiniteMeasure_map g
  have h := (nullMeasurableSet_exists_two_nonsubsingleton_inter_components (μ.map g)).preimage
    (hg.quasiMeasurePreserving μ)
  convert h using 1
  ext ω
  change (∃ x ∈ (A ω : Set ℂ) ∩ B ω, ∃ y ∈ (A ω : Set ℂ) ∩ B ω,
      connectedComponentIn ((A ω : Set ℂ) ∩ B ω) x ≠
        connectedComponentIn ((A ω : Set ℂ) ∩ B ω) y ∧
      ¬ (connectedComponentIn ((A ω : Set ℂ) ∩ B ω) x).Subsingleton ∧
      ¬ (connectedComponentIn ((A ω : Set ℂ) ∩ B ω) y).Subsingleton) ↔
    ∃ x ∈ (e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ)),
    ∃ y ∈ (e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ)),
      connectedComponentIn ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ))) x ≠
        connectedComponentIn ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ))) y ∧
      ¬ (connectedComponentIn ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ))) x).Subsingleton ∧
      ¬ (connectedComponentIn ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ))) y).Subsingleton
  rw [← image_inter e.injective]
  exact (exists_two_nonsubsingleton_components_image_iff e.toHomeomorph _).symm

/-- The same event for two measurable random continuous curves. -/
theorem nullMeasurableSet_random_complex_curve_inter_two_components
    {Ω : Type*} [MeasurableSpace Ω] (α β : Ω → C(unitInterval, ℂ))
    (hα : Measurable α) (hβ : Measurable β)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      ∃ x ∈ range (α ω) ∩ range (β ω), ∃ y ∈ range (α ω) ∩ range (β ω),
        connectedComponentIn (range (α ω) ∩ range (β ω)) x ≠
          connectedComponentIn (range (α ω) ∩ range (β ω)) y ∧
        ¬ (connectedComponentIn (range (α ω) ∩ range (β ω)) x).Subsingleton ∧
        ¬ (connectedComponentIn (range (α ω) ∩ range (β ω)) y).Subsingleton} μ := by
  exact nullMeasurableSet_random_complex_compact_inter_two_components
    (fun ω => compactCurveRange (α ω)) (fun ω => compactCurveRange (β ω))
    (continuous_compactCurveRange.measurable.comp hα)
    (continuous_compactCurveRange.measurable.comp hβ) μ

end LatticeProb
