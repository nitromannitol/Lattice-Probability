import LatticeProb.Topology.CompactIntersectionComponentThreshold
import LatticeProb.Topology.ComplexCompactComponentEvent

/-! # Cardinalities of components of random compact intersections -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open ReflectedGMS ReflectedGMS.Code

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- A homeomorphism maps the non-singleton components bijectively. -/
theorem nonSingletonComponents_image_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (S : Set X) :
    nonSingletonComponents (e '' S) = (fun C : Set X => e '' C) '' nonSingletonComponents S := by
  ext C
  simp only [nonSingletonComponents, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, hn⟩
    refine ⟨connectedComponentIn S x, ⟨⟨x, hx, rfl⟩, ?_⟩, ?_⟩
    · rw [← e.image_connectedComponentIn hx, e.injective.subsingleton_image_iff] at hn
      exact hn
    · exact e.image_connectedComponentIn hx
  · rintro ⟨_, ⟨⟨x, hx, rfl⟩, hn⟩, rfl⟩
    refine ⟨⟨e x, ⟨x, hx, rfl⟩, (e.image_connectedComponentIn hx).symm⟩, ?_⟩
    rwa [e.injective.subsingleton_image_iff]

/-- Finite component-count thresholds for measurable random compact complex sets
are null measurable under a finite law. -/
theorem nullMeasurableSet_random_complex_compact_inter_component_threshold
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Ω → NonemptyCompacts ℂ) (hA : Measurable A) (hB : Measurable B)
    (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) :
    NullMeasurableSet {ω : Ω | (n : ℕ∞) ≤
      (nonSingletonComponents ((A ω : Set ℂ) ∩ B ω)).encard} μ := by
  let e := MatedCRTHarmonic.Planar.Jordan.Arcs.complexLIE
  let f : NonemptyCompacts ℂ → CompactCell := NonemptyCompacts.map e e.continuous
  have hf : Measurable f := e.isometry.uniformContinuous.nonemptyCompacts_map.continuous.measurable
  let g : Ω → CompactCell × CompactCell := fun ω => (f (A ω), f (B ω))
  have hg : Measurable g := (hf.comp hA).prodMk (hf.comp hB)
  let : IsFiniteMeasure (μ.map g) := μ.isFiniteMeasure_map g
  have h := (nullMeasurableSet_le_encard_nonSingletonComponents_inter n (μ.map g)).preimage
    (hg.quasiMeasurePreserving μ)
  convert h using 1
  ext ω
  change ((n : ℕ∞) ≤ (nonSingletonComponents ((A ω : Set ℂ) ∩ B ω)).encard) ↔
    (n : ℕ∞) ≤ (nonSingletonComponents ((e '' (A ω : Set ℂ)) ∩ (e '' (B ω : Set ℂ)))).encard
  rw [← image_inter e.injective]
  have heq := nonSingletonComponents_image_homeomorph e.toHomeomorph
    ((A ω : Set ℂ) ∩ B ω)
  change nonSingletonComponents (e '' ((A ω : Set ℂ) ∩ B ω)) =
    (fun C : Set ℂ => e '' C) '' nonSingletonComponents ((A ω : Set ℂ) ∩ B ω) at heq
  have hinj : Function.Injective (fun C : Set ℂ => e '' C) :=
    fun _ _ h => e.injective.image_injective h
  rw [heq, Set.InjOn.encard_image hinj.injOn]

/-- The component count is almost everywhere measurable, including when it is infinite. -/
theorem aemeasurable_random_complex_compact_inter_component_encard
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Ω → NonemptyCompacts ℂ) (hA : Measurable A) (hB : Measurable B)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    AEMeasurable (fun ω => (nonSingletonComponents ((A ω : Set ℂ) ∩ B ω)).encard) μ :=
  aemeasurable_enat_of_nullMeasurable_thresholds μ _
    (fun n => nullMeasurableSet_random_complex_compact_inter_component_threshold A B hA hB μ n)

/-- The natural component count is almost everywhere measurable; it is zero
when there are infinitely many components. -/
theorem aemeasurable_random_complex_compact_inter_component_ncard
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Ω → NonemptyCompacts ℂ) (hA : Measurable A) (hB : Measurable B)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    AEMeasurable (fun ω => (nonSingletonComponents ((A ω : Set ℂ) ∩ B ω)).ncard) μ :=
  aemeasurable_ncard_of_nullMeasurable_encard_thresholds μ _
    (fun n => nullMeasurableSet_random_complex_compact_inter_component_threshold A B hA hB μ n)

/-- The exact natural component counts of all pairs of shifted curve cells have
an almost everywhere measurable version under every finite law. -/
theorem aemeasurable_shifted_cell_component_ncard_array
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    AEMeasurable (fun ω (k l : ℤ) => (nonSingletonComponents
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)).ncard) μ := by
  apply AEMeasurable.of_eval
  intro k
  apply AEMeasurable.of_eval
  intro l
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) j) :=
    (measurable_shiftedCompactCell j).comp (hη.prodMk (hε.prodMk hθ))
  exact aemeasurable_random_complex_compact_inter_component_ncard _ _ (hc k) (hc l) μ

end LatticeProb
