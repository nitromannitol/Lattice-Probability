import LatticeProb.Prob.CellConfigPatchClasses
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-! # Positive-measure cell configuration patch classes -/

set_option autoImplicit false

open Set MeasureTheory

namespace ReflectedGMS.GMS

/-- A positive-measure set with countably many values has a positive-measure
fiber, without measurability assumptions on the set, the function, or the fibers. -/
theorem exists_pos_measure_fiber_of_countable_image {Ω α : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) (f : Ω → α)
    (hE : 0 < μ E) (hcount : (f '' E).Countable) :
    ∃ ω ∈ E, 0 < μ {ω' | ω' ∈ E ∧ f ω' = f ω} := by
  classical
  by_contra h
  push Not at h
  have hnull : μ (⋃ z ∈ f '' E, {ω | ω ∈ E ∧ f ω = z}) = 0 := by
    apply (measure_biUnion_null_iff hcount).2
    rintro z ⟨ω, hω, rfl⟩
    exact nonpos_iff_eq_zero.mp (h ω hω)
  have hsub : E ⊆ ⋃ z ∈ f '' E, {ω | ω ∈ E ∧ f ω = z} := by
    intro ω hω
    exact mem_iUnion.mpr ⟨f ω, mem_iUnion.mpr ⟨⟨ω, hω, rfl⟩, hω, rfl⟩⟩
  exact (ne_of_gt hE) (measure_mono_null hsub hnull)

/-- A positive-measure family of configurations stable on a common interval
inside a second-countable subspace contains a positive-measure patch class. -/
theorem exists_pos_measure_patchClass_of_stable_restrict {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) (X : Ω → GMSSpace)
    (T : Set GMSSpace) [SecondCountableTopology T] {a b s : ℝ}
    (hE : 0 < μ E) (hmem : ∀ ω ∈ E, X ω ∈ T)
    (ha : 0 ≤ a) (hab : a < b)
    (hstable : ∀ ω ∈ E, ∀ r ∈ Ioo a b,
      (X ω).1.restrict (Metric.ball 0 r) = (X ω).1.restrict (Metric.ball 0 s)) :
    ∃ ω ∈ E, 0 < μ {ω' | ω' ∈ E ∧
      CellConfig.patchClass s (X ω').1 = CellConfig.patchClass s (X ω).1} := by
  let F : E → T := fun ω => ⟨X ω.1, hmem ω.1 ω.2⟩
  have hcount := countable_patchClasses_of_stable_restrict T (range F) ha hab (by
    rintro x ⟨ω, rfl⟩ r hr
    exact hstable ω.1 ω.2 r hr)
  apply exists_pos_measure_fiber_of_countable_image μ E
    (fun ω => CellConfig.patchClass s (X ω).1) hE
  apply hcount.mono
  rintro _ ⟨ω, hω, rfl⟩
  exact ⟨F ⟨ω, hω⟩, ⟨⟨ω, hω⟩, rfl⟩, rfl⟩

end ReflectedGMS.GMS
