import LatticeProb.Topology.AreaCurveOpenCoverage
import LatticeProb.Topology.ProperAreaCurveFrontier
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Component interval covers for area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- A family of interval witnesses for components covering the interior of a
segment also covers all visits to that interior by the open witness intervals. -/
theorem preimage_interior_subset_iUnion_component_intervals
    {ι : Type*} (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (s t : ℝ) (x : ι → ℂ) (a b : ι → ℝ) (A : Set ι)
    (hab : ∀ i ∈ A, a i < b i)
    (himage : ∀ i ∈ A, η '' Icc (a i) (b i) =
      closure (connectedComponentIn (interior (η '' Icc s t)) (x i)))
    (hcover : ∀ z ∈ interior (η '' Icc s t), ∃ i ∈ A,
      z ∈ connectedComponentIn (interior (η '' Icc s t)) (x i)) :
    η ⁻¹' interior (η '' Icc s t) ⊆ ⋃ i ∈ A, Ioo (a i) (b i) := by
  intro u hu
  obtain ⟨i, hi, hui⟩ := hcover (η u) hu
  refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ?_⟩⟩
  apply preimage_open_subset_Ioo_of_area_curve_coverage η μ η.continuous harea
    isOpen_interior.connectedComponentIn (hab i hi) _ hui
  rw [himage i hi]
  exact subset_closure

/-- If component interval witnesses cover the interior of a proper area curve
segment, their open intervals cover almost every time in the original segment. -/
theorem ae_mem_component_intervals_of_proper_area_curve
    {ι : Type*} (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t) (x : ι → ℂ) (a b : ι → ℝ) (A : Set ι)
    (hab : ∀ i ∈ A, a i < b i)
    (himage : ∀ i ∈ A, η '' Icc (a i) (b i) =
      closure (connectedComponentIn (interior (η '' Icc s t)) (x i)))
    (hcover : ∀ z ∈ interior (η '' Icc s t), ∃ i ∈ A,
      z ∈ connectedComponentIn (interior (η '' Icc s t)) (x i)) :
    ∀ᵐ u ∂volume, u ∈ Icc s t → ∃ i ∈ A, u ∈ Ioo (a i) (b i) := by
  have hfront := measure_frontier_image_Icc_eq_zero_of_proper η μ η.continuous hp hs harea hst
  have hae := interior_ae_eq_of_null_frontier hfront
  rw [← hmap] at hae
  have hae' := ae_of_ae_map η.continuous.measurable.aemeasurable hae
  filter_upwards [hae'] with u hu huI
  have hui : η u ∈ interior (η '' Icc s t) := hu.mpr ⟨u, huI, rfl⟩
  have h := preimage_interior_subset_iUnion_component_intervals η μ harea s t x a b A
    hab himage hcover hui
  obtain ⟨i, hi⟩ := mem_iUnion.mp h
  obtain ⟨hiA, hui⟩ := mem_iUnion.mp hi
  exact ⟨i, hiA, hui⟩

end LatticeProb
