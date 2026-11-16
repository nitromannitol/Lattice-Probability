import LatticeProb.MeasureTheory.FiniteAlgebraSimpleProfile
import LatticeProb.MeasureTheory.ProfileExceptionalError

/-! # Approximation by labelled algebra partitions -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal symmDiff BigOperators

namespace LatticeProb

/-- A labelled algebra partition approximates a profile outside the symmetric
 differences of the original and approximating sets. -/
theorem exists_simpleFunc_labelled_partition_bound {α E ι : Type*}
    [MeasurableSpace α] [PseudoEMetricSpace E] [Fintype ι]
    (μ : Measure α) {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜) {D : Set E}
    (s t : ι → Set α) (v : ι → E) (v₀ : E) (hv₀ : v₀ ∈ D)
    (ht : ∀ i, t i ∈ 𝒜) (htm : ∀ i, MeasurableSet (t i))
    (hv : ∀ i, v i ∈ D) (hdisj : Pairwise (Function.onFun Disjoint t))
    (hcover : ∀ x, ∃ i, x ∈ s i) (f : α → E) (δ : ℝ≥0∞)
    (hclose : ∀ i x, x ∈ s i → edist (f x) (v i) ≤ δ) :
    ∃ g : SimpleFunc α E, Set.range g ⊆ D ∧
      (∀ y ∈ Set.range g, g ⁻¹' {y} ∈ 𝒜) ∧
      (∫⁻ x, min 1 (edist (f x) (g x)) ∂μ) ≤
        δ * μ univ + ∑ i, μ (s i ∆ t i) := by
  classical
  obtain ⟨g, hgD, hgA, hgval, _⟩ :=
    exists_simpleFunc_of_disjoint_algebra_sets h𝒜 t v v₀ hv₀ ht htm hv hdisj Finset.univ
  refine ⟨g, hgD, hgA, ?_⟩
  calc
    (∫⁻ x, min 1 (edist (f x) (g x)) ∂μ) ≤
        δ * μ univ + μ (⋃ i, s i ∆ t i) := by
      apply lintegral_min_edist_le_of_forall_not_mem
      intro x hx
      obtain ⟨i, hxi⟩ := hcover x
      have hxt : x ∈ t i := by
        have hn : x ∉ s i ∆ t i := fun h => hx (mem_iUnion.mpr ⟨i, h⟩)
        by_contra hxt
        exact hn (by simp [mem_symmDiff, hxi, hxt])
      rw [hgval i (Finset.mem_univ i) x hxt]
      exact hclose i x hxi
    _ ≤ δ * μ univ + ∑ i, μ (s i ∆ t i) :=
      add_le_add_right (measure_iUnion_fintype_le μ _) _

end LatticeProb
