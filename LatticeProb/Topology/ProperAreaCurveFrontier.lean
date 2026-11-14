import LatticeProb.Analysis.AreaParametrizedCurveCells
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Frontiers of proper area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function
open scoped ENNReal

namespace LatticeProb

/-- Every compact segment of a proper surjective area-parametrized curve has null frontier. -/
theorem measure_frontier_image_Icc_eq_zero_of_proper
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : ℝ → X) (μ : Measure X)
    (hc : Continuous η) (hp : IsProperMap η) (hs : Surjective η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b : ℝ} (hab : a < b) : μ (frontier (η '' Icc a b)) = 0 := by
  let K := η '' Icc a b
  let L := η '' Iic a
  let R := η '' Ici b
  have hK : IsClosed K := (isCompact_Icc.image hc).isClosed
  have hLR : IsClosed (L ∪ R) :=
    (hp.isClosedMap _ isClosed_Iic).union (hp.isClosedMap _ isClosed_Ici)
  have hcover : ∀ x, x ∈ L ∪ K ∪ R := by
    intro x
    obtain ⟨t, rfl⟩ := hs x
    rcases le_total t a with hta | hat
    · exact Or.inl (Or.inl ⟨t, hta, rfl⟩)
    rcases le_total t b with htb | hbt
    · exact Or.inl (Or.inr ⟨t, ⟨hat, htb⟩, rfl⟩)
    · exact Or.inr ⟨t, hbt, rfl⟩
  have hfront : frontier K ⊆ K ∩ (L ∪ R) := by
    intro x hx
    have hxK : x ∈ K := hK.closure_eq ▸ frontier_subset_closure hx
    refine ⟨hxK, ?_⟩
    by_contra hxLR
    have hxint : x ∈ interior K := by
      apply mem_interior_iff_mem_nhds.mpr
      apply Filter.mem_of_superset (hLR.isOpen_compl.mem_nhds hxLR)
      intro y hy
      rcases hcover y with (hyL | hyK) | hyR
      · exact (hy (Or.inl hyL)).elim
      · exact hyK
      · exact (hy (Or.inr hyR)).elim
    exact (show x ∉ interior K from hx.2) hxint
  have hL : μ (K ∩ L) = 0 := by
    have hsub : K ∩ L ⊆ ⋃ n : ℕ, K ∩ (η '' Icc (a - (n + 1 : ℕ)) a) := by
      rintro x ⟨hxK, t, ht, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (a - t)
      refine mem_iUnion.mpr ⟨n, hxK, t, ⟨?_, ht⟩, rfl⟩
      push_cast
      linarith
    apply measure_mono_null hsub
    apply measure_iUnion_null
    intro n
    rw [inter_comm]
    apply measure_image_Icc_inter_image_Icc_eq_zero hc hμ _ le_rfl hab
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    linarith
  have hR : μ (K ∩ R) = 0 := by
    have hsub : K ∩ R ⊆ ⋃ n : ℕ, K ∩ (η '' Icc b (b + (n + 1 : ℕ))) := by
      rintro x ⟨hxK, t, ht, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (t - b)
      refine mem_iUnion.mpr ⟨n, hxK, t, ⟨ht, ?_⟩, rfl⟩
      push_cast
      linarith
    apply measure_mono_null hsub
    apply measure_iUnion_null
    intro n
    apply measure_image_Icc_inter_image_Icc_eq_zero hc hμ hab le_rfl _
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    linarith
  apply measure_mono_null hfront
  rw [inter_union_distrib_left]
  exact measure_union_null hL hR

end LatticeProb
