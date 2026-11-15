import LatticeProb.Prob.TVMarkedBoxApproximation
import LatticeProb.Prob.TVFiniteSum

/-! Total variation approximation of finite sums by marked boxes. -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace LatticeProb

/-- A finite sum of restrictions of finite measures can be approximated in
    total variation by restrictions to finite unions of marked boxes. -/
theorem exists_finset_marked_Ico_boxes_tv_sum_restrict_lt
    {E ι J : Type*} [MeasurableSpace E] [Finite ι]
    (μ : J → Measure (E × (ι → ℝ))) [∀ j, IsFiniteMeasure (μ j)]
    (s : J → Set (E × (ι → ℝ))) (hs : ∀ j, MeasurableSet (s j))
    (I : Finset J) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F : J → Finset (Set (E × (ι → ℝ))),
      (∀ j ∈ I, (↑(F j) : Set (Set (E × (ι → ℝ)))) ⊆
        Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
          (Set.univ.pi '' Set.univ.pi (fun _ : ι =>
            {s : Set ℝ | ∃ u v : ℝ, s = Ico u v}))) ∧
      (∀ j ∈ I, (↑(F j) : Set (Set (E × (ι → ℝ)))).PairwiseDisjoint id) ∧
      QuantumZipper.TV.tvDist
        (∑ j ∈ I, (μ j).restrict (⋃ t ∈ F j, t))
        (∑ j ∈ I, (μ j).restrict (s j)) < ε := by
  classical
  induction I using Finset.induction_on generalizing ε with
  | empty =>
      refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
      · intro j hj
        exact (Finset.notMem_empty j hj).elim
      · intro j hj
        exact (Finset.notMem_empty j hj).elim
      · simpa only [Finset.sum_empty, QuantumZipper.TV.tvDist_self] using hε
  | @insert j I hj ih =>
      have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
      obtain ⟨A, hA, hAd, hAtv⟩ :=
        exists_disjoint_finset_marked_Ico_boxes_tv_restrict_lt (μ j) (hs j) hhalf
      obtain ⟨F, hF, hFd, hFtv⟩ := ih hhalf
      refine ⟨Function.update F j A, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa only [Function.update_self] using hA
        · have hne : k ≠ j := fun h => hj (h ▸ hk)
          simpa only [Function.update_of_ne hne] using hF k hk
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa only [Function.update_self] using hAd
        · have hne : k ≠ j := fun h => hj (h ▸ hk)
          simpa only [Function.update_of_ne hne] using hFd k hk
      · have heq : (∑ k ∈ I, (μ k).restrict (⋃ t ∈ Function.update F j A k, t)) =
            ∑ k ∈ I, (μ k).restrict (⋃ t ∈ F k, t) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hne : k ≠ j := fun h => hj (h ▸ hk)
          simp only [Function.update_of_ne hne]
        rw [Finset.sum_insert hj, Finset.sum_insert hj, Function.update_self, heq]
        exact (tvDist_add_add_le _ _ _ _).trans_lt (by
          simpa only [ENNReal.add_halves] using ENNReal.add_lt_add hAtv hFtv)

end LatticeProb
