import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector
import LatticeProb.Prob.ParentBlockDyadicFiniteSelector

/-! # Dyadic parent-block choices for small partition cells -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace LatticeProb.ParentBlock

/-- Choose one dyadic parent block for each cell meeting the active region.
The chosen block has a uniform interior margin at every point of the cell. -/
theorem exists_partition_dyadic_choice
    {ι : Type*} [Fintype ι] [MeasurableSpace (Option ι)]
    [MeasurableSingletonClass (Option ι)]
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (hC : C ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S)
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
      dist y x ≤ (2 * S / (2 : ℝ) ^ n) / 2)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ x ∈ C, ∃ i, x ∈ E i) :
    ∃ choice : ι → Option (ParentDyadicIndex n),
      Measurable (BouRabeeGwynne.cellSelector E choice) ∧
      (∀ x ∈ C, BouRabeeGwynne.cellSelector E choice x ≠ none) ∧
      ∀ x j, BouRabeeGwynne.cellSelector E choice x = some j →
        ball x ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)) := by
  classical
  obtain ⟨f, _, hsome, hnone⟩ := exists_measurable_finite_dyadic_selector_margin c hS n
  have hex (i : ι) : ∃ b : Option (ParentDyadicIndex n),
      (b = none ↔ E i ∩ C = ∅) ∧
      ∀ j, b = some j → ∀ y ∈ E i,
        ball y ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)) := by
    by_cases he : (E i ∩ C).Nonempty
    · obtain ⟨x, hxi, hxC⟩ := he
      have hf : f x ≠ none := by
        intro hn
        exact ((hnone x).mp hn) (hC hxC)
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hf
      refine ⟨some j, ?_, ?_⟩
      · simp only [Option.some_ne_none, false_iff]
        exact (show (E i ∩ C).Nonempty from ⟨x, hxi, hxC⟩).ne_empty
      · intro k hk y hy z hz
        have hkj : j = k := Option.some.inj hk
        subst k
        apply (hsome x j hj).2.2
        rw [mem_ball] at hz ⊢
        have hd := hdiam i x hxi y hy
        calc
          dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
          _ < (2 * S / (2 : ℝ) ^ n) / 2 + (2 * S / (2 : ℝ) ^ n) / 2 :=
            add_lt_add_of_lt_of_le hz hd
          _ = 2 * S / (2 : ℝ) ^ n := by ring
    · refine ⟨none, ?_, ?_⟩
      · simp only [true_iff]
        exact Set.not_nonempty_iff_eq_empty.mp he
      · intro j hj
        cases hj
  choose choice hnoneChoice hmargin using hex
  refine ⟨choice, BouRabeeGwynne.measurable_cellSelector E choice hdisj hE, ?_, ?_⟩
  · intro x hx hn
    obtain ⟨i, hi⟩ := hcover x hx
    have hl := (BouRabeeGwynne.cellLabel_eq_some_iff E hdisj x i).mpr hi
    have hc : choice i = none := by
      rw [← BouRabeeGwynne.cellSelector_of_label E choice hl]
      exact hn
    exact (Set.notMem_empty x) ((hnoneChoice i).mp hc ▸ (show x ∈ E i ∩ C from ⟨hi, hx⟩))
  · intro x j hj
    obtain ⟨i, hi, hc⟩ := BouRabeeGwynne.cellSelector_some_mem E choice hj
    exact hmargin i j hc x hi

end LatticeProb.ParentBlock
