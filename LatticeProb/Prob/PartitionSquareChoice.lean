import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector
import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Square choices for endpoint partitions -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace LatticeProb.ParentBlock

/-- An endpoint partition cell meeting an active region can be assigned a square
containing the whole cell and lying in an outer region. -/
theorem exists_partition_square_choices
    {ι J : Type*} (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (C O : Set (EuclideanSpace ℝ (Fin 2))) (centres : J → ℂ) (s d : ℝ)
    (hcover : ∀ x ∈ C, ∃ j, Complex.orthonormalBasisOneI.repr.symm x ∈
      closedSquare (centres j) s)
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist y x ≤ d)
    (houter : ∀ x ∈ C, ∀ y, dist y x ≤ d → y ∈ O) :
    ∃ choice : ι → Option J,
      (∀ i, choice i = none ↔ E i ∩ C = ∅) ∧
      ∀ i j, choice i = some j → ∀ y ∈ E i,
        y ∈ O ∧ Complex.orthonormalBasisOneI.repr.symm y ∈
          closedSquare (centres j) (s + 2 * d) := by
  classical
  have hchoice (i : ι) : ∃ b : Option J,
      (b = none ↔ E i ∩ C = ∅) ∧
      ∀ j, b = some j → ∀ y ∈ E i,
        y ∈ O ∧ Complex.orthonormalBasisOneI.repr.symm y ∈
          closedSquare (centres j) (s + 2 * d) := by
    by_cases he : (E i ∩ C).Nonempty
    · obtain ⟨x, hx, hxC⟩ := he
      obtain ⟨j, hj⟩ := hcover x hxC
      refine ⟨some j, ?_, ?_⟩
      · simp only [Option.some_ne_none, false_iff]
        exact (show (E i ∩ C).Nonempty from ⟨x, hx, hxC⟩).ne_empty
      · intro k hk y hy
        have hkj : j = k := Option.some.inj hk
        subst k
        have hd := hdiam i x hx y hy
        have hnorm : ‖Complex.orthonormalBasisOneI.repr.symm y -
            Complex.orthonormalBasisOneI.repr.symm x‖ ≤ d := by
          rw [← dist_eq_norm, Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq]
          exact hd
        have hre := (Complex.abs_re_le_norm
          (Complex.orthonormalBasisOneI.repr.symm y -
            Complex.orthonormalBasisOneI.repr.symm x)).trans hnorm
        have him := (Complex.abs_im_le_norm
          (Complex.orthonormalBasisOneI.repr.symm y -
            Complex.orthonormalBasisOneI.repr.symm x)).trans hnorm
        have h₁ := abs_add_le
          ((Complex.orthonormalBasisOneI.repr.symm y).re -
            (Complex.orthonormalBasisOneI.repr.symm x).re)
          ((Complex.orthonormalBasisOneI.repr.symm x).re - (centres j).re)
        have h₂ := abs_add_le
          ((Complex.orthonormalBasisOneI.repr.symm y).im -
            (Complex.orthonormalBasisOneI.repr.symm x).im)
          ((Complex.orthonormalBasisOneI.repr.symm x).im - (centres j).im)
        change |(Complex.orthonormalBasisOneI.repr.symm x).re - (centres j).re| ≤ s / 2 ∧
          |(Complex.orthonormalBasisOneI.repr.symm x).im - (centres j).im| ≤ s / 2 at hj
        simp only [Complex.sub_re] at hre
        simp only [Complex.sub_im] at him
        refine ⟨houter x hxC y hd, ?_⟩
        change |(Complex.orthonormalBasisOneI.repr.symm y).re - (centres j).re| ≤
          (s + 2 * d) / 2 ∧
          |(Complex.orthonormalBasisOneI.repr.symm y).im - (centres j).im| ≤
          (s + 2 * d) / 2
        simp only [sub_add_sub_cancel] at h₁ h₂
        constructor <;> linarith
    · refine ⟨none, ?_, ?_⟩
      · simp only [true_iff]
        exact Set.not_nonempty_iff_eq_empty.mp he
      · intro j hj
        cases hj
  choose choice hnone hsome using hchoice
  exact ⟨choice, hnone, hsome⟩

/-- A measurable finite partition admits a selector which stays active on the
active region, with a uniform parent-block margin at each selected point. -/
theorem exists_partition_square_selector
    {ι J : Type*} [Fintype ι] [MeasurableSpace (Option ι)]
    [MeasurableSingletonClass (Option ι)] [MeasurableSpace (Option J)]
    (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (C O : Set (EuclideanSpace ℝ (Fin 2))) (centres : J → ℂ) (s d : ℝ)
    (hside : 0 < s + 2 * d)
    (hcover : ∀ x ∈ C, ∃ j, Complex.orthonormalBasisOneI.repr.symm x ∈
      closedSquare (centres j) s)
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist y x ≤ d)
    (houter : ∀ x ∈ C, ∀ y, dist y x ≤ d → y ∈ O)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hEC : ∀ x ∈ C, ∃ i, x ∈ E i) :
    ∃ choice : ι → Option J,
      Measurable (BouRabeeGwynne.cellSelector E choice) ∧
      (∀ x ∈ C, BouRabeeGwynne.cellSelector E choice x ≠ none) ∧
      ∀ x j, BouRabeeGwynne.cellSelector E choice x = some j →
        x ∈ O ∧ Complex.orthonormalBasisOneI.repr.symm x ∈
          closedSquare (centres j) (s + 2 * d) ∧
        ball x (s + 2 * d) ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (parentBlock (centres j) (s + 2 * d)) := by
  obtain ⟨choice, hnone, hsome⟩ :=
    exists_partition_square_choices E C O centres s d hcover hdiam houter
  refine ⟨choice, BouRabeeGwynne.measurable_cellSelector E choice hdisj hE, ?_, ?_⟩
  · intro x hx hxnone
    obtain ⟨i, hxi⟩ := hEC x hx
    have hlabel := (BouRabeeGwynne.cellLabel_eq_some_iff E hdisj x i).mpr hxi
    have hchoice : choice i = none := by
      rw [← BouRabeeGwynne.cellSelector_of_label E choice hlabel]
      exact hxnone
    have hempty := (hnone i).mp hchoice
    exact Set.notMem_empty x (hempty ▸ (show x ∈ E i ∩ C from ⟨hxi, hx⟩))
  · intro x j hx
    obtain ⟨i, hxi, hi⟩ := BouRabeeGwynne.cellSelector_some_mem E choice hx
    obtain ⟨hout, hsquare⟩ := hsome i j hi x hxi
    refine ⟨hout, hsquare, ?_⟩
    intro y hy
    apply ball_subset_interior_parentBlock hside.le hsquare
    rw [mem_ball] at hy ⊢
    simpa only [Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq] using hy

end LatticeProb.ParentBlock
