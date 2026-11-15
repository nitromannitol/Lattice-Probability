import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector
import LatticeProb.Prob.ParentBlockDyadicFiniteSelector

/-! # Refining partitions by selector fibers -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace LatticeProb.PartitionSelector

variable {X ι J : Type*}

/-- Refine each cell by the value of a measurable selector. -/
def fiberCell (E : ι → Set X) (f : X → Option J) (p : ι × Option J) : Set X :=
  E p.1 ∩ f ⁻¹' {p.2}

theorem measurableSet_fiberCell [MeasurableSpace X] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)] (E : ι → Set X) (f : X → Option J)
    (hE : ∀ i, MeasurableSet (E i)) (hf : Measurable f) (p : ι × Option J) :
    MeasurableSet (fiberCell E f p) :=
  (hE p.1).inter (hf (measurableSet_singleton p.2))

theorem pairwise_disjoint_fiberCell (E : ι → Set X) (f : X → Option J)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (fun p q => Disjoint (fiberCell E f p) (fiberCell E f q)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases h : p.1 = q.1
  · have hv : p.2 = q.2 := hx.2.symm.trans hy.2
    exact hpq (Prod.ext h hv)
  · exact Set.disjoint_left.mp (hE h) hx.1 hy.1

theorem mem_iUnion_fiberCell_iff (E : ι → Set X) (f : X → Option J) (x : X) :
    x ∈ ⋃ p, fiberCell E f p ↔ x ∈ ⋃ i, E i := by
  simp only [mem_iUnion]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, hp.1⟩
  · rintro ⟨i, hi⟩
    exact ⟨(i, f x), hi, rfl⟩

theorem fiberCell_subset (E : ι → Set X) (f : X → Option J) (p : ι × Option J) :
    fiberCell E f p ⊆ E p.1 := inter_subset_left

/-- On the union of the original cells, the refined cell selector recovers the
original selector. -/
theorem cellSelector_fiberCell (E : ι → Set X) (f : X → Option J)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (x : X)
    (hx : x ∈ ⋃ i, E i) :
    BouRabeeGwynne.cellSelector (fiberCell E f) Prod.snd x = f x := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hmem : x ∈ fiberCell E f (i, f x) := ⟨hi, rfl⟩
  have hlabel := (BouRabeeGwynne.cellLabel_eq_some_iff (fiberCell E f)
    (pairwise_disjoint_fiberCell E f hE) x (i, f x)).mpr hmem
  exact BouRabeeGwynne.cellSelector_of_label (fiberCell E f) Prod.snd hlabel

/-- A dyadic selector refines any finite measurable endpoint partition into cells
on which its dyadic square is fixed. The refined cells retain their original union. -/
theorem exists_dyadic_fiber_refinement {ι : Type*} [Fintype ι]
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option (ParentBlock.ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (ParentBlock.ParentDyadicIndex n))]
    (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → Option (ParentBlock.ParentDyadicIndex n),
      Measurable f ∧
      (∀ p, MeasurableSet (fiberCell E f p)) ∧
      Pairwise (fun p q => Disjoint (fiberCell E f p) (fiberCell E f q)) ∧
      (∀ x, x ∈ ⋃ p, fiberCell E f p ↔ x ∈ ⋃ i, E i) ∧
      (∀ x, x ∈ ⋃ i, E i →
        BouRabeeGwynne.cellSelector (fiberCell E f) Prod.snd x = f x) ∧
      (∀ x j, x ∈ ⋃ i, E i →
        BouRabeeGwynne.cellSelector (fiberCell E f) Prod.snd x = some j →
        Complex.orthonormalBasisOneI.repr.symm x ∈ ParentBlock.parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          ParentBlock.closedSquare (ParentBlock.parentDyadicCentre c S n j)
            (2 * S / (2 : ℝ) ^ n) ∧
        ball x (2 * S / (2 : ℝ) ^ n) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (ParentBlock.parentBlock (ParentBlock.parentDyadicCentre c S n j)
              (2 * S / (2 : ℝ) ^ n))) ∧
      (∀ x, x ∈ ⋃ i, E i →
        (BouRabeeGwynne.cellSelector (fiberCell E f) Prod.snd x = none ↔
          Complex.orthonormalBasisOneI.repr.symm x ∉ ParentBlock.parentBlock c S)) := by
  obtain ⟨f, hf, hsome, hnone⟩ :=
    ParentBlock.exists_measurable_finite_dyadic_selector_margin c hS n
  refine ⟨f, hf, fun p => measurableSet_fiberCell E f hE hf p,
    pairwise_disjoint_fiberCell E f hdisj, mem_iUnion_fiberCell_iff E f,
    cellSelector_fiberCell E f hdisj, ?_, ?_⟩
  · intro x j hx hj
    exact hsome x j ((cellSelector_fiberCell E f hdisj x hx).symm.trans hj)
  · intro x hx
    rw [cellSelector_fiberCell E f hdisj x hx]
    exact hnone x

end LatticeProb.PartitionSelector
