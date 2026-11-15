import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! # Adjacent intervals in a finite cover -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- In a finite closed cover by intervals with pairwise disjoint interiors,
every right endpoint before the end of the cover is the left endpoint of
another interval. -/
theorem exists_interval_successor_of_finite_cover
    {ι : Type*} [Finite ι] (c d : ℝ) (A B : ι → ℝ)
    (hne : ∀ i, A i < B i)
    (hdis : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hcover : Icc c d ⊆ ⋃ i, Icc (A i) (B i))
    (i : ι) (hci : c ≤ B i) (hid : B i < d) :
    ∃ j, j ≠ i ∧ A j = B i := by
  classical
  let F : Set ℝ := ⋃ j : {j // j ≠ i}, Icc (A j) (B j)
  have hFclosed : IsClosed F := isClosed_iUnion_of_finite (fun _ => isClosed_Icc)
  have hsub : Ioo (B i) d ⊆ F := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨hci.trans hx.1.le, hx.2.le⟩)
    have hji : j ≠ i := by
      intro h
      subst j
      linarith [hj.2, hx.1]
    exact mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
  have hend : B i ∈ F := by
    have hc := closure_mono hsub
    rw [closure_Ioo (ne_of_lt hid), hFclosed.closure_eq] at hc
    exact hc ⟨le_rfl, hid.le⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hend
  refine ⟨j, j.2, ?_⟩
  have hord := (Ioo_disjoint_Ioo).mp (hdis j.2.symm)
  have hle : B i ≤ A j := by
    simp only [min_le_iff, le_max_iff] at hord
    rcases hord with (h | h) | (h | h) <;> linarith [hne i, hne j, hj.1, hj.2]
  exact le_antisymm hj.1 hle

end LatticeProb
