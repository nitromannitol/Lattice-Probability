import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith

/-! # Finite almost-everywhere interval coverage -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- If finitely many subsets cover an open set almost everywhere, their closed
supersets cover it everywhere, for a measure positive on nonempty open sets. -/
theorem open_subset_iUnion_closed_of_ae_cover
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [Finite ι]
    (μ : Measure X) [Measure.IsOpenPosMeasure μ] (U : Set X) (I F : ι → Set X)
    (hU : IsOpen U) (hF : ∀ i, IsClosed (F i)) (hIF : ∀ i, I i ⊆ F i)
    (hcover : μ (U \ ⋃ i, I i) = 0) : U ⊆ ⋃ i, F i := by
  have hclosed : IsClosed (⋃ i, F i) := isClosed_iUnion_of_finite hF
  have hnull : μ (U \ ⋃ i, F i) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right (iUnion_mono hIF)) hcover
  exact sdiff_eq_empty.mp ((hU.sdiff hclosed).eq_empty_of_measure_zero hnull)

/-- A finite almost-everywhere cover of an open interval by open intervals
covers its closure by the corresponding closed intervals. -/
theorem closed_interval_subset_of_ae_finite_interval_cover
    {ι : Type*} [Finite ι] (c d : ℝ) (A B : ι → ℝ) (hcd : c < d)
    (hcover : volume (Ioo c d \ ⋃ i, Ioo (A i) (B i)) = 0) :
    Icc c d ⊆ ⋃ i, Icc (A i) (B i) := by
  have h := open_subset_iUnion_closed_of_ae_cover volume (Ioo c d)
    (fun i => Ioo (A i) (B i)) (fun i => Icc (A i) (B i))
    isOpen_Ioo (fun _ => isClosed_Icc) (fun _ => Ioo_subset_Icc_self) hcover
  have hc := closure_mono h
  rw [closure_Ioo (ne_of_lt hcd), (isClosed_iUnion_of_finite (fun _ => isClosed_Icc)).closure_eq] at hc
  exact hc

/-- Under containment in a bounded interval, a finite almost-everywhere cover
has intervals attaining each endpoint of the bounded interval. -/
theorem endpoints_of_ae_finite_interval_cover
    {ι : Type*} [Finite ι] (c d : ℝ) (A B : ι → ℝ) (hcd : c < d)
    (hbounds : ∀ i, c ≤ A i ∧ B i ≤ d)
    (hcover : volume (Ioo c d \ ⋃ i, Ioo (A i) (B i)) = 0) :
    (∃ i, A i = c) ∧ ∃ j, B j = d := by
  have h := closed_interval_subset_of_ae_finite_interval_cover c d A B hcd hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (h ⟨le_rfl, hcd.le⟩)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (h ⟨hcd.le, le_rfl⟩)
  exact ⟨⟨i, le_antisymm hi.1 (hbounds i).1⟩,
    ⟨j, le_antisymm (hbounds j).2 hj.2⟩⟩

end LatticeProb
