import LatticeProb.Topology.ComponentVisitIdentity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.DenselyOrdered

/-! # Confinement of visits to open sets -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An open set of real numbers that agrees almost everywhere with an open
interval is contained in that interval, including when the interval is empty. -/
theorem isOpen_subset_Ioo_of_ae_iff {μ : Measure ℝ} [Measure.IsOpenPosMeasure μ]
    {V : Set ℝ} {a b : ℝ} (hV : IsOpen V)
    (h : ∀ᵐ t ∂μ, t ∈ V ↔ t ∈ Ioo a b) : V ⊆ Ioo a b := by
  have hd : Dense {t : ℝ | t ∈ V ↔ t ∈ Ioo a b} := μ.dense_of_ae h
  have hsub : V ⊆ Icc a b := by
    intro t ht
    by_contra hn
    obtain ⟨x, hx, hx'⟩ := hd.exists_mem_open (hV.inter isClosed_Icc.isOpen_compl)
      ⟨t, ht, hn⟩
    have hi := hx.mp hx'.1
    exact hx'.2 ⟨hi.1.le, hi.2.le⟩
  rw [← interior_Icc]
  exact interior_maximal hsub hV

/-- An area-parametrized continuous curve cannot visit an open set outside the
interior of an interval whose image is its closure, if its frontier is null. -/
theorem preimage_open_subset_Ioo_of_area_curve
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (U : Set E) (a b : ℝ)
    (hη : Continuous η) (hmap : Measure.map η volume = μ)
    (hU : IsOpen U) (hfrontier : μ (frontier U) = 0)
    (himage : η '' Icc a b = closure U)
    (hmass : μ (η '' Icc a b) = volume (Icc a b)) :
    η ⁻¹' U ⊆ Ioo a b := by
  apply isOpen_subset_Ioo_of_ae_iff (μ := volume) (hU.preimage hη)
  exact ae_visit_open_eq_interval η μ U a b hη.measurable hmap hU hfrontier himage hmass

end LatticeProb
