import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Basic.Real.Basic

/-! # Open sets almost everywhere equal to an interval -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An open set which agrees almost everywhere with a nonempty open interval is contained
in its closure and has rational points arbitrarily close to each endpoint. -/
theorem rational_visits_of_open_ae_interval (μ : Measure ℝ) [Measure.IsOpenPosMeasure μ]
    (S : Set ℝ) (a b : ℝ) (hS : IsOpen S) (hab : a < b)
    (hae : ∀ᵐ x ∂μ, x ∈ S ↔ x ∈ Ioo a b) :
    (∀ q : ℚ, (q : ℝ) ∈ S → a ≤ q ∧ (q : ℝ) ≤ b) ∧
    (∀ t : ℝ, a < t → ∃ q : ℚ, (q : ℝ) ∈ S ∧ (q : ℝ) < t) ∧
    (∀ t : ℝ, t < b → ∃ q : ℚ, (q : ℝ) ∈ S ∧ t < (q : ℝ)) := by
  have hd : Dense {x : ℝ | x ∈ S ↔ x ∈ Ioo a b} := μ.dense_of_ae hae
  have hbound : S ⊆ Icc a b := by
    intro x hx
    by_contra hnot
    obtain ⟨y, hygood, hy⟩ := hd.exists_mem_open
      (hS.inter isClosed_Icc.isOpen_compl) ⟨x, hx, hnot⟩
    have hyI : y ∈ Ioo a b := hygood.mp hy.1
    exact hy.2 ⟨le_of_lt hyI.1, le_of_lt hyI.2⟩
  have hrat : ∀ V : Set ℝ, IsOpen V → V.Nonempty → ∃ q : ℚ, (q : ℝ) ∈ V := by
    intro V hV hne
    exact (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).exists_mem_open hV hne
  constructor
  · intro q hq
    exact hbound hq
  constructor
  · intro t hat
    have hlt : a < min t b := lt_min hat hab
    obtain ⟨x, hxgood, hx⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hlt)
    have hxS : x ∈ S := hxgood.mpr ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
    have hxt : x < t := lt_of_lt_of_le hx.2 (min_le_left _ _)
    obtain ⟨q, hq⟩ := hrat (S ∩ Iio t) (hS.inter isOpen_Iio) ⟨x, hxS, hxt⟩
    exact ⟨q, hq.1, hq.2⟩
  · intro t htb
    have hlt : max a t < b := max_lt hab htb
    obtain ⟨x, hxgood, hx⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hlt)
    have hxS : x ∈ S := hxgood.mpr ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
    have htx : t < x := lt_of_le_of_lt (le_max_right _ _) hx.1
    obtain ⟨q, hq⟩ := hrat (S ∩ Ioi t) (hS.inter isOpen_Ioi) ⟨x, hxS, htx⟩
    exact ⟨q, hq.1, hq.2⟩

end LatticeProb
