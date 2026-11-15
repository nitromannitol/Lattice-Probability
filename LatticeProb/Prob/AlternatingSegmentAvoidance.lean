import LatticeProb.Prob.AlternatingSegmentEndpoints
import Mathlib.Topology.Order.DenselyOrdered

/-! # Avoidance by segments ending at open-set entry times -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A continuous path started outside an open set stays outside through its finite first entry. -/
theorem image_Icc_untopD_openEntryAfter_subset_compl {Ω E : Type*} [TopologicalSpace E]
    (f : Ω → ℝ → E) (a : Ω → WithTop ℝ) {U : Set E} (hU : IsOpen U)
    (ω : Ω) (hf : Continuous (f ω)) (ha : a ω ≠ ⊤)
    (he : openEntryAfter f a U ω ≠ ⊤) (hstart : f ω ((a ω).untopD 0) ∉ U) :
    f ω '' Icc ((a ω).untopD 0) ((openEntryAfter f a U ω).untopD 0) ⊆ Uᶜ := by
  classical
  let b := (a ω).untopD 0
  let e := (openEntryAfter f a U ω).untopD 0
  have hcoe (x : WithTop ℝ) (hx : x ≠ ⊤) : ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
    lift x to ℝ using hx
    rfl
  have hbefore : Ico b e ⊆ (f ω) ⁻¹' Uᶜ := by
    intro t ht
    change f ω t ∉ U
    apply notMem_of_lt_hittingAfter (n := b) (u := fun t ω => f ω t) (ω := ω) ?_ ht.1
    have ht' : (t : WithTop ℝ) < openEntryAfter f a U ω := by
      rw [← hcoe (openEntryAfter f a U ω) he]
      exact WithTop.coe_lt_coe.mpr ht.2
    simpa only [openEntryAfter, ha, ↓reduceIte, b] using ht'
  have hclosed : IsClosed ((f ω) ⁻¹' Uᶜ) := hU.isClosed_compl.preimage hf
  have hall : Icc b e ⊆ (f ω) ⁻¹' Uᶜ := by
    by_cases h : b = e
    · rw [h, Icc_self]
      intro t ht
      simp only [mem_singleton_iff] at ht
      subst t
      change f ω e ∉ U
      rw [← h]
      exact hstart
    · rw [← closure_Ico h]
      exact closure_minimal hbefore hclosed
  exact image_subset_iff.mpr hall

/-- Each finite alternating segment avoids the inner open set if its starting point does. -/
theorem alternatingSegment_image_subset_compl {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (ω : Ω) (n : ℕ)
    (hn : n < alternatingExcursionCount f a U V ω)
    (hstart : f ω ((alternatingExitClock f a U V n ω).untopD 0) ∉ U) :
    f ω '' Icc ((alternatingExitClock f a U V n ω).untopD 0)
      ((openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω).untopD 0) ⊆ Uᶜ := by
  obtain ⟨hx, hy, _⟩ := alternatingSegmentEndpoints_of_lt f a U V ω n hn
  exact image_Icc_untopD_openEntryAfter_subset_compl
    (fun ω t => f ω t) (alternatingExitClock f a U V n) hU ω (f ω).continuous hx hy hstart

end LatticeProb
