import LatticeProb.Prob.AlternatingEntryExitClocks
import Mathlib.Topology.Order.Monotone

/-! # Ordering and endpoints of entry clocks -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- An entry clock cannot precede its starting time. -/
theorem le_openEntryAfter {Ω E : Type*} (f : Ω → ℝ → E)
    (a : Ω → WithTop ℝ) (U : Set E) (ω : Ω) :
    a ω ≤ openEntryAfter f a U ω := by
  classical
  by_cases ha : a ω = ⊤
  · simp [openEntryAfter, ha]
  · have hcoe (x : WithTop ℝ) (hx : x ≠ ⊤) :
        ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
      lift x to ℝ using hx
      rfl
    simp only [openEntryAfter, ha, ↓reduceIte]
    rw [← hcoe (a ω) ha]
    exact le_hittingAfter ω

/-- A finite entry time of a continuous path has its endpoint in the closure. -/
theorem openEntryAfter_mem_closure {Ω E : Type*} [TopologicalSpace E]
    (f : Ω → ℝ → E) (a : Ω → WithTop ℝ) (U : Set E) (ω : Ω)
    (hf : Continuous (f ω)) (hfin : openEntryAfter f a U ω ≠ ⊤) :
    f ω ((openEntryAfter f a U ω).untopD 0) ∈ closure U := by
  classical
  have ha : a ω ≠ ⊤ := by
    intro h
    exact hfin (by simp [openEntryAfter, h])
  let b := (a ω).untopD 0
  let S : Set ℝ := {t | b ≤ t ∧ f ω t ∈ U}
  have hhit : ∃ t, b ≤ t ∧ f ω t ∈ U := by
    by_contra h
    apply hfin
    simp [openEntryAfter, ha, hittingAfter, b, h]
  have hne : S.Nonempty := hhit
  have hbdd : BddBelow S := ⟨b, fun _ ht => ht.1⟩
  have heq : openEntryAfter f a U ω = ((sInf S : ℝ) : WithTop ℝ) := by
    simp [openEntryAfter, ha, hittingAfter, b, S, hhit]
  rw [heq, WithTop.untopD_coe]
  exact hf.continuousWithinAt.mem_closure (csInf_mem_closure hne hbdd)
    (fun _ ht => ht.2)

end LatticeProb
