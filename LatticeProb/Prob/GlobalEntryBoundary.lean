import LatticeProb.Prob.GlobalEntryFinite
import LatticeProb.Prob.GlobalEntrySegmentOutside

/-! # Boundary of a global open entry -/

set_option autoImplicit false

open Set Filter

namespace LatticeProb

/-- The global entry of a continuous path into an open set lies on its frontier
when the set of entry times is nonempty and bounded below. -/
theorem globalOpenEntry_csInf_mem_frontier {Ω E : Type*} [TopologicalSpace E]
    (f : Ω → ℝ → E) {V : Set E} (hV : IsOpen V) (ω : Ω)
    (hf : Continuous (f ω)) (hne : {t | f ω t ∈ V}.Nonempty)
    (hb : BddBelow {t | f ω t ∈ V}) :
    f ω (sInf {t | f ω t ∈ V}) ∈ frontier V := by
  have hclosure := globalOpenEntry_csInf_mem_closure f V ω hf hne hb
  have heq := globalOpenEntry_eq_coe_csInf f V ω hne hb
  have hout := globalOpenEntry_not_mem_of_eq_coe f hV ω hf heq
  rw [frontier, hV.interior_eq]
  exact ⟨hclosure, hout⟩

/-- A transient complex path visiting a bounded open set has a finite global
entry clock whose endpoint lies on the frontier. -/
theorem transient_globalEntry_finite_mem_frontier
    (c : C(ℝ, ℂ)) {V : Set ℂ} (hVopen : IsOpen V)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hV : Bornology.IsBounded V) (hvisit : ∃ t, c t ∈ V) :
    ∃ t : ℝ, globalOpenEntry (fun (_ : Unit) t => c t) V () = (t : EReal) ∧
      entryClockOfEReal (globalOpenEntry (fun (_ : Unit) t => c t) V ()) =
        (t : WithTop ℝ) ∧ c t ∈ frontier V := by
  obtain ⟨t, heq, hclock, hclosure⟩ :=
    transient_globalEntry_finite_mem_closure c V htr hV hvisit
  refine ⟨t, heq, hclock, ?_⟩
  rw [frontier, hVopen.interior_eq]
  exact ⟨hclosure, globalOpenEntry_not_mem_of_eq_coe
    (fun (_ : Unit) t => c t) hVopen () c.continuous heq⟩

end LatticeProb
