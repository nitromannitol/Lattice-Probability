import LatticeProb.Prob.TransientGlobalEntry
import Mathlib.Topology.Order.Monotone

/-! # Finite global entry times -/

set_option autoImplicit false

open Set Filter

namespace LatticeProb

/-- The global entry is the real infimum when hit times are nonempty and bounded below. -/
theorem globalOpenEntry_eq_coe_csInf {Ω E : Type*} (f : Ω → ℝ → E)
    (V : Set E) (ω : Ω) (hne : {t | f ω t ∈ V}.Nonempty)
    (hb : BddBelow {t | f ω t ∈ V}) :
    globalOpenEntry f V ω = ((sInf {t | f ω t ∈ V} : ℝ) : EReal) := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨u, hu⟩ := hne
  have hbot := globalOpenEntry_ne_bot_of_lower_bound f V ω a ha
  have htop : globalOpenEntry f V ω ≠ ⊤ := by
    have hle : globalOpenEntry f V ω ≤ (u : EReal) := sInf_le ⟨u, hu, rfl⟩
    exact ne_top_of_le_ne_top (EReal.coe_ne_top u) hle
  obtain ⟨c, hc, _⟩ := (entryClockOfEReal_spec hbot).resolve_left (fun h => htop h.1)
  rw [hc]
  congr 1
  apply le_antisymm
  · apply le_csInf ⟨u, hu⟩
    intro t ht
    apply EReal.coe_le_coe_iff.mp
    rw [← hc]
    exact sInf_le ⟨t, ht, rfl⟩
  · have h : ((sInf {t | f ω t ∈ V} : ℝ) : EReal) ≤ globalOpenEntry f V ω := by
      apply le_sInf
      rintro x ⟨t, ht, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (csInf_le ⟨a, ha⟩ ht)
    rw [hc] at h
    exact EReal.coe_le_coe_iff.mp h

/-- A continuous path at its finite global entry lies in the closure of the target. -/
theorem globalOpenEntry_csInf_mem_closure {Ω E : Type*} [TopologicalSpace E]
    (f : Ω → ℝ → E) (V : Set E) (ω : Ω)
    (hf : Continuous (f ω)) (hne : {t | f ω t ∈ V}.Nonempty)
    (hb : BddBelow {t | f ω t ∈ V}) :
    f ω (sInf {t | f ω t ∈ V}) ∈ closure V := by
  exact (hf.continuousAt.continuousWithinAt).mem_closure
    (csInf_mem_closure hne hb) (fun _ ht => ht)

/-- A visit to a bounded set by a transient complex path has a finite global entry,
and the path at that time lies in the closure of the set. -/
theorem transient_globalEntry_finite_mem_closure
    (c : C(ℝ, ℂ)) (V : Set ℂ)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hV : Bornology.IsBounded V) (hvisit : ∃ t, c t ∈ V) :
    ∃ t : ℝ, globalOpenEntry (fun (_ : Unit) t => c t) V () = (t : EReal) ∧
      entryClockOfEReal (globalOpenEntry (fun (_ : Unit) t => c t) V ()) =
        (t : WithTop ℝ) ∧ c t ∈ closure V := by
  obtain ⟨a, ha⟩ := MatedCRTHarmonic.GMS4c.exists_past_outside htr hV
  have hb : BddBelow {t | c t ∈ V} := by
    refine ⟨a, fun t ht => ?_⟩
    exact le_of_not_gt (fun h => ha t h ht)
  let t : ℝ := sInf {t | c t ∈ V}
  have heq : globalOpenEntry (fun (_ : Unit) t => c t) V () = (t : EReal) :=
    globalOpenEntry_eq_coe_csInf _ V () hvisit hb
  refine ⟨t, heq, ?_, ?_⟩
  · rw [heq, entryClockOfEReal_coe]
  · exact globalOpenEntry_csInf_mem_closure (fun (_ : Unit) t => c t) V ()
      c.continuous hvisit hb

end LatticeProb
