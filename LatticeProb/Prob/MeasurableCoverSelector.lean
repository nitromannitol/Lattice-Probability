import LatticeProb.Prob.Scaling.MeasurableLocalChoice

/-!
# Measurable selectors for countable covers

A measurable continuation set covered by countably many measurable sets admits a measurable
index selector which returns `none` exactly outside the continuation set.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Select a member of a countable measurable cover on `C`, and stop outside `C`. -/
theorem exists_measurable_cover_selector {α : Type*} [MeasurableSpace α] [MeasurableSpace (Option ℕ)]
    (C : Set α) (A : ℕ → Set α) (hC : MeasurableSet C)
    (hA : ∀ n, MeasurableSet (A n)) (hcover : C ⊆ ⋃ n, A n) :
    ∃ f : α → Option ℕ, Measurable f ∧
      (∀ x n, f x = some n → x ∈ C ∧ x ∈ A n) ∧
      (∀ x ∈ C, ∃ n, f x = some n) ∧
      (∀ x, f x = none ↔ x ∉ C) := by
  let p : ℕ → α → Prop := fun n x => x ∈ C ∧ x ∈ A n
  have hp : ∀ n, MeasurableSet {x | p n x} := fun n => hC.inter (hA n)
  obtain ⟨f, hf, hsome, hnone⟩ :=
    Scaling.MeasurableLocalChoice.exists_measurable_selection p hp
      (fun n _ => some n) (fun _ => measurable_const) (fun _ => none) measurable_const
  have hex : ∀ x ∈ C, ∃ n, p n x := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨n, hx, hn⟩
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro x n hfn
    by_cases h : ∃ k, p k x
    · obtain ⟨k, hk, hfk⟩ := hsome x h
      have heq : k = n := Option.some.inj (hfk.symm.trans hfn)
      simpa only [heq] using hk
    · rw [hnone x h] at hfn
      cases hfn
  · intro x hx
    obtain ⟨n, _, hn⟩ := hsome x (hex x hx)
    exact ⟨n, hn⟩
  · intro x
    constructor
    · intro hfnone hx
      obtain ⟨n, _, hn⟩ := hsome x (hex x hx)
      rw [hfnone] at hn
      cases hn
    · intro hx
      exact hnone x (fun ⟨n, hn⟩ => hx hn.1)

end LatticeProb
