import Mathlib

/-!
# Almost sure transfer of membership along equality in law

If `X` and `X'` have the same distribution and `E` is a measurable set with `X' ∈ E` almost surely, then
`X ∈ E` almost surely. This is the almost sure form of `IdentDistrib.measure_mem_eq`: the two laws give the
same mass to `E`, hence to its complement, and the complement is null on the side where `X'` lies in `E`.

Mathlib proves the transfer in the direction `X ↦ X'` as `IdentDistrib.ae_mem_snd`; the statement here is
that lemma applied to `IdentDistrib.symm`.

Literature: Kallenberg, *Foundations of Modern Probability* (2nd ed.), Ch. 1 (random elements and their
distributions).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- Equality in law transfers almost sure membership in a measurable set: if `X` and `X'` have the same
distribution and `X' ∈ E` almost surely, then `X ∈ E` almost surely. -/
theorem ae_of_identDistrib {Ω Ω' α : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α] {P : Measure Ω}
    {P' : Measure Ω'} {X : Ω → α} {X' : Ω' → α} (h : IdentDistrib X X' P P') {E : Set α} (hE : MeasurableSet E)
    (hE' : ∀ᵐ ω' ∂P', X' ω' ∈ E) : ∀ᵐ ω ∂P, X ω ∈ E :=
  h.symm.ae_mem_snd hE hE'

end LatticeProb
