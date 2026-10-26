import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Bases

/-!
# Determinism of invariant closed random sets

A closed-set family with measurable open-hit events and pointwise invariance under an
actual ergodic map is almost surely one fixed closed set. Countably many basis-hit events
identify that set with one realized member of the family, including the empty-set case.
-/

namespace LatticeProb.Prob

open MeasureTheory TopologicalSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]

/-- Closed sets agreeing on all hits of a topological basis are equal. -/
theorem isClosed_eq_of_basis_hits {B : Set (Set X)} (hB : IsTopologicalBasis B)
    {C D : Set X} (hC : IsClosed C) (hD : IsClosed D)
    (hhit : ∀ U ∈ B, (C ∩ U).Nonempty ↔ (D ∩ U).Nonempty) : C = D := by
  have subset_of_hits : ∀ {A E : Set X}, IsClosed E →
      (∀ U ∈ B, (A ∩ U).Nonempty → (E ∩ U).Nonempty) → A ⊆ E := by
    intro A E hE hAE x hx
    by_contra hxE
    obtain ⟨U, hUB, hxU, hUE⟩ := hB.exists_subset_of_mem_open hxE hE.isOpen_compl
    obtain ⟨y, hyE, hyU⟩ := hAE U hUB ⟨x, hx, hxU⟩
    exact hUE hyU hyE
  exact Set.Subset.antisymm
    (subset_of_hits hD fun U hU => (hhit U hU).mp)
    (subset_of_hits hC fun U hU => (hhit U hU).mpr)

/-- An invariant closed-set family with measurable open hits is almost surely deterministic.
The fixed set is an actual value of the family on a common conull event. -/
theorem exists_isClosed_ae_eq_of_ergodic [SecondCountableTopology X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} (hErg : Ergodic T μ)
    (F : Ω → Set X) (hclosed : ∀ ω, IsClosed (F ω))
    (hhit : ∀ U : Set X, IsOpen U → MeasurableSet {ω | (F ω ∩ U).Nonempty})
    (hcov : ∀ ω, F (T ω) = F ω) :
    ∃ S : Set X, IsClosed S ∧ ∀ᵐ ω ∂μ, F ω = S := by
  classical
  have hbit : ∀ U : countableBasis X, ∃ b : Prop,
      ∀ᵐ ω ∂μ, (F ω ∩ (U : Set X)).Nonempty ↔ b := by
    intro U
    have hinv : T ⁻¹' {ω | (F ω ∩ (U : Set X)).Nonempty} =
        {ω | (F ω ∩ (U : Set X)).Nonempty} := by
      ext ω
      change (F (T ω) ∩ (U : Set X)).Nonempty ↔ (F ω ∩ (U : Set X)).Nonempty
      rw [hcov ω]
    rcases hErg.ae_empty_or_univ (hhit U (isOpen_of_mem_countableBasis U.property))
        hinv with h | h
    · refine ⟨False, h.mono fun ω hω => ?_⟩
      exact iff_of_eq hω
    · refine ⟨True, h.mono fun ω hω => ?_⟩
      exact iff_of_eq hω
  choose b hb using hbit
  have hcommon : ∀ᵐ ω ∂μ, ∀ U : countableBasis X,
      (F ω ∩ (U : Set X)).Nonempty ↔ b U := ae_all_iff.mpr hb
  obtain ⟨ω₀, hω₀⟩ := hcommon.exists
  refine ⟨F ω₀, hclosed ω₀, hcommon.mono fun ω hω => ?_⟩
  apply isClosed_eq_of_basis_hits (isBasis_countableBasis X) (hclosed ω) (hclosed ω₀)
  intro U hU
  exact (hω ⟨U, hU⟩).trans (hω₀ ⟨U, hU⟩).symm

end LatticeProb.Prob
