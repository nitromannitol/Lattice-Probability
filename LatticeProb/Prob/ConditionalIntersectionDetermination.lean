import LatticeProb.Prob.AdaptedStandardBorel

/-! # Determination from conditionally independent information -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {G A B C : MeasurableSpace Ω}

/-- An observable determined up to null sets by each of two conditionally independent
σ-algebras is already determined by the conditioning σ-algebra. -/
theorem AELeSigma.of_condIndepEv_two_sides [IsProbabilityMeasure μ]
    (hGA : G ≤ A) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : CondIndepEv G A B μ)
    (hCA : AELeSigma C A μ) (hCB : AELeSigma C B μ) :
    AELeSigma C G μ := by
  apply AELeSigma.of_condIndepEv_past le_rfl hGA hA hB h.symm hCA
  intro s hs
  obtain ⟨t, ht, heq⟩ := hCB s hs
  exact ⟨t, (show B ≤ G ⊔ B from le_sup_right) t ht, heq⟩

/-- A standard Borel-valued observable determined by both conditionally independent
σ-algebras is a measurable function of the conditioning variable almost surely. -/
theorem aeDeterminedBy_of_condIndepEv_two_sides [IsProbabilityMeasure μ]
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β] {X : Ω → α} {Y : Ω → β}
    (hXA : mα.comap X ≤ A) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : CondIndepEv (mα.comap X) A B μ)
    (hYA : AELeSigma (mβ.comap Y) A μ) (hYB : AELeSigma (mβ.comap Y) B μ) :
    @AEDeterminedBy Ω mΩ α β mα mβ Y X μ :=
  aeDeterminedBy_of_aeDeterminedSigma
    (AELeSigma.of_condIndepEv_two_sides hXA hA hB h hYA hYB)

end LatticeProb
