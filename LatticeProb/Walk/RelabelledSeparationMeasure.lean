import LatticeProb.Walk.RelabelledTraceSeparation

/-! # Separation probabilities under relabelling -/

set_option autoImplicit false

open Set MeasureTheory MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb

/-- A measurable graph isomorphism preserves the measure of the event that the
pre-hit trace separates two sets. The event need not be measurable. -/
theorem measure_graphSeparates_traceBefore_map {V W : Type*}
    [MeasurableSpace V] [MeasurableSpace W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (he : Measurable e) (hes : Measurable e.symm)
    (I A B : Set W) (Q : Measure (ℕ → V)) :
    (Q.map (fun x n => e (x n)))
        {x | GraphSeparates H (traceBefore id I x) A B} =
      Q {x | GraphSeparates G (traceBefore id (e ⁻¹' I) x) (e ⁻¹' A) (e ⁻¹' B)} := by
  let f : V ≃ᵐ W := ⟨e.toEquiv, he, hes⟩
  let F : (ℕ → V) ≃ᵐ (ℕ → W) := MeasurableEquiv.piCongrRight (fun _ => f)
  change (Q.map F) {x | GraphSeparates H (traceBefore id I x) A B} = _
  rw [F.map_apply]
  congr 1
  ext x
  exact (graphSeparates_traceBefore_map_iff e I A B x).symm

end LatticeProb
