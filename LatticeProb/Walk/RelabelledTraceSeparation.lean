import LatticeProb.Walk.RelabelledHittingTrace
import LatticeProb.Walk.RelabelledGraphSeparation

/-! # Separation by relabelled pre-hit traces -/

set_option autoImplicit false

open Set MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb

/-- A graph isomorphism preserves separation by the trace before the first hit. -/
theorem graphSeparates_traceBefore_map_iff {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (I A B : Set W) (x : ℕ → V) :
    GraphSeparates G (traceBefore id (e ⁻¹' I) x) (e ⁻¹' A) (e ⁻¹' B) ↔
      GraphSeparates H (traceBefore id I (fun n => e (x n))) A B := by
  rw [traceBefore_map (fun v => e v) I x]
  have h := graphSeparates_preimage_iff e (e '' traceBefore id (e ⁻¹' I) x) A B
  rw [Set.preimage_image_eq _ e.injective] at h
  exact h

end LatticeProb
