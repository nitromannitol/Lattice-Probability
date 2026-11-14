import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Chain

/-! # Relabelling hitting times and traces -/

set_option autoImplicit false

noncomputable section

open Set MatedCRTHarmonic.Markov MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb

/-- A mapped path hits a set at the same time as the original path hits its preimage. -/
theorem hitTime_map {V W : Type*} (f : V → W) (I : Set W) (x : ℕ → V) :
    hitTime I (fun n => f (x n)) = hitTime (f ⁻¹' I) x := rfl

/-- The pre-hit trace of a mapped path is the image of the original pre-hit trace. -/
theorem traceBefore_map {V W : Type*} (f : V → W) (I : Set W) (x : ℕ → V) :
    traceBefore id I (fun n => f (x n)) = f '' traceBefore id (f ⁻¹' I) x := by
  ext w
  simp only [traceBefore, Set.preimage_id, Set.mem_ofPred_eq, id_eq, hitTime_map, Set.mem_image]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨x n, ⟨n, hn, rfl⟩, heq⟩
  · rintro ⟨v, ⟨n, hn, rfl⟩, hv⟩
    exact ⟨n, hn, hv⟩

end LatticeProb

end
