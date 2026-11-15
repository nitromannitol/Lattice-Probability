import LatticeProb.LQG.MatingOfTreesCouplingMergeScaling

/-! # Positive scaling of contour coordinates -/

set_option autoImplicit false

open MatedCRTHarmonic.MatedCRT

namespace LatticeProb

/-- Positive amplitude scaling leaves direct contour identifications unchanged. -/
theorem directRel_mul_iff (X : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (s t : ℝ) :
    DirectRel (fun u => c * X u) s t ↔ DirectRel X s t := by
  simpa only [one_mul] using directRel_smul_comp_mul_iff (by norm_num : (0 : ℝ) < 1) hc X s t

/-- Independent positive scalings of two contour coordinates leave their
    generated equivalence relation unchanged, with the same time parameter. -/
theorem eqvGen_directRel_mul_iff (X Y : ℝ → ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (s t : ℝ) :
    Relation.EqvGen (fun a b => DirectRel (fun u => c * X u) a b ∨
      DirectRel (fun u => d * Y u) a b) s t ↔
    Relation.EqvGen (fun a b => DirectRel X a b ∨ DirectRel Y a b) s t := by
  have hrel : (fun a b => DirectRel (fun u => c * X u) a b ∨
      DirectRel (fun u => d * Y u) a b) =
      (fun a b => DirectRel X a b ∨ DirectRel Y a b) := by
    funext a b
    exact propext (or_congr (directRel_mul_iff X hc a b) (directRel_mul_iff Y hd a b))
  rw [hrel]

end LatticeProb
