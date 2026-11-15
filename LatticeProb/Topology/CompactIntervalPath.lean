import LatticeProb.Topology.CompactUniformLocalConnected

/-! # Local connectedness of compact interval path images -/

set_option autoImplicit false

open Set
open scoped Topology

namespace LatticeProb.Topology

/-- The image of a continuous path on a compact real interval is locally connected. -/
theorem isLocallyConnectedSet_image_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : IsLocallyConnectedSet (f '' Icc a b) := by
  let φ : ℝ → ℝ := AffineMap.lineMap a b
  have himage : φ '' Icc 0 1 = Icc a b := by
    rw [← segment_eq_image_lineMap, segment_eq_Icc hab]
  have hφ : Continuous φ := by
    exact AffineMap.lineMap_continuous
  have hcomp : ContinuousOn (f ∘ φ) (Icc 0 1) :=
    hf.comp hφ.continuousOn (fun t ht => himage ▸ mem_image_of_mem φ ht)
  have h := isLocallyConnectedSet_image_unitInterval hcomp
  rwa [image_comp, himage] at h

end LatticeProb.Topology
