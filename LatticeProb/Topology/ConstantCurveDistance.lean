import LatticeProb.Topology.CurveSpace

/-! # Distance from a constant curve -/

set_option autoImplicit false
open scoped ENNReal unitInterval

namespace LatticeProb.CurveSpace

/-- The distance from a constant curve to a normalized curve is the supremum
of their pointwise spatial distances. -/
theorem edist_const_mk {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (g : NormalizedCurve d) :
    edist (mk (NormalizedCurve.const x)) (mk g) =
      ⨆ t : unitInterval, edist x (g.path t) := by
  rw [edist_mk]
  apply le_antisymm
  · refine (iInf_le _ (OrderIso.refl unitInterval)).trans ?_
    refine iSup_le fun t => ?_
    exact le_iSup (fun s : unitInterval => edist x (g.path s)) t
  · refine le_iInf fun e => iSup_le fun t => ?_
    simpa only [NormalizedCurve.const, ContinuousMap.const_apply, e.apply_symm_apply] using
      (le_iSup (fun s : unitInterval =>
        edist ((NormalizedCurve.const x).path s) (g.path (e s))) (e.symm t))

/-- The same formula with the constant curve in the second argument. -/
theorem edist_mk_const {d : ℕ} (f : NormalizedCurve d)
    (x : EuclideanSpace ℝ (Fin d)) :
    edist (mk f) (mk (NormalizedCurve.const x)) =
      ⨆ t : unitInterval, edist (f.path t) x := by
  rw [edist_comm, edist_const_mk]
  simp only [edist_comm]

end LatticeProb.CurveSpace
