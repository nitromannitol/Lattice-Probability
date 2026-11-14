import LatticeProb.Topology.CurveSpace

/-! # Comparing curves along continuous monotone clocks -/

set_option autoImplicit false
open scoped ENNReal unitInterval

namespace LatticeProb

/-- The Fréchet distance is bounded by the uniform cost along any pair of continuous
nondecreasing clocks that traverse the entire unit interval. -/
theorem curveSpace_edist_le_iSup_of_monotone_clocks {d : ℕ}
    (f g : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (φ ψ : C(unitInterval, unitInterval))
    (hφ : Monotone φ) (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1)
    (hψ : Monotone ψ) (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 1) :
    edist (CurveSpace.project f) (CurveSpace.project g) ≤
      ⨆ t : unitInterval, edist (f (φ t)) (g (ψ t)) := by
  rw [← curveSpace_project_comp_monotone f φ hφ hφ0 hφ1,
    ← curveSpace_project_comp_monotone g ψ hψ hψ0 hψ1]
  calc
    edist (CurveSpace.project (f.comp φ)) (CurveSpace.project (g.comp ψ)) ≤
        edist (f.comp φ) (g.comp ψ) := by
      simpa only [ENNReal.coe_one, one_mul] using (CurveSpace.project_lipschitz (d := d) (f.comp φ) (g.comp ψ))
    _ = ⨆ t : unitInterval, edist (f (φ t)) (g (ψ t)) := by
      rw [ContinuousMap.edist_eq_iSup]
      rfl

end LatticeProb
