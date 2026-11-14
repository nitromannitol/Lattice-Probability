/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LipschitzExteriorBalls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LipschitzExteriorGeometry
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Balls below a Lipschitz graph give the exterior balls used for boundary
escape. The graph is the one in the approved geometric domain definition. -/

open Set
open scoped NNReal

namespace BouRabeeGwynne

/-- A downward displacement of at least `(K + 1) * ρ` puts an entire ball
below a `K`-Lipschitz graph. -/
theorem closedBall_below_lipschitz_graph {d : ℕ} {φ : Euc (d - 1) → ℝ}
    {K : ℝ≥0} (hφ : LipschitzWith K φ) (q : Euc (d - 1)) (t a ρ : ℝ)
    (hbelow : t ≤ φ q) (hsep : ((K : ℝ) + 1) * ρ ≤ a) :
    ∀ y ∈ Metric.closedBall (cylinderCoordinates (d := d) q (t - a)) ρ,
      y none ≤ φ (cylinderHorizontal (d := d) y) := by
  intro y hy
  have hd : dist y (cylinderCoordinates (d := d) q (t - a)) ≤ ρ := hy
  have hhorizontal : dist (cylinderHorizontal (d := d) y) q ≤ ρ := by
    simpa only [cylinderHorizontal_cylinderCoordinates] using
      (cylinderHorizontal_dist_le (d := d) y
        (cylinderCoordinates (d := d) q (t - a))).trans hd
  have hvertical : |y none - (t - a)| ≤ ρ := by
    have hn : ‖y - cylinderCoordinates (d := d) q (t - a)‖ ≤ ρ := by
      simpa only [dist_eq_norm] using hd
    simpa [cylinderCoordinates, PiLp.sub_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (y - cylinderCoordinates (d := d) q (t - a)) none).trans hn
  have hφlower : φ q ≤ φ (cylinderHorizontal (d := d) y) + (K : ℝ) * ρ := by
    apply (hφ.le_add_mul q (cylinderHorizontal (d := d) y)).trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    simpa only [dist_comm] using hhorizontal
  have hupper := (le_abs_self (y none - (t - a))).trans hvertical
  nlinarith

end BouRabeeGwynne
