/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LipschitzChartExteriorBalls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LipschitzExteriorBalls

/-! An exterior ball in an actual rigid Lipschitz chart. The explicit cylinder
margins ensure every point of the ball is covered by the chart equivalence. -/

open Set
open scoped NNReal

namespace BouRabeeGwynne

theorem closedBall_compl_of_lipschitz_chart {d : ℕ}
    (U : Set (Euc d)) (p : Euc d)
    (R : Euc d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin (d - 1))))
    {φ : Euc (d - 1) → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (r h : ℝ)
    (hchart : ∀ q : Euc (d - 1), ∀ t : ℝ, ‖q‖ < r → |t| < h →
      (p + R.symm (cylinderCoordinates (d := d) q t) ∈ U ↔ φ q < t))
    (q : Euc (d - 1)) (t a ρ : ℝ)
    (hbelow : t ≤ φ q) (hsep : ((K : ℝ) + 1) * ρ ≤ a)
    (hmarginq : ‖q‖ + ρ < r) (hmargint : |t - a| + ρ < h) :
    Metric.closedBall (p + R.symm (cylinderCoordinates (d := d) q (t - a))) ρ ⊆ Uᶜ := by
  intro y hy hyU
  let v : EuclideanSpace ℝ (Option (Fin (d - 1))) := R (y - p)
  have hyrepr : p + R.symm v = y := by
    dsimp only [v]
    rw [R.symm_apply_apply, add_comm p (y - p), sub_add_cancel]
  have hvball : v ∈ Metric.closedBall (cylinderCoordinates (d := d) q (t - a)) ρ := by
    have hd : dist (p + R.symm v)
        (p + R.symm (cylinderCoordinates (d := d) q (t - a))) ≤ ρ := by
      simpa only [Metric.mem_closedBall, hyrepr] using hy
    simpa only [Metric.mem_closedBall, dist_add_left, R.symm.dist_map] using hd
  have hqdist : dist (cylinderHorizontal (d := d) v) q ≤ ρ := by
    simpa only [cylinderHorizontal_cylinderCoordinates] using
      (cylinderHorizontal_dist_le (d := d) v
        (cylinderCoordinates (d := d) q (t - a))).trans hvball
  have hqinside : ‖cylinderHorizontal (d := d) v‖ < r := by
    have hn : ‖cylinderHorizontal (d := d) v‖ - ‖q‖ ≤ ρ :=
      (norm_sub_norm_le _ _).trans (by simpa only [dist_eq_norm] using hqdist)
    linarith
  have htdiff : |v none - (t - a)| ≤ ρ := by
    have hn : ‖v - cylinderCoordinates (d := d) q (t - a)‖ ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hvball
    simpa [cylinderCoordinates, PiLp.sub_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (v - cylinderCoordinates (d := d) q (t - a)) none).trans hn
  have htinside : |v none| < h := by
    have hn : |v none| - |t - a| ≤ |v none - (t - a)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_norm_le (v none) (t - a)
    linarith
  have hcoordU : p + R.symm (cylinderCoordinates (d := d)
      (cylinderHorizontal (d := d) v) (v none)) ∈ U := by
    simpa only [cylinderCoordinates_reconstruct, hyrepr] using hyU
  have hgraph := closedBall_below_lipschitz_graph (d := d) hφ q t a ρ hbelow hsep v hvball
  exact (not_lt_of_ge hgraph) ((hchart _ _ hqinside htinside).mp hcoordU)

end BouRabeeGwynne
