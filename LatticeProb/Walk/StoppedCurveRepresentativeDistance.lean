import LatticeProb.Bonanno.BouRabeeGwynne.WalkExcursionKernel

/-! # Stability of stopped polygonal curves under changes of representative -/

set_option autoImplicit false
noncomputable section

open BouRabeeGwynne Set
open scoped unitInterval ENNReal

namespace LatticeProb

/-- Polygonal interpolations through uniformly close vertices remain uniformly close. -/
theorem dist_polygonalCurve_le_of_dist_le {d : ℕ} {V : Type*} [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (ω : ℕ → V) (m : ℕ) {r : ℝ}
    (h : ∀ v, dist (p v) (q v) ≤ r) (t : unitInterval) :
    dist (polygonalCurve p ω m t) (polygonalCurve q ω m t) ≤ r := by
  have hd : polygonalCurve (fun v => p v - q v) ω m t =
      polygonalCurve p ω m t - polygonalCurve q ω m t := by
    simp only [polygonalCurve, ContinuousMap.coe_mk, sub_sub_sub_comm, smul_sub,
      Finset.sum_sub_distrib]
    abel
  have hm := polygonalCurve_mem_of_convex (fun v => p v - q v) ω
    (convex_closedBall (0 : Euc d) r) (fun v => by
      simpa only [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] using h v) m t
  rw [hd, Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at hm
  exact hm

/-- The same estimate holds after stopping at a shared active set and
projecting to curves modulo increasing reparametrization. -/
theorem edist_stoppedPolygonalCurve_le_of_dist_le {d : ℕ} {V : Type*} [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (A : Set V) (ω : ℕ → V) {r : ℝ}
    (h : ∀ v, dist (p v) (q v) ≤ r) :
    edist (stoppedPolygonalCurve p A ω) (stoppedPolygonalCurve q A ω) ≤ ENNReal.ofReal r := by
  apply (CurveSpace.project_lipschitz.edist_le_mul _ _).trans
  rw [ContinuousMap.edist_eq_iSup]
  simp only [ENNReal.coe_one, one_mul]
  apply iSup_le
  intro t
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_polygonalCurve_le_of_dist_le p q ω _ h t)

end LatticeProb
end
