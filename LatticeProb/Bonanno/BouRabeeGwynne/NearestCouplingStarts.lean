/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.NearestCouplingStarts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FixedBallCover
import LatticeProb.Bonanno.BouRabeeGwynne.ApproximationGeometry
import LatticeProb.Bonanno.BouRabeeGwynne.LocalRegion

/-! The approximation condition places every actual nearest starting vertex
in the same fixed inner ball as its continuum start, uniformly in that start. -/

open Set Metric Filter
open scoped Topology

namespace BouRabeeGwynne.NearestVertexData

theorem eventually_nearest_coupling_starts {d : ℕ} {G : TilingSequence d}
    (N : NearestVertexData G) (happrox : N.ApproximationCondition)
    {U W : Set (Euc d)} (hUD : HasAmbientCollar U G.domain)
    (centers : Finset (Euc d)) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hcover : ∀ z ∈ U, ∃ c ∈ centers, z ∈ ball c (r / 4))
    (hballs : ∀ c ∈ centers, closedBall c r ⊆ W) :
    ∀ᶠ n in atTop, ∀ z ∈ U, ∃ (j : centers) (v : (G.tiling n).closedVertices W),
      v.val = N.vertex n z ∧
      (G.tiling n).pos v ∈ closedBall j.val (r / 2) ∧
      z ∈ closedBall j.val (r / 2) ∧
      dist ((G.tiling n).pos v) z ≤ δ := by
  filter_upwards [N.eventually_vertex_dist_le happrox
    (lt_min hδ (by positivity : 0 < r / 4))] with n hn
  intro z hz
  have hzD : z ∈ G.domain := interior_subset (hUD (subset_closure hz))
  have hnear := hn z hzD
  obtain ⟨c, hc, hzc⟩ := hcover z hz
  have hx : (G.tiling n).pos (N.vertex n z) ∈ ball c (r / 2) :=
    near_cover_point_mem_inner_ball hzc (hnear.trans (min_le_right _ _))
  have hxW : (G.tiling n).pos (N.vertex n z) ∈ W :=
    hballs c hc (closedBall_subset_closedBall (half_le_self hr.le) (ball_subset_closedBall hx))
  let v : (G.tiling n).closedVertices W := ⟨N.vertex n z, Or.inl hxW⟩
  refine ⟨⟨c, hc⟩, v, rfl, ball_subset_closedBall hx, ?_,
    hnear.trans (min_le_left _ _)⟩
  exact ball_subset_closedBall (ball_subset_ball (by linarith : r / 4 ≤ r / 2) hzc)

end BouRabeeGwynne.NearestVertexData
