import LatticeProb.Bonanno.BouRabeeGwynne.LocalGeometry
import Mathlib.Data.Set.Finite.Lemmas

/-! Nearest vertices in locally finite tilings.



Adapted from Leonardo Bonanno’s lean-formalizations

(https://github.com/leobon12/lean-formalizations),

BouRabeeGwynne.NearestVertexExistence at commit fdb5cad; only local import paths change.

-/

open scoped ENNReal

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- Marked points in a compact subset of D form a finite set of vertices. -/
lemma vertices_in_compact_finite {K : Set (Euc d)} (hK : IsCompact K)
    (hKD : K ⊆ T.domain) : {v : T.V | T.pos v ∈ K}.Finite := by
  apply (T.locallyFinite K hK hKD).subset
  intro v hv
  exact ⟨T.pos v, interior_subset (T.pos_mem_interior v), hv⟩

/-- A covered point with a mesh-sized neighborhood in D has an actual nearest
vertex. Distant vertices cannot improve on the candidate supplied by its cell. -/
theorem exists_nearest_vertex {z : Euc d} {r : ℝ} (hr : 0 < r)
    (hrD : Metric.closedBall z r ⊆ T.domain) (hmesh : T.mesh ≠ ∞)
    (hsmall : T.mesh.toReal ≤ r) :
    ∃ v : T.V, ∀ w : T.V, dist z (T.pos v) ≤ dist z (T.pos w) := by
  have hzD : z ∈ T.domain := hrD (Metric.mem_closedBall_self hr.le)
  obtain ⟨v₀, hv₀⟩ := T.exists_mem_cell hzD
  have hd₀ : dist z (T.pos v₀) ≤ r := (T.dist_pos_le_mesh hv₀ hmesh).trans hsmall
  let S : Set T.V := {v | T.pos v ∈ Metric.closedBall z r}
  have hS : S.Finite := T.vertices_in_compact_finite (isCompact_closedBall z r) hrD
  have hv₀S : v₀ ∈ S := by
    exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hd₀)
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S (fun w => dist z (T.pos w)) hS ⟨v₀, hv₀S⟩
  refine ⟨v, fun w => ?_⟩
  by_cases hw : w ∈ S
  · exact hmin w hw
  · have hrw : r < dist z (T.pos w) := by
      apply lt_of_not_ge
      intro hle
      exact hw (Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hle))
    exact ((hmin v₀ hv₀S).trans hd₀).trans hrw.le

end BouRabeeGwynne.TilingData
