/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LocalGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects

open scoped ENNReal

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- A finite mesh bounds the distance between any two points of one cell. -/
lemma dist_le_mesh {v : T.V} {x y : Euc d}
    (hx : x ∈ (T.cell v).carrier) (hy : y ∈ (T.cell v).carrier)
    (hmesh : T.mesh ≠ ∞) : dist x y ≤ T.mesh.toReal := by
  have hdiam : (T.cell v).diamENN ≤ T.mesh :=
    le_iSup (fun w : T.V => (T.cell w).diamENN) v
  have hreal := ENNReal.toReal_mono hmesh hdiam
  rw [ConvexPolytope.diamENN, ENNReal.toReal_ofReal Metric.diam_nonneg] at hreal
  exact (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded hx hy).trans hreal

/-- The marked point is within one mesh of every point in its cell. -/
lemma dist_pos_le_mesh {v : T.V} {x : Euc d}
    (hx : x ∈ (T.cell v).carrier) (hmesh : T.mesh ≠ ∞) :
    dist x (T.pos v) ≤ T.mesh.toReal :=
  T.dist_le_mesh hx (interior_subset (T.pos_mem_interior v)) hmesh

/-- Adjacent marked points are at most two meshes apart, including exterior neighbors. -/
lemma edge_dist_le_two_mesh {v w : T.V} (hvw : T.adj v w)
    (hmesh : T.mesh ≠ ∞) : dist (T.pos v) (T.pos w) ≤ 2 * T.mesh.toReal := by
  obtain ⟨x, hxv, hxw⟩ := hvw.2.1
  calc
    dist (T.pos v) (T.pos w) ≤ dist (T.pos v) x + dist x (T.pos w) := dist_triangle _ _ _
    _ ≤ T.mesh.toReal + T.mesh.toReal :=
      add_le_add (by simpa only [dist_comm] using T.dist_pos_le_mesh hxv hmesh)
        (T.dist_pos_le_mesh hxw hmesh)
    _ = 2 * T.mesh.toReal := (two_mul _).symm

/-- A cell marked in U lies inside the uniform thickening of its closure. -/
lemma cell_subset_cthickening {U : Set (Euc d)} {v : T.V}
    (hv : T.pos v ∈ U) (hmesh : T.mesh ≠ ∞) {δ : ℝ}
    (hδ : T.mesh.toReal ≤ δ) :
    (T.cell v).carrier ⊆ Metric.cthickening δ (closure U) := by
  intro x hx
  exact Metric.mem_cthickening_of_dist_le x (T.pos v) δ (closure U)
    (subset_closure hv) ((T.dist_pos_le_mesh hx hmesh).trans hδ)

/-- The collar supplies cell containment only where the local argument needs it. -/
lemma cell_subset_domain_of_collar {U : Set (Euc d)} {v : T.V} {δ : ℝ}
    (hcollar : Metric.cthickening δ (closure U) ⊆ T.domain)
    (hv : T.pos v ∈ U) (hmesh : T.mesh ≠ ∞) (hδ : T.mesh.toReal ≤ δ) :
    (T.cell v).carrier ⊆ T.domain :=
  (T.cell_subset_cthickening hv hmesh hδ).trans hcollar

end BouRabeeGwynne.TilingData
