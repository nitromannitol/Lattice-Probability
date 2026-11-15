/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ApproximationGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.Approximation
import LatticeProb.Bonanno.BouRabeeGwynne.LocalGeometry

open scoped ENNReal Topology

namespace BouRabeeGwynne.NearestVertexData

variable {d : ℕ} {G : TilingSequence d} (N : NearestVertexData G)

/-- Condition (1.3) eventually supplies a finite mesh below every fixed positive scale. -/
lemma eventually_mesh_finite_le (h : N.ApproximationCondition) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, (G.tiling n).mesh ≠ ∞ ∧ (G.tiling n).mesh.toReal ≤ δ := by
  have hsmall := (N.mesh_tendsto_zero h).eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [hsmall] with n hn
  refine ⟨(lt_trans hn ENNReal.ofReal_lt_top).ne, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn.le
  simpa only [ENNReal.toReal_ofReal hδ.le] using hr

/-- The nearest-vertex error tends uniformly to zero on the actual covered set D. -/
lemma eventually_vertex_dist_le (h : N.ApproximationCondition) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, ∀ z ∈ G.domain,
      dist ((G.tiling n).pos (N.vertex n z)) z ≤ δ := by
  have hsmall := (N.uniformError_tendsto_zero h).eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [hsmall] with n hn z hz
  have hb := (N.errorAt_le_uniformError n hz).trans hn.le
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [N.errorAt_eq_dist, ENNReal.toReal_ofReal hδ.le] using hr

/-- Cells marked in U eventually lie in the interior of D. This is derived from
the approved collar and approximation condition, not added to the tiling definition. -/
lemma eventually_interior_cells_subset_domain (h : N.ApproximationCondition)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ∀ v : (G.tiling n).V, (G.tiling n).pos v ∈ U →
      ((G.tiling n).cell v).carrier ⊆ interior G.domain := by
  obtain ⟨δ, hδ, hδD⟩ :=
    hU.isCompact_closure.exists_cthickening_subset_open isOpen_interior hUD
  filter_upwards [N.eventually_mesh_finite_le h hδ] with n hn v hv
  exact ((G.tiling n).toTilingData.cell_subset_cthickening hv hn.1 hn.2).trans hδD

end BouRabeeGwynne.NearestVertexData
