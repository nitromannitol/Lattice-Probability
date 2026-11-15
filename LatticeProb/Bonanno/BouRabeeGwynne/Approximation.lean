/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Approximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects

open scoped ENNReal Topology

namespace BouRabeeGwynne

/--
The nearest vertices `z^n` used in (1.3).  The paper uses lexicographic order
only to choose among minimizers. We retain a total vertex map for convenience,
but require minimization only for points in the covered set `D`. Values outside
`D` impose no extra nearest-vertex existence requirement.
-/
structure NearestVertexData {d : ℕ} (G : TilingSequence d) : Type 1 where
  vertex : (n : ℕ) → Euc d → (G.tiling n).V
  isNearest : ∀ n z, z ∈ G.domain → ∀ v,
    dist z ((G.tiling n).pos (vertex n z)) ≤
      dist z ((G.tiling n).pos v)

namespace NearestVertexData

variable {d : ℕ} {G : TilingSequence d} (N : NearestVertexData G)

/-- Pointwise nearest-vertex error. -/
noncomputable def errorAt (n : ℕ) (z : Euc d) : ℝ≥0∞ :=
  ENNReal.ofReal (dist ((G.tiling n).pos (N.vertex n z)) z)

/-- The supremum in (1.3), restricted to `z ∈ D`. -/
noncomputable def uniformError (n : ℕ) : ℝ≥0∞ :=
  ⨆ z : G.domain, N.errorAt n z.1

lemma errorAt_eq_dist (n : ℕ) (z : Euc d) :
    (N.errorAt n z).toReal = dist ((G.tiling n).pos (N.vertex n z)) z := by
  rw [errorAt, ENNReal.toReal_ofReal]
  exact dist_nonneg

/-- Condition (1.3) exactly, in extended nonnegative reals. -/
def ApproximationCondition : Prop :=
  Filter.Tendsto
    (fun n => (G.tiling n).mesh + N.uniformError n)
    Filter.atTop (𝓝 0)

lemma mesh_tendsto_zero (h : N.ApproximationCondition) :
    Filter.Tendsto (fun n => (G.tiling n).mesh) Filter.atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h (fun _ => zero_le)
    (fun _ => le_self_add)

lemma uniformError_tendsto_zero (h : N.ApproximationCondition) :
    Filter.Tendsto N.uniformError Filter.atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h (fun _ => zero_le)
    (fun _ => le_add_self)

lemma errorAt_le_uniformError (n : ℕ) {z : Euc d} (hz : z ∈ G.domain) :
    N.errorAt n z ≤ N.uniformError n := by
  exact le_iSup (fun q : G.domain => N.errorAt n q.1) ⟨z, hz⟩

end NearestVertexData

end BouRabeeGwynne
