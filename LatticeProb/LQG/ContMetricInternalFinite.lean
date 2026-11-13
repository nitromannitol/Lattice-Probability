import LatticeProb.LQG.ContMetricLSCInternal
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# Finite internal distances for continuous length metrics

For a continuous metric `D` on `ℂ` (inducing the Euclidean topology) such that `(ℂ, D)` is a length
space, and an open set `U`, the internal metric `D(·, ·; U)` (the infimum of the `D`-lengths of paths
contained in `U`) is finite between any two points of a preconnected subset of `U`; in particular
between any two points of a connected open set `U`.

The proof is the usual chaining argument: `D(·, ·; U)` is continuous on `U × U` and vanishes on the
diagonal, so it is finite near the diagonal, and finiteness propagates along a preconnected set by
the triangle inequality.

We also record the same statement for the associated lower semicontinuous metric
`contToLSCMetric D`, in the form used by the finiteness axiom for internal set distances of strong
LQG metrics (Ding-Gwynne).
-/

open Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

open LQGMetric.MetricGeometry

/-- **Finite internal distances on a preconnected set.** For a continuous length metric `D`, an open
set `U` and a preconnected set `K ⊆ U`, the internal metric `D(z, w; U)` is finite for `z, w ∈ K`. -/
theorem internal_lt_top_of_isPreconnected (D : LQGMetric.ContMetric) (hD : D.IsLength)
    {K U : Set ℂ} (hK : IsPreconnected K) (hU : IsOpen U) (hKU : K ⊆ U) {z w : ℂ} (hz : z ∈ K)
    (hw : w ∈ K) : D.internal U z w < ⊤ := by
  refine hK.induction₂ (fun x y => D.internal U x y < ⊤) (fun x hx => ?_)
    (fun x y v _ _ _ hxy hyv => ?_) (fun x y _ _ hxy => ?_) hz hw
  · have hc : ContinuousAt (fun p : ℂ × ℂ => D.internal U p.1 p.2) (x, x) :=
      (LQGMetric.ContMetric.continuousOn_internal D hD hU).continuousAt
        ((hU.prod hU).mem_nhds (mk_mem_prod (hKU hx) (hKU hx)))
    have h0 : D.internal U x x < ⊤ := by
      have : D.internal U x x = 0 := internalEDist_self (mem_image_of_mem D.pt (hKU hx))
      rw [this]
      exact ENNReal.zero_lt_top
    have h2 : Tendsto (fun y : ℂ => (x, y)) (𝓝 x) (𝓝 (x, x)) :=
      (continuous_const.prodMk continuous_id).tendsto x
    exact nhdsWithin_le_nhds (h2.eventually (hc.eventually (eventually_lt_nhds h0)))
  · exact lt_of_le_of_lt (internalEDist_triangle (D.pt '' U) (D.pt x) (D.pt y) (D.pt v))
      (ENNReal.add_lt_top.2 ⟨hxy, hyv⟩)
  · exact (internalEDist_comm (D.pt '' U) (D.pt y) (D.pt x)).trans_lt hxy

/-- **Finite internal distances on a connected open set.** For a continuous length metric `D` and a
connected open set `U`, the internal metric `D(z, w; U)` is finite for all `z, w ∈ U`. -/
theorem internal_lt_top_of_isLength (D : LQGMetric.ContMetric) (hD : D.IsLength) {U : Set ℂ}
    (hU : IsOpen U) (hc : IsConnected U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    D.internal U z w < ⊤ :=
  internal_lt_top_of_isPreconnected D hD hc.isPreconnected hU subset_rfl hz hw

/-- The internal distance `(contToLSCMetric D)(z, w; U)` of the associated lower semicontinuous
metric is finite for any two points `z, w` of a connected open set `U`. -/
theorem internal_contToLSCMetric_lt_top (D : LQGMetric.ContMetric) (hD : D.IsLength) {U : Set ℂ}
    (hU : IsOpen U) (hc : IsConnected U) (p : U × U) : (contToLSCMetric D).internal U p < ⊤ := by
  rw [internal_contToLSCMetric]
  exact internal_lt_top_of_isLength D hD hU hc p.1.2 p.2.2

/-- **Finite internal set distances.** For a continuous length metric `D`, a connected open set `U`
and nonempty sets `K₁, K₂ ⊆ U`, the infimum of `(contToLSCMetric D)(x, y; U)` over `x ∈ K₁`, `y ∈ K₂`
is finite. -/
theorem iInf_internal_contToLSCMetric_lt_top (D : LQGMetric.ContMetric) (hD : D.IsLength)
    {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {K₁ K₂ : Set U} (h₁ : K₁.Nonempty)
    (h₂ : K₂.Nonempty) : ⨅ (x ∈ K₁) (y ∈ K₂), (contToLSCMetric D).internal U (x, y) < ⊤ := by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  exact lt_of_le_of_lt (iInf₂_le_of_le x hx (iInf₂_le_of_le y hy le_rfl))
    (internal_contToLSCMetric_lt_top D hD hU hc (x, y))

end LatticeProb.LQG
