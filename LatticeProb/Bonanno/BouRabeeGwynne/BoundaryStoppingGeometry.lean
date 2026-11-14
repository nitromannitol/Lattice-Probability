/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BoundaryStoppingGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BoundaryStoppingComparison
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurvePrefixes
import Mathlib.Topology.MetricSpace.Thickening

/-! Geometric bracketing for the actual discrete vertex exit. Before that
vertex, polygonal edges need only stay in a mesh collar of the domain. -/

open Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

/-- The matched vertex-exit time lies between the Brownian inner and outer
boundary approaches. The assertion also allows the vertex-exit time to be zero. -/
theorem vertexExit_timeChange_mem_boundaryInterval {d : ℕ}
    (f g : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (e : NormalizedCurve.TimeChange) (U : Set (EuclideanSpace ℝ (Fin d)))
    (a l u : unitInterval) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hclose : ∀ t, dist (f t) (g (e t)) ≤ ε)
    (hpre : ∀ t < a, f t ∈ Metric.cthickening δ U) (hout : f a ∉ U)
    (hinner : ∀ t < l, Metric.closedBall (g t) ε ⊆ U)
    (houter : g u ∉ Metric.cthickening (ε + δ) U) :
    e a ∈ Icc l u := by
  constructor
  · by_contra h
    apply hout
    exact hinner (e a) (lt_of_not_ge h) (hclose a)
  · by_contra h
    have ht : e.symm u < a := by
      apply e.lt_iff_lt.mp
      simpa only [e.apply_symm_apply] using (lt_of_not_ge h)
    have hd : dist (g u) (f (e.symm u)) ≤ ε := by
      simpa only [e.apply_symm_apply, dist_comm] using hclose (e.symm u)
    exact houter (Metric.cthickening_cthickening_subset hε hδ U
      (Metric.mem_cthickening_of_dist_le (g u) (f (e.symm u)) ε
        (Metric.cthickening δ U) (hpre _ ht) hd))

/-- Compare the actual normalized stopped prefixes using a discrete vertex exit,
a continuous exit, and the second path's boundary-interval oscillation. -/
theorem curveSpace_edist_prefixes_le_of_vertexExit {d : ℕ}
    (f g : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (e : NormalizedCurve.TimeChange) (U : Set (EuclideanSpace ℝ (Fin d)))
    (a b l u : unitInterval) {ε δ η : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hclose : ∀ t, dist (f t) (g (e t)) ≤ ε)
    (hfpre : ∀ t < a, f t ∈ Metric.cthickening δ U) (hfout : f a ∉ U)
    (hgpre : ∀ t < b, g t ∈ U) (hgout : g b ∉ U)
    (hinner : ∀ t < l, Metric.closedBall (g t) ε ⊆ U)
    (houter : g u ∉ Metric.cthickening (ε + δ) U)
    (hosc : ∀ s ∈ Icc l u, ∀ t ∈ Icc l u, dist (g s) (g t) ≤ η) :
    edist (CurveSpace.project (prefixUnitCurve f a))
      (CurveSpace.project (prefixUnitCurve g b)) ≤ ENNReal.ofReal (ε + η) := by
  have ha := vertexExit_timeChange_mem_boundaryInterval f g e U a l u hε hδ
    hclose hfpre hfout hinner houter
  have hb : b ∈ Icc l u := by
    constructor
    · by_contra h
      apply hgout
      apply hinner b (lt_of_not_ge h)
      simpa only [Metric.mem_closedBall, dist_self] using hε
    · by_contra h
      apply houter
      apply Metric.mem_cthickening_of_dist_le (g u) (g u) (ε + δ) U
        (hgpre u (lt_of_not_ge h))
      simpa only [dist_self] using add_nonneg hε hδ
  rw [← curveSpace_project_stoppedUnitCurve_eq_prefix f a,
    ← curveSpace_project_stoppedUnitCurve_eq_prefix g b]
  exact curveSpace_edist_stoppedUnitCurve_le f g e a b l u hclose ha hb hosc

end BouRabeeGwynne
