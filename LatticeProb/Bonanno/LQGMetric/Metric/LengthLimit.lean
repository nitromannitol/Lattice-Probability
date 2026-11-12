/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.LengthLimit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Metric.Midpoint
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Uniform limits of length metrics are length metrics (DFGPS Lemma 2.7, BBI Exercise 2.4.19)

Metrics are given as functions `d : X × X → ℝ` (DFGPS l. 860–866: "a sequence of length metrics
on `X` which converge uniformly to a metric `D` on `X`"; BBI Ex. 2.4.19: "recall that metrics are
functions on `X × X`, so the notion of uniform convergence applies here").

* `IsMetricFun d`: `d` is a metric on `X`; `MetricFunSpace d hd` is `X` with the metric `d`
  (a type synonym, as `ContMetric.Space` in FOUNDATIONS §5); `IsLengthMetricFun d hd` says that
  `(X, d)` is a length space (paths continuous for `d`, lengths measured with `d`).
* `isLengthSpace_of_tendstoUniformly`: in a complete metric space `(X, D)`, if length metrics
  `dᵢ` converge uniformly to `D`, then `(X, D)` is a length space.
* `isLengthMetricFun_of_tendstoUniformly` (**DFGPS Lemma 2.7**, `lem-bbi`): `X` a compact
  topological space, `dⁿ` length metrics on `X` converging uniformly to a continuous metric `D`
  (a metric on the topological space `X`; continuity is all that is used of "metric on `X`") ⇒
  `D` is a length metric. `isLengthMetricFun_of_tendstoUniformly_of_continuous`: the same with
  the `dⁿ` continuous instead of `D` (then `D` is continuous as a uniform limit).
* `isLengthMetricFun_of_tendstoUniformly_compact_complex`: the form used for compact `K ⊂ ℂ`
  (DFGPS L2.8, L2.9 with `K = S, W̄`; DDDF Thm 1 / §1 item on `𝒟̄`, `tightness.tex` l. 174).

Proof (BBI: "an easy consequence of Corollary 2.4.17", DFGPS l. 865): `dᵢ` has `ε/4`-midpoints
(BBI Lemma 2.4.10, `hasApproxMidpoints_of_isLengthSpace`); for `i` with `|dᵢ − D| < ε/4` these
are `ε`-midpoints for `D`; conclude by Menger's lemma (BBI Thm 2.4.16(2),
`isLengthSpace_of_hasApproxMidpoints`). `(X, D)` is compact (the identity `X → (X, D)` is
continuous), hence complete.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace LQGMetric.MetricGeometry

/-- `d : X × X → ℝ` is a metric on `X`. -/
structure IsMetricFun {X : Type*} (d : X × X → ℝ) : Prop where
  self_eq_zero : ∀ x, d (x, x) = 0
  eq_of_eq_zero : ∀ x y, d (x, y) = 0 → x = y
  symm : ∀ x y, d (x, y) = d (y, x)
  triangle : ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)

/-- `X` carrying the metric `d` (type synonym). -/
@[nolint unusedArguments]
def MetricFunSpace {X : Type*} (d : X × X → ℝ) (_hd : IsMetricFun d) : Type _ := X

instance {X : Type*} (d : X × X → ℝ) (hd : IsMetricFun d) : MetricSpace (MetricFunSpace d hd) where
  dist x y := d (x, y)
  dist_self := hd.self_eq_zero
  dist_comm := hd.symm
  dist_triangle := hd.triangle
  eq_of_dist_eq_zero {x y} h := hd.eq_of_eq_zero x y h

/-- The identity `X → MetricFunSpace d hd`. -/
def MetricFunSpace.pt {X : Type*} (d : X × X → ℝ) (hd : IsMetricFun d) : X → MetricFunSpace d hd :=
  id

/-- `d` is a length metric on `X`: `(X, d)` is a length space (GM §1.2, BBI Def. 2.1.6). -/
def IsLengthMetricFun {X : Type*} (d : X × X → ℝ) (hd : IsMetricFun d) : Prop :=
  IsLengthSpace (MetricFunSpace d hd)

/-- For a continuous metric `D` on a compact space `X`, `(X, D)` is compact. -/
theorem compactSpace_metricFunSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {D : X × X → ℝ} (hD : IsMetricFun D) (hDc : Continuous D) :
    CompactSpace (MetricFunSpace D hD) := by
  have hcont : Continuous (MetricFunSpace.pt D hD) := by
    rw [Metric.continuous_iff']
    intro a ε hε
    have ht : Tendsto (fun x => D (x, a)) (𝓝 a) (𝓝 (D (a, a))) :=
      (hDc.comp (continuous_id.prodMk continuous_const)).tendsto a
    rw [hD.self_eq_zero] at ht
    exact ht.eventually (gt_mem_nhds hε)
  have hrange : Set.range (MetricFunSpace.pt D hD) = univ :=
    Set.range_eq_univ.2 fun y => ⟨y, rfl⟩
  exact ⟨by simpa [← hrange] using isCompact_range hcont⟩

end LQGMetric.MetricGeometry
