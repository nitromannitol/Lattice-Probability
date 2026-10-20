/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/LengthLimit.lean.
-/
import LatticeProb.Topology.Length.LengthSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Metrics given as functions, and length metrics

Metrics are given as functions `d : X × X → ℝ`, so that a family of metrics on one set can be
compared by uniform convergence of the functions.

* `IsMetricFun d`: `d` is a metric on `X`.
* `MetricFunSpace d hd`: the type `X` carrying the metric `d`, as a type synonym with the
  `MetricSpace` instance `dist x y = d (x, y)`.
* `IsLengthMetricFun d hd`: `(X, d)` is a length space.
* `compactSpace_metricFunSpace`: if `X` is a compact topological space and `D` is a continuous
  metric on `X`, then `(X, D)` is a compact metric space.
-/

open Set Filter Topology

namespace LatticeProb.MetricGeometry

/-- `d : X × X → ℝ` is a metric on `X`: it vanishes on the diagonal, vanishes only on the diagonal,
is symmetric, and satisfies the triangle inequality. Non-negativity is not a field: it follows from
the other three. -/
structure IsMetricFun {X : Type*} (d : X × X → ℝ) : Prop where
  self_eq_zero : ∀ x, d (x, x) = 0
  eq_of_eq_zero : ∀ x y, d (x, y) = 0 → x = y
  symm : ∀ x y, d (x, y) = d (y, x)
  triangle : ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)

/-- `X` carrying the metric `d` (a type synonym). Its `MetricSpace` instance has
`dist x y = d (x, y)`. -/
@[nolint unusedArguments]
def MetricFunSpace {X : Type*} (d : X × X → ℝ) (_hd : IsMetricFun d) : Type _ := X

/-- The metric space structure of `MetricFunSpace d hd`, with `dist x y = d (x, y)`. -/
instance {X : Type*} (d : X × X → ℝ) (hd : IsMetricFun d) : MetricSpace (MetricFunSpace d hd) where
  dist x y := d (x, y)
  dist_self := hd.self_eq_zero
  dist_comm := hd.symm
  dist_triangle := hd.triangle
  eq_of_dist_eq_zero {x y} h := hd.eq_of_eq_zero x y h

/-- The identity `X → MetricFunSpace d hd`. -/
def MetricFunSpace.pt {X : Type*} (d : X × X → ℝ) (hd : IsMetricFun d) : X → MetricFunSpace d hd :=
  id

/-- The distance in `MetricFunSpace d hd` between the points `x` and `y` is `d (x, y)`. -/
theorem MetricFunSpace.dist_pt {X : Type*} (d : X × X → ℝ) (hd : IsMetricFun d) (x y : X) :
    dist (MetricFunSpace.pt d hd x) (MetricFunSpace.pt d hd y) = d (x, y) :=
  rfl

/-- `d` is a length metric on `X`: `(X, d)` is a length space (`IsLengthSpace`). -/
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

/-!
### Nonvacuity example
-/

namespace MetricFunSpaceExample

/-- The discrete metric on `Bool`: distinct points are at distance `1`. -/
def discreteBool : Bool × Bool → ℝ := fun p => if p.1 = p.2 then 0 else 1

/-- The discrete metric is a metric on `Bool`. -/
theorem isMetricFun_discreteBool : IsMetricFun discreteBool where
  self_eq_zero x := by simp [discreteBool]
  eq_of_eq_zero x y h := by
    by_contra hxy
    simp [discreteBool, hxy] at h
  symm x y := by
    by_cases h : x = y <;> simp [discreteBool, h, eq_comm]
  triangle x y z := by
    simp only [discreteBool]
    split_ifs <;> simp_all

/-- `(Bool, discreteBool)` is a compact metric space: this instantiates both hypotheses of
`compactSpace_metricFunSpace`. -/
example : CompactSpace (MetricFunSpace discreteBool isMetricFun_discreteBool) :=
  compactSpace_metricFunSpace isMetricFun_discreteBool continuous_of_discreteTopology

end MetricFunSpaceExample

end LatticeProb.MetricGeometry
