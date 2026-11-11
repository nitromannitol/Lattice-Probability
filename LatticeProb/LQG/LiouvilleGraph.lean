import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure

/-! # Liouville graph distance and the whole-plane LQG dimension: general definitions

General copies of the Liouville graph-distance objects of Ding and Gwynne, arXiv:1807.01072v3, Definition 1.3, and of the
whole-plane LQG dimension characterization of their Theorem 1.4, at the generality of their source. They are stated over
the whole-plane field layer of `LatticeProb/Gauss/GFF.lean` (namespace `LatticeProb.Gauss`) and the γ-LQG measure of
`LatticeProb/LQG/LQGMeasure.lean` (namespace `LatticeProb.LQG`).

* `LatticeProb.LQG.IsLiouvilleGraphCover μ ε z w count`: `count` balls of positive radius and `μ`-mass at most `ε`
  cover a path from `z` to `w`.
* `LatticeProb.LQG.liouvilleGraphDistance μ ε z w : ℕ∞`: the least such `count`, or `⊤` if there is none.
* `LatticeProb.LQG.liouvilleGraphExponent μ z w k = log D(2^{-k}) / (k log 2)`: the dyadic point-to-point exponent.
* `LatticeProb.LQG.IsLiouvilleGraphDimension μ z w d`: `d > 0`, the dyadic distances are eventually finite, and the dyadic
  exponent tends to `1 / d`.
* `LatticeProb.LQG.IsWholePlaneLQGDimension γ d`: `d > 0`, and for every whole-plane GFF realization with its γ-LQG
  measure `μ` (`α₀ = 0`), almost surely `IsLiouvilleGraphDimension (μ ω) 0 1 d`.
* `LatticeProb.LQG.WholePlaneLQGGraphDimension`: the literature input of Ding and Gwynne, Theorem 1.4, equation (1.8),
  stated as a Prop only.

Provenance. Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity,
arXiv:2208.11795]: the definitions `IsLiouvilleGraphCover`, `liouvilleGraphDistance`, `liouvilleGraphExponent`,
`IsLiouvilleGraphDimension` and `IsWholePlaneLQGDimension`, and the input `WholePlaneLQGGraphDimension`. No statement,
hypothesis or conclusion of the source is changed. The terminology is that of the Liouville graph distance (Ding and Gwynne) and
of the LQG dimension (Duplantier and Sheffield, Berestycki and Powell).

Helper theorems inside the source bodies: none (the bodies contain no proof terms), so none is restated here. The sanity
and uniqueness lemmas of the source are theorems, not definitions, and are not included here.
-/

open MeasureTheory Filter Topology

namespace LatticeProb.LQG

/-- `IsLiouvilleGraphCover μ ε z w count`: there are `count` Euclidean balls, each of positive radius and `μ`-mass at
most `ε`, such that every point of some path from `z` to `w` lies in one of the balls. -/
def IsLiouvilleGraphCover (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) (count : ℕ) : Prop :=
  ∃ balls : Fin count → ℂ × ℝ,
    (∀ index, 0 < (balls index).2 ∧
      μ (Metric.ball (balls index).1 (balls index).2) ≤ ENNReal.ofReal ε) ∧
    ∃ path : Path z w, ∀ time : unitInterval,
      ∃ index, path time ∈ Metric.ball (balls index).1 (balls index).2

/-- The Liouville graph distance at mass scale `ε`: the minimum number of balls of `μ`-mass at most `ε` covering a path
from `z` to `w`, or infinity if no such cover exists. -/
noncomputable def liouvilleGraphDistance (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) : ℕ∞ :=
  sInf {number | ∃ count : ℕ, number = count ∧ IsLiouvilleGraphCover μ ε z w count}

/-- The dyadic point-to-point Liouville graph-distance exponent `log D(2^{-k}) / (k log 2)`, where `D` is
`liouvilleGraphDistance` and the infinite value is read as `0`. -/
noncomputable def liouvilleGraphExponent (μ : Measure ℂ) (z w : ℂ) (index : ℕ) : ℝ :=
  Real.log (liouvilleGraphDistance μ (dyadicScale index) z w).toNat /
    ((index : ℝ) * Real.log 2)

/-- `IsLiouvilleGraphDimension μ z w d`: `d` is positive, the dyadic graph distances are eventually finite, and the dyadic
point-to-point exponent tends to `1 / d`. -/
def IsLiouvilleGraphDimension (μ : Measure ℂ) (z w : ℂ) (dimension : ℝ) : Prop :=
  0 < dimension ∧
    (∀ᶠ index : ℕ in atTop, liouvilleGraphDistance μ (dyadicScale index) z w ≠ ⊤) ∧
    Tendsto (liouvilleGraphExponent μ z w) atTop (𝓝 (1 / dimension))

/-- `IsWholePlaneLQGDimension γ d`: `d` is positive, and for every whole-plane GFF realization `(P, hC, hcirc)` with
γ-LQG measure `μ` of the field with `α₀ = 0`, almost surely the Liouville graph-distance dimension between the fixed
points `0` and `1` is `d`. -/
def IsWholePlaneLQGDimension (γ dimension : ℝ) : Prop :=
  0 < dimension ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ᵐ ω ∂P, IsLiouvilleGraphDimension (μ ω) 0 1 dimension

/-- **LQG graph-distance exponent (literature input, stated as a Prop).** Ding and Gwynne, *The fractal dimension of
Liouville quantum gravity: universality, monotonicity, and bounds*, arXiv:1807.01072v3, Theorem 1.4, p. 6, equation
(1.8), together with the positivity of the dimension in Theorem 1.1, p. 4. For every `γ ∈ (0, 2)` some dimension
satisfies `IsWholePlaneLQGDimension γ`. The statement restricts the full limit to dyadic mass scales and fixes the
points `0` and `1`; the same deterministic dimension serves every realization of the normalized field.

This is a literature input, not a theorem: it is an assumption wherever it is used, and not a theorem of this
development. -/
def WholePlaneLQGGraphDimension : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ dimension, IsWholePlaneLQGDimension γ dimension

end LatticeProb.LQG
