import Mathlib

/-!
# Length metrics, Weyl scaling and internal diameters on `ℂ`

General definitions of the metric geometry of the γ-Liouville quantum gravity (LQG) metric that do not involve the
Gaussian free field or the LQG measure: the `D`-length of a curve and of a path, the internal metric `D(z, w; U)` of a set
`U`, the internal diameter `diam^δ_D(A)`, Euclidean length metrics on `ℂ`, length-parametrized curves, the Weyl scaling
`e^{ξ f} · D`, and the Weyl shift `(μ, D) ↦ (e^{γ f} μ, e^{ξ f} · D)` of a measure-metric pair. Only Mathlib is imported.

A metric is a function `D : ℂ → ℂ → ℝ`, as in the source definitions; the length metric axioms are the structure
`IsEuclideanLengthMetric`. The random part (the LQG metric of a field, `IsLQGMetric`, `IsLQGMetricOfField`) is not here.

Provenance (HarmonicBalls repository, branch main): `curveLength`, `pathLength`, `internalMetric`,
`IsEuclideanLengthMetric`, `IsLengthParametrized`, `weylScaling` are copies of `HarmonicBalls/Defs/LQGMetric.lean`;
`internalDiam` is a copy of `HarmonicBalls/Draft/Section11.lean`; `weylShiftPair` is a copy of
`HarmonicBalls/FirstPass/Frozen/S11c.lean`. Each copy has the same body as its source. Bridge theorems relating the two
copies are in `HarmonicBalls/FirstPass/LPBridge/M5a.lean`.

Terminology: the length of a curve is the supremum of inscribed sums, as in the length structures of Burago-Burago-Ivanov;
the internal metric of a set is the infimum of lengths of paths in the set; the Weyl scaling is the one of Gwynne-Miller
(arXiv:1905.00383, (1.7)-(1.8)) and Duplantier-Sheffield-Gwynne-Miller, the weighted infimum over curves parametrized by
`D`-length of `∫ e^{ξ f}`.
-/

namespace LatticeProb.LQG

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The `D`-length of the curve `p : ℝ → ℂ` on the parameter interval `[a, b]`: the supremum over finite monotone
sequences `a ≤ t₀ ≤ t₁ ≤ ... ≤ tₙ ≤ b` of the sums `∑ D(p(tᵢ₊₁), p(tᵢ))`. For `D = dist` this is the variation of `p`
on `[a, b]`. -/
noncomputable def curveLength (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b },
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i)))

/-- The `D`-length `len(P; D)` of a Euclidean-continuous path `P` from `z` to `w`, the length of its extension on `[0, 1]`. -/
noncomputable def pathLength (D : ℂ → ℂ → ℝ) {z w : ℂ} (P : Path z w) : ℝ≥0∞ :=
  curveLength D P.extend 0 1

/-- The internal metric `D(z, w; U)`: the infimum of the `D`-lengths of the paths from `z` to `w` with range in `U`, with
value `∞` when no path in `U` joins `z` to `w`. -/
noncomputable def internalMetric (D : ℂ → ℂ → ℝ) (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (P : Path z w) (_ : ∀ t, P t ∈ U), pathLength D P

/-- The internal diameter `diam^δ_D(A) = sup_{x, y ∈ A} D(x, y; B_δ(A))` of a set `A`, for the internal metric of its
`δ`-neighbourhood. -/
noncomputable def internalDiam (D : ℂ → ℂ → ℝ) (δ : ℝ) (A : Set ℂ) : ℝ≥0∞ :=
  ⨆ x ∈ A, ⨆ y ∈ A, internalMetric D (Metric.thickening δ A) x y

/-- `D` is a Euclidean length metric on `ℂ`: a metric whose open sets are the Euclidean open sets, and whose distance
is the infimum of the `D`-lengths of paths (`D(z, w) = D(z, w; ℂ)`). -/
structure IsEuclideanLengthMetric (D : ℂ → ℂ → ℝ) : Prop where
  /-- `D(z, z) = 0`. -/
  self_eq_zero : ∀ z, D z z = 0
  /-- `D` separates points. -/
  eq_of_eq_zero : ∀ z w, D z w = 0 → z = w
  /-- `D` is symmetric. -/
  symm : ∀ z w, D z w = D w z
  /-- The triangle inequality. -/
  triangle : ∀ x y z, D x z ≤ D x y + D y z
  /-- The `D`-open sets are the Euclidean open sets. -/
  isOpen_iff : ∀ U : Set ℂ, IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w, D z w < ε → w ∈ U
  /-- Length metric: `D(z, w) = D(z, w; ℂ)`. -/
  ofReal_eq_internalMetric : ∀ z w, ENNReal.ofReal (D z w) = internalMetric D univ z w

/-- The curve `p` is parametrized by `D`-length on `[0, T]`: it is Euclidean-continuous on `[0, T]`, and the `D`-length
of `p` restricted to `[s, t]` is `t - s` for `0 ≤ s ≤ t ≤ T`. -/
def IsLengthParametrized (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) (T : ℝ) : Prop :=
  0 ≤ T ∧ ContinuousOn p (Icc 0 T) ∧
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → curveLength D p s t = ENNReal.ofReal (t - s)

/-- The Weyl scaling `e^{ξ f} · D` of the metric `D` by a function `f`, in the form of Gwynne-Miller (arXiv:1905.00383,
(1.8)): `(u, v) ↦ inf_p ∫_0^T e^{ξ f(p(t))} dt`, the infimum over the curves `p : [0, T] → ℂ` parametrized by `D`-length
from `u` to `v`. The integral is a lower Lebesgue integral in `[0, ∞]`, so the definition applies to weights which are not
integrable along the curve. -/
noncomputable def weylScaling (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (p : ℝ → ℂ) (_ : IsLengthParametrized D p T) (_ : p 0 = u) (_ : p T = v),
    ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t)))

/-- The Weyl shift of a pair `(μ, D)` of a measure and a metric on `ℂ` by a function `f`, with parameters `γ` and `ξ`:
the measure acquires the density `e^{γ f}` and the metric is the Weyl scaling `e^{ξ f} · D`, with values in `ℝ` (the
`toReal` of the extended value). The pair is transformed as a generic pair; no field is involved. -/
noncomputable def weylShiftPair (γ ξ : ℝ) (f : ℂ → ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) :
    Measure ℂ × (ℂ → ℂ → ℝ) :=
  (p.1.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))),
    fun u v => (weylScaling p.2 ξ f u v).toReal)

end LatticeProb.LQG
