/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.MQGeodesic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Blueprint: Miller–Qian, uniqueness of geodesics (for weak metrics) and the RN bound

Source: MQ = J. Miller, W. Qian, *The geodesics in Liouville quantum gravity are not
Schramm–Loewner evolutions*, arXiv:1812.03913, `literature/src/1812.03913/lqg_geodesics.tex`.

* `MQThm1_2Weak` — MQ Thm 1.2 (`thm:geo_unique`, l. 263–267) for **weak** γ-LQG metrics, as GM
  use it (GM l. 646: "For each fixed `z, w ∈ ℂ`, the `D_h`-geodesic from `z` to `w` is a.s.
  unique. This follows from, e.g., the proof of [MQ, Theorem 1.2] (see also [CONF, Lemma 2.2])";
  CONF l. 505–507: "the theorem is stated for a strong LQG metric, but the proof does not use the
  coordinate change assumption"). Decision D33 (`decisions/DEC-C.md` D-C4): node MQ.T1.2w, proved by
  following MQ l. 459–506 with an unconditional Cameron–Martin step. The versions GM need for
  `D̃` (another weak metric: instantiate `D`) and for `h − φ` (`φ` a fixed bump: a transfer
  corollary by absolute continuity of the law of `h − φ` w.r.t. that of `h` modulo constants,
  Cameron–Martin, and Axiom III with constants) are derived from this Prop, not assumed.
* `MQLem4_1` — MQ Lemma 4.1 (`lem:good_scale_rn`, l. 549–563), in frozen-harmonic-part form.
* `MQLem4_1Gen` — the same with general radii and centring constant (decision D41); implies
  `MQLem4_1` (`mqLem4_1_of_gen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- **MQ Theorem 1.2** (`thm:geo_unique`, l. 263–267) for weak γ-LQG metrics (D33): "Suppose that
`h` is a whole-plane GFF … and that `x, y ∈ ℂ` are distinct. There is a.s. a unique
`𝔡_h`-geodesic `η` connecting `x` and `y`." Here `𝔡 = D` is any weak γ-LQG metric, `γ ∈ (0,2)`
(CONF Lemma 2.2's proof, l. 505–507), and `h` any whole-plane GFF (`IsWholePlaneGFF` allows any
additive constant; MQ fix one). -/
def MQThm1_2Weak : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ x y : ℂ, x ≠ y → ∀ᵐ ω ∂P, UniqueGeod (D (h ω)) x y

/-- **MQ Lemma 4.1, general radii and centring** (decision D41; MQ l. 549–589). MQ's proof
(l. 566–589: cutoff `φ ∈ C_0^∞(B(z,29r/32))` equal to `1` on `B(z,7r/8)`, the RN derivative
`exp((h̃,g)_∇ − ‖g‖²_∇/2)` of the Cameron–Martin shift by `g = (𝔥 − a)φ`, the harmonic gradient
estimate (MQ (4.1)) bounding `‖g‖_∇` by a constant depending on `M`, and Jensen's inequality for
the restriction) does not use the specific ratios `7/8 < 15/16 < 1`, nor that the centring
constant is `𝔥(z)`: here `ρ₁ r < ρ₂ r < r` replace `7r/8 < 15r/16 < r`, and `G` represents
`g − a` for any constant `a` with `|g − a| ≤ M` on `B(z, ρ₂ r)`. This generalizes `MQLem4_1`
(which stays unchanged): take `ρ₁ = 7/8`, `ρ₂ = 15/16`, `a = g(z)`. -/
def MQLem4_1Gen : Prop :=
  ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ < ρ₂ → ρ₂ < 1 → ∀ M : ℝ, 0 < M → ∀ p : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ (z : ℂ) (r : ℝ), 0 < r →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ht : Ω → DistC),
      Measurable ht → IsZeroBoundaryGFF (ballO z r) (fun ω => restrictTo (ballO z r) (ht ω)) P →
    ∀ (g : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd g (Metric.ball z r) → ∀ a : ℝ,
      (∀ w ∈ Metric.ball z (ρ₂ * r), |g w - a| ≤ M) →
    ∀ G : DistC, (∀ φ : TestOn (ballO z r),
        restrictTo (ballO z r) G φ = ∫ x, (g x - a) * φ x) →
      let μ₀ : Measure (DistOn (ballO z (ρ₁ * r))) :=
        P.map fun ω => restrictTo (ballO z (ρ₁ * r)) (ht ω)
      let μg : Measure (DistOn (ballO z (ρ₁ * r))) :=
        P.map fun ω => restrictTo (ballO z (ρ₁ * r)) (ht ω + G)
      μg ≪ μ₀ ∧ μ₀ ≪ μg ∧
        ∫⁻ x, (μg.rnDeriv μ₀ x) ^ p ∂μ₀ ≤ ENNReal.ofReal c ∧
        ∫⁻ x, (μ₀.rnDeriv μg x) ^ p ∂μg ≤ ENNReal.ofReal c

end LQGMetric.Blueprint
