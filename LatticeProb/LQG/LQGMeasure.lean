import Mathlib
import LatticeProb.Gauss.GFF

/-! # The γ-Liouville quantum gravity area measure: general definitions

General copies of the γ-LQG area measure definitions, at the generality of their source, stated over the
whole-plane field layer of `LatticeProb/Gauss/GFF.lean` (namespace `LatticeProb.Gauss`).

* `LatticeProb.LQG.lqgQ γ = 2/γ + γ/2`: the LQG constant `Q` (Duplantier-Sheffield 2011).
* `LatticeProb.LQG.dyadicScale k = 2^{-k}`: the dyadic scales along which the limit is taken.
* `LatticeProb.LQG.lqgApprox γ hε ε = ε^{γ²/2} e^{γ hε(ε,·)} dz`: the approximating measure.
* `LatticeProb.LQG.IsLQGLimit γ hε m`: `m` is locally finite and the vague limit of `lqgApprox γ hε (2^{-k})`.
* `LatticeProb.LQG.IsLQGMeasure P γ hε μ`: almost surely, `μ ω` is the vague limit for the circle averages `hε ω`.
* `LatticeProb.LQG.IsLQGMeasureOfField P γ α₀ hcirc μ`: `μ` is the γ-LQG measure of the field whose circle
  averages are `LatticeProb.Gauss.fieldCircleAverage α₀ (hcirc ω)`.

Provenance. Copies of the definitions `dyadicScale`, `lqgApprox`, `IsLQGLimit`, `IsLQGMeasure`,
`IsLQGMeasureOfField` (Defs/LQG.lean) and `lqgQ` (Defs/Notation.lean) of Bou-Rabee and Gwynne,
*Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795). No statement, hypothesis or conclusion of the
source is changed. The terminology follows Duplantier-Sheffield, *Liouville quantum gravity and KPZ* (2011), and
Berestycki-Powell, *Gaussian free field, Liouville quantum gravity and Gaussian multiplicative chaos*. The bridge
lemmas (HB definition ↔ LP definition) are in `HarmonicBalls/FirstPass/LPBridge/M4.lean`.

Helper theorems inside the source bodies: none (the bodies contain no proof terms), so none is restated here.
The sanity lemmas and uniqueness lemmas of the source (`dyadicScale_pos`, `lqgApprox_neg_log`, `isLQGLimit_volume`,
`IsLQGLimit.unique`, `IsLQGMeasure.ae_eq`) are theorems, not definitions, and are not included here.
-/

open MeasureTheory Filter Topology

namespace LatticeProb.LQG

/-- The LQG constant `Q = 2/γ + γ/2` (Duplantier-Sheffield 2011). -/
noncomputable def lqgQ (γ : ℝ) : ℝ :=
  2 / γ + γ / 2

/-- The dyadic scale `2^{-k}`. -/
noncomputable def dyadicScale (k : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ k

/-- The approximation `ε^{γ²/2} e^{γ hε ε z} dz` of the γ-LQG measure, where `hε ε z` is the circle average at
scale `ε` of the field at `z`. This is the Lebesgue measure `volume` with density `ε^{γ²/2} exp(γ hε ε z)`. -/
noncomputable def lqgApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))

/-- `IsLQGLimit γ hε m`: the measure `m` on `ℂ` is locally finite (Radon) and is the vague limit of the
approximations `lqgApprox γ hε (2^{-k})` along the dyadic scales: for every continuous `f : ℂ → ℝ` with compact
support, `∫ f d(lqgApprox γ hε 2^{-k}) → ∫ f dm` as `k → ∞` (Duplantier-Sheffield 2011, Prop. 1.1). -/
structure IsLQGLimit (γ : ℝ) (hε : ℝ → ℂ → ℝ) (m : Measure ℂ) : Prop where
  /-- The limit is a Radon measure. -/
  isLocallyFiniteMeasure : IsLocallyFiniteMeasure m
  /-- Vague convergence along the dyadic scales. -/
  tendsto_integral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) atTop (𝓝 (∫ z, f z ∂m))

/-- `IsLQGMeasure P γ hε μ`: the random measure `μ : Ω → Measure ℂ` is the γ-LQG measure of the random
circle-average function `hε ω`: almost surely, `μ ω` is an `IsLQGLimit` for `hε ω`. Intended for `γ ∈ (0, 2)`. -/
def IsLQGMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hε : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) : Prop :=
  ∀ᵐ ω ∂P, IsLQGLimit γ (hε ω) (μ ω)

/-- `IsLQGMeasureOfField P γ α₀ hcirc μ`: `μ` is the γ-LQG area measure of the field `h = h^ℂ - α₀ log |·|`
whose circle averages are `LatticeProb.Gauss.fieldCircleAverage α₀ (hcirc ω)`, where `hcirc ω r z` are the circle
averages of the whole-plane GFF `h^ℂ` (`LatticeProb.Gauss.IsWholePlaneGFF`). The construction for `γ ∈ (0, 2)` is
Duplantier-Sheffield 2011, Prop. 1.1, as cited in the source. The limit is locally finite near the origin only when
`α₀ < lqgQ γ`, so statements using this definition assume `0 < γ < 2` and `α₀ < lqgQ γ`. -/
def IsLQGMeasureOfField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsLQGMeasure P γ (fun ω => LatticeProb.Gauss.fieldCircleAverage α₀ (hcirc ω)) μ

end LatticeProb.LQG
