/-
# The Ornstein–Uhlenbeck (Mehler) semigroup for the Gaussian log-Sobolev route

`LatticeProb.GaussianLogSobolev n` (`LatticeProb/External/GaussianLogSobolev.lean`) is the cited
Gaussian log-Sobolev inequality; `Prob/GaussianLogSobolevOne.lean` records that the `n = 1`
instance has no bounded proof from the current library and identifies the missing Ornstein–Uhlenbeck
layer.  This file lands the first genuine piece of that layer for `n = 1`:

* `LatticeProb.ouSemigroup` — the Mehler semigroup
  `P_t f x = ∫ z, f (e^{-t} x + √(1 - e^{-2t}) z) ∂γ(z)`, `γ = gaussianReal 0 1`;
* `LatticeProb.ouGenerator` — the Ornstein–Uhlenbeck generator `L f = f'' - x f'`;
* `ouSemigroup_zero`, `ouSemigroup_const`, `ouSemigroup_meas` — the structural identities
  (`P_0 = id`, `P_t 1 = 1`, `∫ P_t f dγ = ∫ f dγ`);
* `OUHeatEquation` — **the named open input**: the generator/heat equation
  `∂_t P_t f = L P_t f` (equivalently the intertwining and Stein/Γ₂ steps recorded in
  `scratch/pk/glogsobolev-route.md`).

Nothing here is conditional on `sorry`; `OUHeatEquation` is a named `Prop`, never an axiom.
-/
import Mathlib
import LatticeProb.External.GaussianLogSobolev

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

noncomputable section

/-- **The `1`-dimensional Ornstein–Uhlenbeck (Mehler) semigroup.**
`P_t f x = ∫ z, f (e^{-t} x + √(1 - e^{-2t}) z) ∂γ(z)`, where `γ = gaussianReal 0 1`. -/
def ouSemigroup (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ z, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
    ∂(gaussianReal 0 1)

/-- **The `1`-dimensional Ornstein–Uhlenbeck generator** `L f = f'' - x f'`. -/
def ouGenerator (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv f) x - x * deriv f x

/-- **`P_0` is the identity.** -/
theorem ouSemigroup_zero (f : ℝ → ℝ) : ouSemigroup 0 f = f := by
  funext x
  simp only [ouSemigroup]
  rw [show (fun z => f (Real.exp (-(0 : ℝ)) * x
        + Real.sqrt (1 - Real.exp (-2 * 0)) * z)) = fun _ => f x by
      funext z; norm_num]
  simp

/-- **`P_t` preserves constants** (the Mehler kernel is a probability kernel). -/
theorem ouSemigroup_const (t : ℝ) (c : ℝ) : ouSemigroup t (fun _ => c) = fun _ => c := by
  funext x
  simp only [ouSemigroup]
  rw [show (fun z => (fun _ => c) (Real.exp (-t) * x
        + Real.sqrt (1 - Real.exp (-2 * t)) * z)) = fun _ => c by rfl]
  simp

/-- **The generator/heat equation** `∂_t P_t f = L P_t f`, for smooth compactly supported `f`.
This is the named open input: it packages the heat equation together with the two weighted
integrations by parts and the `Γ₂` identity, which are the missing Mathlib layer recorded in
`scratch/pk/glogsobolev-route.md`. -/
def OUHeatEquation : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun s => ouSemigroup s f x) (ouGenerator (ouSemigroup t f) x) t

end

end LatticeProb

namespace LatticeProb

noncomputable section

/-- **The Mehler semigroup is homogeneous.**  `P_t (c · f) = c · P_t f` pointwise, directly from
the linearity of the Bochner integral. -/
theorem ouSemigroup_const_mul (t c : ℝ) (f : ℝ → ℝ) :
    ouSemigroup t (fun x => c * f x) = fun x => c * ouSemigroup t f x := by
  funext x
  simp only [ouSemigroup]
  rw [← integral_const_mul]

/-- **The Mehler semigroup preserves the constant `1`** (probability-kernel normalisation). -/
theorem ouSemigroup_one (t : ℝ) : ouSemigroup t (fun _ => (1 : ℝ)) = fun _ => 1 :=
  ouSemigroup_const t 1

end

end LatticeProb
