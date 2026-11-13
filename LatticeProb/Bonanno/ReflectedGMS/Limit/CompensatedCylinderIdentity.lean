/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CompensatedCylinderIdentity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppingCrossMoment
import LatticeProb.Bonanno.ReflectedGMS.Limit.ThresholdStoppedMartingaleMoments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.LocallyFinite
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The asymptotic compensated cylinder identity of the prelimit array

`ReflectedGMS.Limit.InterpolatedArrayUIIntegration.integral_pathCylinderTest_mul_compensated_sq_interpolated_limit_eq_zero_of_tendsto`
and
`ReflectedGMS.Limit.QuadraticLimitMartingale.integral_pathCylinderTest_mul_compensated_sq_limit_eq_zero_of_tendsto`
both carry one remaining undischarged premise, named `hcomp` in both signatures:

```
Tendsto (fun n => ∫ f, (H fun i => f (u i)) * ((f t - f s) ^ 2 - v)
  ∂(μs n : Measure C(Set.Icc (0 : ℝ) Tr, ℝ))) atTop (𝓝 0)
```

This file discharges that premise from the martingale structure of the prelimit array plus
three named, atomic, *non-martingale* inputs.  The conclusion is copied verbatim from the
consumer signature.

## What is proved here outright

* `integrable_bracket_of_square_martingale` — the compensator `A r` of a square-integrable
  martingale is integrable.
* `condExp_compensated_sq_increment_eq_zero` — **the exact conditional orthogonality**
  `P[(M b - M a)² - (A b - A a) | 𝔽 a] = 0` for a *random* compensator `A`.  The existing
  `ReflectedGMS.MartingaleLimit.condExp_increment_sq_eq_of_square_martingale`
  (`GaussianIdentificationUnlocalization`) proves only the deterministic-rate case
  `A u = C u`, and `ReflectedGMS.martingale_sq_increment_integral_eq_compensator`
  (`Forms/SquareCompensatorEnergy`) proves only the unweighted, unconditional case; neither
  suffices for a cylinder test.
* `integral_mul_compensated_sq_increment_eq_zero` — the **exact compensated cylinder
  identity at grid times**: for every bounded `𝔽 a`-measurable weight `G`,
  `∫ G · ((M b - M a)² - (A b - A a)) dP = 0`.  This is the entire martingale content of
  the asymptotic identity, and it is unconditional.
* `abs_integral_mul_le_of_compensated_split` — the purely integration-theoretic four-term
  bound that turns the grid identity into a bound on the interpolated cylinder integral.

## What remains an input, and why that is honest

The path laws `μs n` are the laws of a piecewise **linear interpolation** of the array, and
the cylinder times `u i, s, t` are arbitrary reals, not grid times.  A linear interpolation
of a martingale is not a martingale, so the exact identity above applies to the grid values
only.  The residual is exactly the mismatch between the two, and it is stated as three
separate `Tendsto … (𝓝 0)` inputs of the main theorem:

* `htest` — the cylinder **test** evaluated on the interpolated path matches the one
  evaluated on the grid values, weighted by the compensated grid increment.  This follows
  from convergence in probability of the interpolation to the grid values at the times
  `u i` together with uniform integrability of the squared grid increments; it contains no
  martingale content.
* `hincr` — the squared **increment** of the interpolated path matches the squared grid
  increment in `L¹`.  Same character; it is the `L¹` form of the interpolation modulus
  already studied in `ReflectedGMS.Limit.LinearInterpolationModulus` and
  `ReflectedGMS.Limit.MartingaleInterpolationTightness`.
* `hbracket` — the **bracket increment** `A (b n) - A (a n)` converges in `L¹` to the
  deterministic value `v`.  This is the deliverable of the separately owned array-bracket
  limit packet; it is the genuinely probabilistic remaining input and it is *not* implied
  by anything proved here.

None of the three is the conclusion, and none of them mentions the cylinder identity: the
orthogonality that makes the identity true is supplied here, unconditionally.

**This file therefore does not certify `hcomp`, and hence does not certify the quenched
invariance principle.**  It is an honestly conditional reduction of `hcomp` to the three
inputs above, with the martingale step discharged.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ReflectedGMS.MartingaleLimit

/-! ### The exact compensated identity at grid times -/

section Exact

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {𝔽 : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}

/-- The compensator of a square-integrable martingale is integrable at every time. -/
theorem integrable_bracket_of_square_martingale
    (hC : Martingale (fun r ω => M r ω * M r ω - A r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) (r : ℝ≥0) : Integrable (A r) P := by
  have hsq : Integrable (fun ω => M r ω * M r ω) P := (h2 r).integrable_mul (h2 r)
  have hU : Integrable (fun ω => M r ω * M r ω - A r ω) P := hC.integrable r
  refine (hsq.sub' hU).congr (Filter.Eventually.of_forall fun ω => ?_)
  ring

/-- **Exact conditional orthogonality of the compensated square increment, with a random
compensator.**  If `M` is a martingale, `M²  - A` is a martingale and `M` is square
integrable at every time, then

`P[(M b - M a)² - (A b - A a) | 𝔽 a] = 0` almost surely

for all `a ≤ b`.  No boundedness, no stopping, no localizing sequence, and — unlike
`condExp_increment_sq_eq_of_square_martingale` — no assumption that the compensator is the
deterministic map `u ↦ C u`. -/
theorem condExp_compensated_sq_increment_eq_zero
    (hM : Martingale M 𝔽 P)
    (hC : Martingale (fun r ω => M r ω * M r ω - A r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {a b : ℝ≥0} (hab : a ≤ b) :
    P[fun ω => (M b ω - M a ω) ^ 2 - (A b ω - A a ω) | 𝔽 a] =ᵐ[P] 0 := by
  have hUb : Integrable (fun ω => M b ω * M b ω - A b ω) P := hC.integrable b
  have hUa : Integrable (fun ω => M a ω * M a ω - A a ω) P := hC.integrable a
  have hMdiff : Integrable (M b - M a) P := (hM.integrable b).sub (hM.integrable a)
  have hY2 : Integrable ((fun ω => 2 * M a ω) * (M b - M a)) P :=
    ((h2 a).const_mul 2).integrable_mul ((h2 b).sub (h2 a))
  have hMa2 : StronglyMeasurable[𝔽 a] (fun ω => 2 * M a ω) :=
    (hM.stronglyMeasurable a).const_mul 2
  have hdec : (fun ω => (M b ω - M a ω) ^ 2 - (A b ω - A a ω)) =
      ((fun ω => M b ω * M b ω - A b ω) - (fun ω => M a ω * M a ω - A a ω))
        - (fun ω => 2 * M a ω) * (M b - M a) := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have e1 : P[((fun ω => M b ω * M b ω - A b ω) - (fun ω => M a ω * M a ω - A a ω))
        - (fun ω => 2 * M a ω) * (M b - M a) | 𝔽 a]
      =ᵐ[P] P[(fun ω => M b ω * M b ω - A b ω) - (fun ω => M a ω * M a ω - A a ω) | 𝔽 a]
        - P[(fun ω => 2 * M a ω) * (M b - M a) | 𝔽 a] :=
    condExp_sub (hUb.sub hUa) hY2 (𝔽 a)
  have e2 : P[(fun ω => M b ω * M b ω - A b ω) - (fun ω => M a ω * M a ω - A a ω) | 𝔽 a]
      =ᵐ[P] P[(fun ω => M b ω * M b ω - A b ω) | 𝔽 a]
        - P[(fun ω => M a ω * M a ω - A a ω) | 𝔽 a] :=
    condExp_sub hUb hUa (𝔽 a)
  have e3 : P[(fun ω => 2 * M a ω) * (M b - M a) | 𝔽 a]
      =ᵐ[P] (fun ω => 2 * M a ω) * P[M b - M a | 𝔽 a] :=
    condExp_mul_of_stronglyMeasurable_left hMa2 hY2 hMdiff
  have hMaeq : P[M a | 𝔽 a] = M a :=
    condExp_of_stronglyMeasurable (𝔽.le a) (hM.stronglyMeasurable a) (hM.integrable a)
  have e4 : P[M b - M a | 𝔽 a] =ᵐ[P] 0 := by
    have hsub : P[M b - M a | 𝔽 a] =ᵐ[P] P[M b | 𝔽 a] - P[M a | 𝔽 a] :=
      condExp_sub (hM.integrable b) (hM.integrable a) (𝔽 a)
    filter_upwards [hsub, hM.condExp_ae_eq hab] with ω g1 g2
    simp only [Pi.sub_apply, Pi.zero_apply, hMaeq] at g1 ⊢
    rw [g1, g2, sub_self]
  have e5 : P[(fun ω => M a ω * M a ω - A a ω) | 𝔽 a] = fun ω => M a ω * M a ω - A a ω :=
    condExp_of_stronglyMeasurable (𝔽.le a) (hC.stronglyMeasurable a) hUa
  have e6 : P[(fun ω => M b ω * M b ω - A b ω) | 𝔽 a]
      =ᵐ[P] fun ω => M a ω * M a ω - A a ω := hC.condExp_ae_eq hab
  rw [hdec]
  filter_upwards [e1, e2, e3, e4, e6] with ω a1 a2 a3 a4 a6
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply, e5] at a1 a2 a3 a4 a6 ⊢
  rw [a4, mul_zero] at a3
  rw [a1, a2, a3, a6]
  ring

/-- **Exact compensated cylinder identity at grid times.**  For every bounded weight `G`
measurable with respect to the past `𝔽 a`, the compensated squared increment of a
square-integrable martingale integrates to exactly zero against `G`.

This is the martingale content of the asymptotic cylinder identity `hcomp`, and it is
unconditional. -/
theorem integral_mul_compensated_sq_increment_eq_zero
    (hM : Martingale M 𝔽 P)
    (hC : Martingale (fun r ω => M r ω * M r ω - A r ω) 𝔽 P)
    (h2 : ∀ r, MemLp (M r) 2 P) {a b : ℝ≥0} (hab : a ≤ b)
    {G : Ω → ℝ} (hG : StronglyMeasurable[𝔽 a] G) {K : ℝ} (hGb : ∀ ω, |G ω| ≤ K) :
    ∫ ω, G ω * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω)) ∂P = 0 := by
  have hD2 : Integrable (fun ω => (M b ω - M a ω) ^ 2) P :=
    ((h2 b).sub (h2 a)).integrable_sq
  have hdA : Integrable (fun ω => A b ω - A a ω) P :=
    (integrable_bracket_of_square_martingale hC h2 b).sub'
      (integrable_bracket_of_square_martingale hC h2 a)
  have hX : Integrable (fun ω => (M b ω - M a ω) ^ 2 - (A b ω - A a ω)) P := hD2.sub' hdA
  have hGm : AEStronglyMeasurable G P := (hG.mono (𝔽.le a)).aestronglyMeasurable
  have hGX : Integrable (G * fun ω => (M b ω - M a ω) ^ 2 - (A b ω - A a ω)) P :=
    hX.bdd_mul hGm (Filter.Eventually.of_forall fun ω => by simpa using hGb ω)
  have hz := condExp_compensated_sq_increment_eq_zero hM hC h2 hab
  have hpull := condExp_mul_of_stronglyMeasurable_left hG hGX hX
  calc ∫ ω, G ω * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω)) ∂P
      = ∫ ω, (P[G * fun ω => (M b ω - M a ω) ^ 2 - (A b ω - A a ω) | 𝔽 a]) ω ∂P :=
        (integral_condExp (𝔽.le a)).symm
    _ = ∫ _ω : Ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hz] with ω h1 h2'
        simp only [Pi.mul_apply, Pi.zero_apply] at h1 h2' ⊢
        rw [h1, h2', mul_zero]
    _ = 0 := integral_zero _ _

end Exact

/-! ### Measurability of a finite-dimensional bounded continuous test -/

/-! ### The four-term split -/

/-! ### The asymptotic compensated cylinder identity -/

section Reduction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

end Reduction

end ReflectedGMS.MartingaleLimit
