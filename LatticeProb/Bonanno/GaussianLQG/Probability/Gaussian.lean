/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module GaussianLQG.Probability.Gaussian at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian facts (blueprint Lemma `lem:gauss`)

Let `Z` be a real random variable with law `N(0, v)` (`HasLaw Z (gaussianReal 0 v) P`), so
`s = √v` is its standard deviation.

* Moments: `integral_of_hasLaw_gaussianReal` (`E Z = 0`), `integral_sq_of_hasLaw_gaussianReal`
  (`E Z² = v`), and the absolute moments `integral_abs_rpow_of_hasLaw_gaussianReal`:
  `E|Z|^p = v^{p/2} E|N|^p` with `N ∼ N(0,1)`, i.e. `‖Z‖_p = s ‖N‖_p`
  (`integral_abs_rpow_rpow_inv_of_hasLaw_gaussianReal`).
* Exponential moments: `integral_exp_mul_of_hasLaw_gaussianReal`: `E e^{tZ} = e^{v t²/2}`.
* Two-sided tail: `measureReal_le_abs_le_of_hasLaw_gaussianReal`:
  `P[|Z| ≥ x] ≤ 2 e^{-x²/(2v)}` for `x ≥ 0` (so also `P[|Z| > x]`).
* Expected maximum: `integral_iSup_abs_le` — if `Z_1, …, Z_n` are centered Gaussians with
  variances at most `s²` (no independence is assumed), then `E max_i |Z_i| ≤ s √(2 log(2n))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

section OneDim

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}

/-- `N(0, v)` is the image of `N(0, 1)` under `x ↦ √v x`. -/
theorem gaussianReal_eq_map_sqrt_mul (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map fun x => Real.sqrt v * x := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    push_cast
    rw [Real.sq_sqrt v.coe_nonneg]
    ring

/-- **Absolute moments** (Lemma `lem:gauss`): `E|Z|^p = v^{p/2} E|N|^p` for `Z ∼ N(0, v)`. -/
theorem integral_abs_rpow_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    (p : ℝ) :
    ∫ ω, |X ω| ^ p ∂P = (v : ℝ) ^ (p / 2) * ∫ x, |x| ^ p ∂gaussianReal 0 1 := by
  have hm : Measurable fun x : ℝ => |x| ^ p := by fun_prop
  have h := hX.integral_comp (f := fun x : ℝ => |x| ^ p) hm.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, gaussianReal_eq_map_sqrt_mul, integral_map (by fun_prop) hm.aestronglyMeasurable,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hs : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  dsimp only
  rw [abs_mul, abs_of_nonneg hs, Real.mul_rpow hs (abs_nonneg x), Real.sqrt_eq_rpow,
    ← Real.rpow_mul v.coe_nonneg]
  ring_nf

end OneDim

/-! ## The expected maximum of finitely many Gaussians -/

section Max

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {Z : ι → Ω → ℝ} {v : ι → ℝ≥0}

end Max

end GaussianLQG
