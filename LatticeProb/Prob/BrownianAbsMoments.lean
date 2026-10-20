/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: QuantumZipper/Proofs/Probability/BMMoments.lean.
-/

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Absolute moments of Brownian motion

For a pre-Brownian motion `B : ℝ≥0 → Ω → ℝ` under a probability measure `P`, this file proves:

* `gaussianAbsMoment n`, the `n`-th absolute moment of the standard Gaussian `gaussianReal 0 1`,
  is nonnegative;
* `brownian_integrable_abs_pow`: for every `n`, `|B t|ⁿ` is integrable;
* `brownian_integral_abs_pow_eq`: the expectation of `|B t|ⁿ` equals `gaussianAbsMoment n * t ^ (n / 2)`;
  `brownian_integral_abs_pow_le` is the corresponding upper bound.

The scaling identity for the absolute moments of `gaussianReal 0 v` is proved first, as the private
lemma `integral_abs_pow_gaussianReal_eq`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- The `n`-th absolute moment of the standard Gaussian `gaussianReal 0 1`. -/
def gaussianAbsMoment (n : ℕ) : ℝ := ∫ x, |x| ^ n ∂(gaussianReal 0 1)

/-- The `n`-th absolute moment of the standard Gaussian is nonnegative. -/
theorem gaussianAbsMoment_nonneg (n : ℕ) : 0 ≤ gaussianAbsMoment n :=
  integral_nonneg fun x => pow_nonneg (abs_nonneg x) n

/-- Every absolute power `|x| ^ n` is integrable for the centred Gaussian of variance `v`. -/
private lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) (n : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' (n : ℝ≥0∞) (by simp)
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

/-- Scaling identity: the `n`-th absolute moment of `gaussianReal 0 v` is `v ^ (n / 2)` times the
`n`-th absolute moment of the standard Gaussian. It follows from `gaussianReal 0 v` being the
image of `gaussianReal 0 1` under `x ↦ √v * x`. -/
private lemma integral_abs_pow_gaussianReal_eq (v : ℝ≥0) (n : ℕ) :
    ∫ x, |x| ^ n ∂(gaussianReal 0 v) = (v : ℝ) ^ ((n : ℝ) / 2) * gaussianAbsMoment n := by
  have hv0 : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hsqrt : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hcsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv0
  have hmap : gaussianReal (0 : ℝ) v =
      (gaussianReal (0 : ℝ) 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      push_cast
      rw [hcsq]
      ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ n = (v : ℝ) ^ ((n : ℝ) / 2) * |x| ^ n := by
    intro x
    rw [abs_mul, abs_of_nonneg hsqrt, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (Real.sqrt v) n, Real.sqrt_eq_rpow, ← Real.rpow_mul hv0]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

/-- For every `t` and `n`, the random variable `|B t| ^ n` is integrable. -/
theorem brownian_integrable_abs_pow (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => |B t ω| ^ n) P := by
  have hX := hB.hasLaw_eval t
  have h : Integrable (fun x : ℝ => |x| ^ n) (P.map (B t)) := by
    rw [hX.map_eq]
    exact integrable_abs_pow_gaussianReal t n
  exact (integrable_map_measure (by fun_prop : Measurable fun x : ℝ => |x| ^ n).aestronglyMeasurable
    hX.aemeasurable).1 h

/-- The expectation of `|B t| ^ n` is `gaussianAbsMoment n * t ^ (n / 2)`. -/
theorem brownian_integral_abs_pow_eq (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    ∫ ω, |B t ω| ^ n ∂P = gaussianAbsMoment n * (t : ℝ) ^ ((n : ℝ) / 2) := by
  have h : ∫ ω, |B t ω| ^ n ∂P = ∫ x, |x| ^ n ∂(gaussianReal 0 t) :=
    (hB.hasLaw_eval t).integral_comp (f := fun x : ℝ => |x| ^ n) (by fun_prop)
  rw [h, integral_abs_pow_gaussianReal_eq]
  exact mul_comm _ _

/-- The `n`-th absolute moment of `B t` is at most `gaussianAbsMoment n * t ^ (n / 2)`; it is
in fact equal (`brownian_integral_abs_pow_eq`). -/
theorem brownian_integral_abs_pow_le (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    ∫ ω, |B t ω| ^ n ∂P ≤ gaussianAbsMoment n * (t : ℝ) ^ ((n : ℝ) / 2) :=
  (brownian_integral_abs_pow_eq hB t n).le

end LatticeProb
