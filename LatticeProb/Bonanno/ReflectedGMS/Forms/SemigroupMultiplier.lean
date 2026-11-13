/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupMultiplier at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Scalar semigroup multiplier

This file isolates the scalar multiplier used later on the resolvent range.  At
positive time and positive spectral parameter it is the elementary exponential
`exp (t * (1 - 1 / x))`; the smooth gluing function supplies its continuous
extension by zero at nonpositive spectral parameters.

No joint continuity at `(0, 0)` or operator-semigroup statement is asserted.
-/

set_option autoImplicit false

open scoped NNReal

namespace ReflectedGMS.SemigroupMultiplier

/-- The scalar multiplier, with the identity multiplier prescribed at time zero. -/
noncomputable def k (t : ℝ≥0) (x : ℝ) : ℝ :=
  if t = 0 then 1 else Real.exp (t : ℝ) * expNegInvGlue (x / (t : ℝ))

@[simp] theorem k_zero (x : ℝ) : k 0 x = 1 := by simp [k]

/-- For each fixed time, the multiplier is continuous in the spectral variable. -/
theorem continuous_k (t : ℝ≥0) : Continuous (k t) := by
  by_cases ht : t = 0
  · rw [ht]
    rw [show k 0 = (fun _ : ℝ => (1 : ℝ)) by funext x; exact k_zero x]
    exact continuous_const
  · rw [show k t = (fun x : ℝ =>
        Real.exp (t : ℝ) * expNegInvGlue (x / (t : ℝ))) by
      funext x
      rw [k, if_neg ht]]
    have hglue : Continuous expNegInvGlue :=
      (expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous
    exact continuous_const.mul
      (hglue.comp (continuous_id.div_const (t : ℝ)))

/-- Away from the glued boundary, the multiplier has its usual exponential formula. -/
theorem k_eq_exp {t : ℝ≥0} {x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    k t x = Real.exp ((t : ℝ) * (1 - 1 / x)) := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  rw [k, if_neg ht.ne', expNegInvGlue]
  rw [if_neg (not_le.2 (div_pos hx htR))]
  rw [← Real.exp_add]
  congr 1
  field_simp [htR.ne', hx.ne']
  ring

/-- The scalar multipliers form a semigroup at each fixed spectral parameter. -/
theorem k_add (s t : ℝ≥0) (x : ℝ) : k (s + t) x = k s x * k t x := by
  by_cases hs : s = 0
  · simp [hs]
  by_cases ht : t = 0
  · simp [ht]
  have hspos : 0 < s := pos_iff_ne_zero.2 hs
  have htpos : 0 < t := pos_iff_ne_zero.2 ht
  have hstpos : 0 < s + t := add_pos hspos htpos
  rcases le_or_gt x 0 with hx | hx
  · have hsR : 0 < (s : ℝ) := by exact_mod_cast hspos
    have htR : 0 < (t : ℝ) := by exact_mod_cast htpos
    have hsumR : 0 < (s : ℝ) + (t : ℝ) := add_pos hsR htR
    simp [k, hs, ht, hstpos.ne', expNegInvGlue.zero_of_nonpos,
      div_nonpos_of_nonpos_of_nonneg hx hsR.le,
      div_nonpos_of_nonpos_of_nonneg hx htR.le,
      div_nonpos_of_nonpos_of_nonneg hx hsumR.le]
  · rw [k_eq_exp hstpos hx, k_eq_exp hspos hx, k_eq_exp htpos hx,
      ← Real.exp_add]
    congr 1
    push_cast
    ring

/-- The multiplier is nonnegative. -/
theorem k_nonneg (t : ℝ≥0) (x : ℝ) : 0 ≤ k t x := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [k, if_neg ht]
    exact mul_nonneg (Real.exp_nonneg _) (expNegInvGlue.nonneg _)

/-- On the spectral interval `[0, 1]`, the multiplier is at most one. -/
theorem k_le_one {t : ℝ≥0} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : k t x ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  have htpos : 0 < t := pos_iff_ne_zero.2 ht
  rcases hx0.eq_or_lt with rfl | hx
  · simp [k, ht, expNegInvGlue.zero]
  rw [k_eq_exp htpos hx, Real.exp_le_one_iff]
  have hinv : 1 ≤ 1 / x := (le_div_iff₀ hx).2 (by simpa using hx1)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hinv)

/-- Multiplication by `x` approaches the identity with the uniform error bound `t`
on the spectral interval `[0, 1]`. -/
theorem abs_mul_k_sub_le {t : ℝ≥0} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x * k t x - x| ≤ (t : ℝ) := by
  by_cases ht : t = 0
  · simp [ht]
  have htpos : 0 < t := pos_iff_ne_zero.2 ht
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  have hk0 := k_nonneg t x
  have hk1 := k_le_one (t := t) hx0 hx1
  rw [abs_of_nonpos (by nlinarith)]
  rw [k_eq_exp htpos hx]
  let a : ℝ := (t : ℝ) * (1 / x - 1)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have hinv : 1 ≤ 1 / x := (le_div_iff₀ hx).2 (by simpa using hx1)
    exact mul_nonneg (by positivity) (sub_nonneg.2 hinv)
  have hexp : 1 - Real.exp (-a) ≤ a := by
    linarith [Real.add_one_le_exp (-a)]
  have hmul : x * (1 - Real.exp (-a)) ≤ x * a :=
    mul_le_mul_of_nonneg_left hexp hx.le
  have hxa : x * a ≤ (t : ℝ) := by
    dsimp [a]
    field_simp [hx.ne']
    nlinarith
  have hexponent : (t : ℝ) * (1 - 1 / x) = -a := by
    dsimp [a]
    ring
  rw [hexponent]
  nlinarith

end ReflectedGMS.SemigroupMultiplier
