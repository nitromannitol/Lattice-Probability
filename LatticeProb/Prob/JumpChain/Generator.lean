import LatticeProb.Prob.JumpChain.Rates
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The bounded-rate generator and the discrete transition operator

For a bounded observable, the rate-weighted increment is absolutely summable. The
uniformized discrete transition operator has exactly this generator after multiplying
its increment by the clock rate. No integrability assumption is added to boundedness.
-/

namespace LatticeProb.JumpChain

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

namespace BoundedRates

/-- A bounded observable is summable against each row of the rate matrix. -/
theorem summable_q_mul (rates : BoundedRates S) (i : S) (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) : Summable (fun j ↦ rates.q i j * f j) := by
  apply ((rates.summable i).mul_right C).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rates.q_nonneg i j)]
  exact mul_le_mul_of_nonneg_left (hf j) (rates.q_nonneg i j)

/-- Bounded observables have an absolutely summable jump-generator increment. -/
theorem summable_q_mul_sub (rates : BoundedRates S) (i : S) (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    Summable (fun j ↦ rates.q i j * (f j - f i)) := by
  have h := (rates.summable_q_mul i f hf).sub ((rates.summable i).mul_right (f i))
  exact h.congr fun j ↦ (mul_sub _ _ _).symm

/-- A bounded observable is summable against a uniformized transition row. -/
theorem summable_p_mul (rates : BoundedRates S) (i : S) (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) : Summable (fun j ↦ rates.p i j * f j) := by
  apply (rates.hasSum_p i).summable.mul_right C |>.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rates.p_nonneg i j)]
  exact mul_le_mul_of_nonneg_left (hf j) (rates.p_nonneg i j)

/-- The discrete transition operator splits into its holding term and rate-weighted average. -/
theorem tsum_p_mul (rates : BoundedRates S) (i : S) (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    (∑' j, rates.p i j * f j) =
      (1 - (∑' j, rates.q i j) / rates.R) * f i +
        (∑' j, rates.q i j * f j) / rates.R := by
  classical
  have hdiag : Summable (fun j ↦
      (if j = i then 1 - (∑' k, rates.q i k) / rates.R else 0) * f j) := by
    apply (hasSum_ite_eq i ((1 - (∑' k, rates.q i k) / rates.R) * f i)).summable.congr
    intro j
    by_cases hj : j = i <;> simp only [hj, if_true, if_false, zero_mul]
  have hrow := (rates.summable_q_mul i f hf).div_const rates.R
  calc
    _ = ∑' j, ((if j = i then 1 - (∑' k, rates.q i k) / rates.R else 0) * f j +
        rates.q i j * f j / rates.R) := by
      apply tsum_congr
      intro j
      rw [rates.p_eq_add, add_mul]
      congr 1
      ring
    _ = _ := by
      rw [hdiag.tsum_add hrow]
      simp only [ite_mul, zero_mul, tsum_ite_eq, tsum_div_const]

/-- The uniformized operator increment is exactly the jump generator on bounded observables. -/
theorem uniformized_generator (rates : BoundedRates S) (i : S) (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    rates.R * ((∑' j, rates.p i j * f j) - f i) =
      ∑' j, rates.q i j * (f j - f i) := by
  have hsplit : (∑' j, rates.q i j * (f j - f i)) =
      (∑' j, rates.q i j * f j) - (∑' j, rates.q i j) * f i := by
    simp_rw [mul_sub]
    rw [(rates.summable_q_mul i f hf).tsum_sub ((rates.summable i).mul_right (f i)),
      tsum_mul_right]
  rw [hsplit, rates.tsum_p_mul i f hf]
  field_simp [rates.R_pos.ne']
  ring

/-- Changing the dominating clock rate gives the exact affine holding correction. -/
theorem p_eq_affine_combination (rates larger : BoundedRates S)
    (hq : larger.q = rates.q) (i j : S) :
    larger.p i j = rates.R / larger.R * rates.p i j +
      (1 - rates.R / larger.R) * (if j = i then 1 else 0) := by
  classical
  simp only [p, hq]
  split_ifs
  all_goals
    field_simp [rates.R_pos.ne', larger.R_pos.ne']
    ring

end BoundedRates

end

end LatticeProb.JumpChain
