import LatticeProb.Prob.JumpChain.Semigroup
import LatticeProb.Analysis.KernelPowersCS
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Positivity comparison under truncation of jump rates

A common uniformization rate turns a bound on removed jump intensity into a diagonal
perturbation bound. The binomial expansion and Poisson averaging give the exponential
comparison of singleton transition masses.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory ProbabilityTheory Finset.HasAntidiagonal
open scoped NNReal ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*}

/-- Removing rates increases the holding probability by at most the removed intensity over `R`. -/
theorem p_le_of_truncation (rates rates' : BoundedRates S) (hR : rates'.R = rates.R)
    (hq : ∀ i j, rates'.q i j ≤ rates.q i j) {C : ℝ}
    (hC : ∀ i, (∑' j, rates.q i j) - (∑' j, rates'.q i j) ≤ C) (i j : S) :
    rates'.p i j ≤ rates.p i j + if j = i then C / rates.R else 0 := by
  classical
  by_cases hij : j = i
  · subst j
    simp only [p, ite_true, hR]
    have h := (div_le_div_iff_of_pos_right rates.R_pos).2 (hC i)
    rw [sub_div] at h
    linarith
  · simp only [p, if_neg hij, hR, add_zero]
    exact div_le_div_of_nonneg_right (hq i j) rates.R_pos.le

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Singleton kernel powers obey right convolution with the uniformized matrix. -/
theorem kernel_pow_succ_singleton (rates : BoundedRates S) (n : ℕ) (i j : S) :
    (rates.kernel ^ (n + 1)) i {j} =
      ∑' z, (rates.kernel ^ n) i {z} * ENNReal.ofReal (rates.p z j) := by
  rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ (measurableSet_singleton j),
    lintegral_countable']
  simp only [rates.kernel_singleton, mul_comm]

/-- The binomial majorant for a uniformized kernel plus a scalar identity matrix. -/
def holdingMajorant (rates : BoundedRates S) (c : ℝ≥0∞) (n : ℕ) (i j : S) : ℝ≥0∞ :=
  ∑ km ∈ antidiagonal n,
    (n.choose km.1 : ℝ≥0∞) * c ^ km.1 * (rates.kernel ^ km.2) i {j}

/-- At power zero the binomial majorant is the identity kernel. -/
theorem holdingMajorant_zero (rates : BoundedRates S) (c : ℝ≥0∞) (i j : S) :
    rates.holdingMajorant c 0 i j = (rates.kernel ^ 0) i {j} := by
  simp only [holdingMajorant, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]

/-- Pascal's identity gives the convolution recurrence for the binomial majorant. -/
theorem holdingMajorant_succ (rates : BoundedRates S) (c : ℝ≥0∞) (n : ℕ) (i j : S) :
    rates.holdingMajorant c (n + 1) i j =
      (∑' z, rates.holdingMajorant c n i z * ENNReal.ofReal (rates.p z j)) +
        c * rates.holdingMajorant c n i j := by
  classical
  unfold holdingMajorant
  simp only [mul_assoc]
  rw [Finset.sum_antidiagonal_choose_succ_mul
    (fun k m => c ^ k * (rates.kernel ^ m) i {j}) n]
  congr 1
  · simp_rw [kernel_pow_succ_singleton, ← ENNReal.tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply tsum_congr
    intro z
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro km hkm
    have heq : n.choose km.2 = n.choose km.1 :=
      (Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hkm).symm).symm
    rw [heq, pow_succ]
    ring

/-- The diagonal perturbation controls every discrete power by its binomial expansion. -/
theorem kernel_pow_le_holdingMajorant (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, (∑' j, rates.q i j) - (∑' j, rates'.q i j) ≤ C)
    (n : ℕ) (i j : S) :
    (rates'.kernel ^ n) i {j} ≤ rates.holdingMajorant (ENNReal.ofReal (C / rates.R)) n i j := by
  classical
  induction n generalizing i j with
  | zero => rw [holdingMajorant_zero]; rfl
  | succ n ih =>
    rw [rates'.kernel_pow_succ_singleton, holdingMajorant_succ]
    calc
      _ ≤ ∑' z, rates.holdingMajorant (ENNReal.ofReal (C / rates.R)) n i z *
          (ENNReal.ofReal (rates.p z j) +
            if j = z then ENNReal.ofReal (C / rates.R) else 0) := by
        apply ENNReal.tsum_le_tsum
        intro z
        apply mul_le_mul' (ih i z)
        have h := ENNReal.ofReal_le_ofReal (rates.p_le_of_truncation rates' hR hq hC z j)
        rw [ENNReal.ofReal_add (rates.p_nonneg z j)] at h
        · simpa only [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero] using h
        · split_ifs
          · exact div_nonneg hC0 rates.R_pos.le
          · exact le_rfl
      _ = _ := by
        simp_rw [mul_add, ENNReal.tsum_add, mul_ite, mul_zero]
        simp only [tsum_ite_eq', mul_comm]

/-- A binomial coefficient cancels the factorial of the combined index. -/
theorem choose_div_factorial (k m : ℕ) :
    ((k + m).choose k : ℝ) / (k + m).factorial =
      1 / (k.factorial : ℝ) / m.factorial := by
  have hf : ((k + m).choose k : ℝ) * (k.factorial : ℝ) * m.factorial =
      (k + m).factorial := by
    exact_mod_cast (by
      simpa only [Nat.add_sub_cancel_left] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k m))
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hkm : ((k + m).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (k + m).factorial_ne_zero
  field_simp [hk, hm, hkm]
  exact hf

/-- The scalar weight in the binomial expansion separates into two exponential series. -/
theorem poisson_binomial_weight (R t C E : ℝ) (hR : R ≠ 0) (k m : ℕ) :
    (E * (R * t) ^ (k + m) / (k + m).factorial) *
        ((k + m).choose k : ℝ) * (C / R) ^ k =
      ((C * t) ^ k / k.factorial) * (E * (R * t) ^ m / m.factorial) := by
  calc
    _ = E * (R * t) ^ (k + m) * (C / R) ^ k *
        (((k + m).choose k : ℝ) / (k + m).factorial) := by ring
    _ = _ := by
      rw [choose_div_factorial, pow_add, mul_pow, div_pow]
      field_simp [hR]
      ring

/-- Summing finite antidiagonals enumerates every pair of nonnegative indices once. -/
theorem tsum_antidiagonal (f : ℕ × ℕ → ℝ≥0∞) :
    (∑' n, ∑ km ∈ antidiagonal n, f km) = ∑' k, ∑' m, f (k, m) := by
  rw [← ENNReal.tsum_prod,
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f,
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  exact (Finset.sum_finset_coe f (antidiagonal n)).symm

/-- The nonnegative scalar exponential series has its usual real exponential value. -/
theorem tsum_ofReal_pow_div_factorial (x : ℝ) (hx : 0 ≤ x) :
    (∑' k : ℕ, ENNReal.ofReal (x ^ k / k.factorial)) = ENNReal.ofReal (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h.summable, h.tsum_eq]

/-- Poisson averaging of the holding majorant produces the exponential loss exactly. -/
theorem tsum_poisson_holdingMajorant (rates : BoundedRates S) {C : ℝ} (hC : 0 ≤ C)
    (t : ℝ≥0) (i j : S) :
    (∑' n : ℕ, ENNReal.ofReal
      (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
        rates.holdingMajorant (ENNReal.ofReal (C / rates.R)) n i j) =
      ENNReal.ofReal (Real.exp (C * t)) * rates.transitionKernel t i {j} := by
  classical
  have hR0 := rates.R_pos.le
  simp only [holdingMajorant, Finset.mul_sum]
  have hterm (n : ℕ) (km : ℕ × ℕ) (hkm : km ∈ antidiagonal n) :
      ENNReal.ofReal (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
          ((n.choose km.1 : ℝ≥0∞) * ENNReal.ofReal (C / rates.R) ^ km.1 *
            (rates.kernel ^ km.2) i {j}) =
        ENNReal.ofReal ((C * t) ^ km.1 / km.1.factorial) *
          (ENNReal.ofReal (Real.exp (-(rates.R * t)) *
            (rates.R * t) ^ km.2 / km.2.factorial) *
              (rates.kernel ^ km.2) i {j}) := by
    obtain ⟨k, m⟩ := km
    have hn : k + m = n := mem_antidiagonal.mp hkm
    subst n
    have hweight := poisson_binomial_weight rates.R t C (Real.exp (-(rates.R * t)))
      rates.R_pos.ne' k m
    have hnonneg : 0 ≤ Real.exp (-(rates.R * t)) *
        (rates.R * t) ^ (k + m) / (k + m).factorial := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (div_nonneg hC rates.R_pos.le)]
    simp only [← mul_assoc]
    rw [← ENNReal.ofReal_mul hnonneg,
      ← ENNReal.ofReal_mul (mul_nonneg hnonneg (Nat.cast_nonneg _)), hweight,
      ENNReal.ofReal_mul (by positivity : 0 ≤ (C * (t : ℝ)) ^ k / k.factorial), mul_assoc]
  have hexpand : (∑' n : ℕ, ∑ km ∈ antidiagonal n,
      ENNReal.ofReal (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
        ((n.choose km.1 : ℝ≥0∞) * ENNReal.ofReal (C / rates.R) ^ km.1 *
          (rates.kernel ^ km.2) i {j})) =
      ∑' n : ℕ, ∑ km ∈ antidiagonal n,
        ENNReal.ofReal ((C * t) ^ km.1 / km.1.factorial) *
          (ENNReal.ofReal (Real.exp (-(rates.R * t)) *
            (rates.R * t) ^ km.2 / km.2.factorial) *
              (rates.kernel ^ km.2) i {j}) := by
    apply tsum_congr
    intro n
    exact Finset.sum_congr rfl (hterm n)
  rw [hexpand, tsum_antidiagonal]
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right, tsum_ofReal_pow_div_factorial _ (by positivity),
    rates.transitionKernel_singleton]

/-- Truncating jumps loses at most the exponential of the removed total intensity times time. -/
theorem transitionKernel_le_of_truncation (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, (∑' j, rates.q i j) - (∑' j, rates'.q i j) ≤ C)
    (t : ℝ≥0) (i j : S) :
    rates'.transitionKernel t i {j} ≤
      ENNReal.ofReal (Real.exp (C * t)) * rates.transitionKernel t i {j} := by
  rw [rates'.transitionKernel_singleton, hR, ← rates.tsum_poisson_holdingMajorant hC0]
  apply ENNReal.tsum_le_tsum
  intro n
  exact mul_le_mul_right (rates.kernel_pow_le_holdingMajorant rates' hR hq hC0 hC n i j) _

end

end LatticeProb.JumpChain.BoundedRates
