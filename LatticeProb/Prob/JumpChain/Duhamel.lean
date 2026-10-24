import LatticeProb.Prob.JumpChain.Truncation
import LatticeProb.Analysis.KernelPowerBridge

/-!
# Additive comparison under removal of jump rates

Uniformization at a common rate gives an additive perturbation estimate. Removed rates
are nonnegative; the negative diagonal correction can be discarded.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

variable {S : Type*}

/-- Removing rates bounds the original transition matrix by the new matrix and removed rates. -/
theorem p_le_add_removed (rates rates' : BoundedRates S) (hR : rates'.R = rates.R)
    (hq : ∀ i j, rates'.q i j ≤ rates.q i j) (i j : S) :
    rates.p i j ≤ rates'.p i j + (rates.q i j - rates'.q i j) / rates.R := by
  classical
  by_cases hij : j = i
  · subst j
    have hsum := (rates'.summable i).tsum_le_tsum (hq i) (rates.summable i)
    simp only [p, ite_true, rates.q_self, rates'.q_self, sub_self, zero_div, add_zero, hR]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hsum rates.R_pos.le) 1
  · simp only [p, if_neg hij, hR]
    rw [sub_div]
    exact le_of_eq (by ring)

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Left convolution of discrete powers, on an arbitrary set of the countable state space. -/
theorem kernel_pow_succ_set_left (rates : BoundedRates S) (n : ℕ) (i : S) (A : Set S) :
    (rates.kernel ^ (n + 1)) i A =
      ∑' z, ENNReal.ofReal (rates.p i z) * (rates.kernel ^ n) z A := by
  have hA : MeasurableSet A := Set.to_countable A |>.measurableSet
  rw [Nat.add_comm n 1, Kernel.pow_add_apply_eq_lintegral _ _ _ _ hA,
    pow_one, lintegral_countable']
  simp only [rates.kernel_singleton, mul_comm]

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
/-- Rows of the uniformized matrix have total mass one in the nonnegative extended reals. -/
theorem tsum_ofReal_p (rates : BoundedRates S) (i : S) :
    (∑' z, ENNReal.ofReal (rates.p i z)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (rates.p_nonneg i) (rates.hasSum_p i).summable,
    (rates.hasSum_p i).tsum_eq, ENNReal.ofReal_one]

/-- A uniform bound on the removed convolution accumulates linearly with the power. -/
theorem kernel_pow_le_add_removed (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    (c : ℝ≥0∞) (A : Set S)
    (herr : ∀ n i, (∑' z, ENNReal.ofReal ((rates.q i z - rates'.q i z) / rates.R) *
      (rates.kernel ^ n) z A) ≤ c) (n : ℕ) (i : S) :
    (rates.kernel ^ n) i A ≤ (rates'.kernel ^ n) i A + n * c := by
  induction n generalizing i with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    rw [rates.kernel_pow_succ_set_left, rates'.kernel_pow_succ_set_left]
    calc
      _ ≤ ∑' z, (ENNReal.ofReal (rates'.p i z) +
          ENNReal.ofReal ((rates.q i z - rates'.q i z) / rates.R)) *
            (rates.kernel ^ n) z A := by
        apply ENNReal.tsum_le_tsum
        intro z
        apply mul_le_mul_left
        rw [← ENNReal.ofReal_add (rates'.p_nonneg i z)
          (div_nonneg (sub_nonneg.mpr (hq i z)) rates.R_pos.le)]
        exact ENNReal.ofReal_le_ofReal (rates.p_le_add_removed rates' hR hq i z)
      _ = (∑' z, ENNReal.ofReal (rates'.p i z) * (rates.kernel ^ n) z A) +
          ∑' z, ENNReal.ofReal ((rates.q i z - rates'.q i z) / rates.R) *
            (rates.kernel ^ n) z A := by simp only [add_mul, ENNReal.tsum_add]
      _ ≤ (∑' z, ENNReal.ofReal (rates'.p i z) *
          ((rates'.kernel ^ n) z A + n * c)) + c := by
        exact add_le_add (ENNReal.tsum_le_tsum fun z => mul_le_mul_right (ih z) _)
          (herr n i)
      _ = _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          rates'.tsum_ofReal_p, one_mul, Nat.cast_add, Nat.cast_one, add_mul]
        ac_rfl

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
/-- The removed row mass is the difference of the two total jump rates, divided by `R`. -/
theorem tsum_removed (rates rates' : BoundedRates S)
    (hq : ∀ i j, rates'.q i j ≤ rates.q i j) (i : S) :
    (∑' z, ENNReal.ofReal ((rates.q i z - rates'.q i z) / rates.R)) =
      ENNReal.ofReal (((∑' z, rates.q i z) - ∑' z, rates'.q i z) / rates.R) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun z => div_nonneg (sub_nonneg.mpr (hq i z)) rates.R_pos.le)
    (((rates.summable i).sub (rates'.summable i)).div_const rates.R),
    tsum_div_const, (rates.summable i).tsum_sub (rates'.summable i)]

/-- A bound on total removed intensity controls every set at each discrete power. -/
theorem kernel_pow_set_le_add (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    {M : ℝ} (hM : ∀ i, (∑' z, rates.q i z) - ∑' z, rates'.q i z ≤ M)
    (n : ℕ) (i : S) (A : Set S) :
    (rates.kernel ^ n) i A ≤
      (rates'.kernel ^ n) i A + n * ENNReal.ofReal (M / rates.R) := by
  apply rates.kernel_pow_le_add_removed rates' hR hq _ A _ n i
  intro m x
  calc
    _ ≤ ∑' z, ENNReal.ofReal ((rates.q x z - rates'.q x z) / rates.R) := by
      apply ENNReal.tsum_le_tsum
      intro z
      exact mul_le_of_le_one_right bot_le (prob_le_one)
    _ ≤ ENNReal.ofReal (M / rates.R) := by
      rw [rates.tsum_removed rates' hq]
      exact ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hM x) rates.R_pos.le)

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
/-- Symmetric jump rates give a symmetric uniformized matrix. -/
theorem p_symm (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    (i j : S) : rates.p i j = rates.p j i := by
  classical
  by_cases h : i = j
  · subst j; rfl
  · simp only [p, if_neg h, if_neg (Ne.symm h), hs i j]

/-- Symmetry makes each column of every discrete power have mass one. -/
theorem tsum_kernel_pow_column (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (n : ℕ) (j : S) :
    (∑' i, (rates.kernel ^ n) i {j}) = 1 := by
  simp_rw [rates.kernel_pow_singleton,
    kernelPow_symm rates.p_nonneg rates.hasSum_p (rates.p_symm hs) n _ j]
  rw [← ENNReal.ofReal_tsum_of_nonneg (kernelPow_nonneg rates.p_nonneg n j)
    (kernelPow_summable rates.p_nonneg rates.hasSum_p n j),
    kernelPow_tsum rates.p_nonneg rates.hasSum_p, ENNReal.ofReal_one]

/-- A uniform bound on removed entries controls singleton masses of discrete powers. -/
theorem kernel_pow_singleton_le_add (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    (hs : ∀ i j, rates.q i j = rates.q j i)
    {b : ℝ} (hb : ∀ i j, rates.q i j - rates'.q i j ≤ b)
    (n : ℕ) (i j : S) :
    (rates.kernel ^ n) i {j} ≤
      (rates'.kernel ^ n) i {j} + n * ENNReal.ofReal (b / rates.R) := by
  apply rates.kernel_pow_le_add_removed rates' hR hq _ {j} _ n i
  intro m x
  calc
    _ ≤ ∑' z, ENNReal.ofReal (b / rates.R) * (rates.kernel ^ m) z {j} := by
      apply ENNReal.tsum_le_tsum
      intro z
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hb x z) rates.R_pos.le)) _
    _ = _ := by
      rw [ENNReal.tsum_mul_left, rates.tsum_kernel_pow_column hs, mul_one]

/-- Multiplication by the index shifts a Poisson weight by one. -/
theorem poisson_weight_succ_mul (x : ℝ) (n : ℕ) :
    (Real.exp (-x) * x ^ (n + 1) / (n + 1).factorial) * (n + 1 : ℕ) =
      x * (Real.exp (-x) * x ^ n / n.factorial) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [hn, hf]

/-- The first moment of the Poisson weights equals their parameter. -/
theorem tsum_poisson_weight_mul_index (x : ℝ) (hx : 0 ≤ x) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-x) * x ^ n / n.factorial) * n) =
      ENNReal.ofReal x := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have hterm (n : ℕ) :
      ENNReal.ofReal (Real.exp (-x) * x ^ (n + 1) / (n + 1).factorial) *
          (n + 1 : ℕ) =
        ENNReal.ofReal x * ENNReal.ofReal (Real.exp (-x) * x ^ n / n.factorial) := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (show
        0 ≤ Real.exp (-x) * x ^ (n + 1) / (n + 1).factorial by positivity),
      poisson_weight_succ_mul,
      ENNReal.ofReal_mul hx]
  simp_rw [hterm]
  have hsum : HasSum (fun n : ℕ => Real.exp (-x) * x ^ n / n.factorial) 1 :=
    hasSum_one_poissonMeasure (⟨x, hx⟩ : ℝ≥0)
  rw [ENNReal.tsum_mul_left,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,
    hsum.tsum_eq, ENNReal.ofReal_one, mul_one]

/-- Poisson averaging turns a linear discrete loss into intensity times elapsed time. -/
theorem transitionKernel_le_add_of_power_bound (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) {C : ℝ} (hC : 0 ≤ C) (A : Set S)
    (hpow : ∀ (n : ℕ) (i : S), (rates.kernel ^ n) i A ≤
      (rates'.kernel ^ n) i A + n * ENNReal.ofReal (C / rates.R))
    (t : ℝ≥0) (i : S) :
    rates.transitionKernel t i A ≤
      rates'.transitionKernel t i A + ENNReal.ofReal (C * t) := by
  have hA : MeasurableSet A := Set.to_countable A |>.measurableSet
  change poissonKernel rates.kernel _ i A ≤ poissonKernel rates'.kernel _ i A + _
  rw [poissonKernel_apply_eq_tsum _ _ _ hA, poissonKernel_apply_eq_tsum _ _ _ hA]
  change (∑' n : ℕ, ENNReal.ofReal
    (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
      (rates.kernel ^ n) i A) ≤ (∑' n : ℕ, ENNReal.ofReal
    (Real.exp (-(rates'.R * t)) * (rates'.R * t) ^ n / n.factorial) *
      (rates'.kernel ^ n) i A) + _
  rw [hR]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
          ((rates'.kernel ^ n) i A + n * ENNReal.ofReal (C / rates.R)) := by
      exact ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hpow n i) _
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
      rw [tsum_poisson_weight_mul_index _ (mul_nonneg rates.R_pos.le t.coe_nonneg),
        ← ENNReal.ofReal_mul' (div_nonneg hC rates.R_pos.le)]
      congr 2
      field_simp [rates.R_pos.ne']

/-- Removing at most `M` total intensity changes each set probability by at most `M * t`. -/
theorem transitionKernel_set_le_add (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, (∑' z, rates.q i z) - ∑' z, rates'.q i z ≤ M)
    (t : ℝ≥0) (i : S) (A : Set S) :
    rates.transitionKernel t i A ≤
      rates'.transitionKernel t i A + ENNReal.ofReal (M * t) := by
  exact rates.transitionKernel_le_add_of_power_bound rates' hR hM0 A
    (fun n i => rates.kernel_pow_set_le_add rates' hR hq hM n i A) t i

/-- For symmetric original rates, a removed-entry bound gives the additive heat-kernel bound. -/
theorem transitionKernel_singleton_le_add (rates rates' : BoundedRates S)
    (hR : rates'.R = rates.R) (hq : ∀ i j, rates'.q i j ≤ rates.q i j)
    (hs : ∀ i j, rates.q i j = rates.q j i)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ i j, rates.q i j - rates'.q i j ≤ b)
    (t : ℝ≥0) (i j : S) :
    rates.transitionKernel t i {j} ≤
      rates'.transitionKernel t i {j} + ENNReal.ofReal (b * t) := by
  exact rates.transitionKernel_le_add_of_power_bound rates' hR hb0 {j}
    (fun n i => rates.kernel_pow_singleton_le_add rates' hR hq hs hb n i j) t i

end

end LatticeProb.JumpChain.BoundedRates
