import LatticeProb.Prob.BrownianParentBlockDyadicClockBound

/-!
# Scale-independent dyadic clock parameters

An enlargement and a clock cutoff can be chosen independently of the scale.
-/

set_option autoImplicit false

open scoped NNReal

namespace BouRabeeGwynne

/-- The ratio estimate and its clock cutoff can be made uniform over positive scales. -/
theorem exists_uniform_dyadic_clock_parameters (C : ℝ) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ≥0, 3 ≤ R ∧ ∃ K : ℕ, ∀ S : ℝ≥0, 0 < S →
      ⌊((((2 * S / (2 : ℝ≥0) ^ n) / (18 * (R * S)) : ℝ≥0) : ℝ) ^
        (-(2 + (1 / 2 : ℝ))))⌋₊ ≤ K + 1 ∧
      C * (((2 * S / (2 : ℝ≥0) ^ n) / (18 * (R * S)) : ℝ≥0) : ℝ) ≤ ε := by
  let A : ℝ := max C 1
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right C 1)
  let R : ℝ≥0 := ⟨3 + A / ε, by positivity⟩
  have hR : (3 : ℝ) ≤ R := by
    change 3 ≤ 3 + A / ε
    have : 0 ≤ A / ε := by positivity
    linarith
  have hRp : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR
  let q : ℝ := 2 / (18 * (R : ℝ) * (2 : ℝ) ^ n)
  let K : ℕ := ⌊q ^ (-(2 + (1 / 2 : ℝ)))⌋₊
  refine ⟨R, ?_, K, ?_⟩
  · exact_mod_cast hR
  · intro S hS
    have hS' : (0 : ℝ) < S := by exact_mod_cast hS
    have hratio : (((2 * S / (2 : ℝ≥0) ^ n) / (18 * (R * S)) : ℝ≥0) : ℝ) = q := by
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
      dsimp [q]
      field_simp
    rw [hratio]
    constructor
    · exact Nat.le_succ K
    · have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      have hq : q ≤ 1 / (R : ℝ) := by
        dsimp [q]
        apply (div_le_div_iff₀ (by positivity) hRp).2
        nlinarith
      have hAR : A / (R : ℝ) < ε := by
        apply (div_lt_iff₀ hRp).2
        change A < ε * (3 + A / ε)
        have he : ε * (A / ε) = A := by field_simp
        nlinarith
      calc
        C * q ≤ A * q := mul_le_mul_of_nonneg_right (le_max_left C 1) hq0
        _ ≤ A * (1 / (R : ℝ)) := mul_le_mul_of_nonneg_left hq hA.le
        _ = A / (R : ℝ) := by ring
        _ ≤ ε := hAR.le

end BouRabeeGwynne
