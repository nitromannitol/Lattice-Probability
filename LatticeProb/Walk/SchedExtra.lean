/-
A sharper schedule average, with one coordinate weighted twice.

`GreenBounds.lean` bounds the schedule average of `∏_i (N_i+1)^{-1/2}` by
`C R^{-d/2}`.  Inserting one extra factor `(N_{i₀}+1)^{-1/2}` turns the `d`
factors into `d + 1`, and the same Chernoff split then gives `C R^{-(d+1)/2}`.
The bulk and tail estimates are restated here with an arbitrary natural
exponent `p` in place of `d`, so that they can be applied at `p = d + 1`.
-/
import Mathlib
import LatticeProb.Walk.SRWGauss

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### Bulk and tail with an arbitrary exponent -/

/-- The bulk term with an arbitrary natural exponent `p` in place of `d`. -/
lemma bulk_le_pow (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (p : ℕ) :
    ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ p
      ≤ (Real.sqrt (4 * (d : ℝ))) ^ p * ((Real.sqrt (R : ℝ)) ^ p)⁻¹ := by
  have hmod : R < 4 * d * (R / (4 * d) + 1) := by
    have h2 : 0 < 4 * d := by omega
    calc R = 4 * d * (R / (4 * d)) + R % (4 * d) := (Nat.div_add_mod R (4 * d)).symm
      _ < 4 * d * (R / (4 * d)) + 4 * d := by have := Nat.mod_lt R h2; omega
      _ = 4 * d * (R / (4 * d) + 1) := by ring
  set a : ℕ := R / (4 * d) with ha
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hRle : (R : ℝ) / (4 * (d : ℝ)) ≤ (a : ℝ) + 2 := by
    have : (R : ℝ) ≤ 4 * (d : ℝ) * ((a : ℝ) + 2) := by
      have : (R : ℝ) < 4 * (d : ℝ) * ((a : ℝ) + 1) := by exact_mod_cast hmod
      nlinarith [hdR]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsq : Real.sqrt ((R : ℝ) / (4 * (d : ℝ))) ≤ Real.sqrt ((a : ℝ) + 2) :=
    Real.sqrt_le_sqrt hRle
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hsqpos : (0 : ℝ) < Real.sqrt ((R : ℝ) / (4 * (d : ℝ))) :=
    Real.sqrt_pos.mpr (by positivity)
  have hinv : (Real.sqrt ((a : ℝ) + 2))⁻¹
      ≤ Real.sqrt (4 * (d : ℝ)) / Real.sqrt (R : ℝ) := by
    have := inv_le_inv₀ (lt_of_lt_of_le hsqpos hsq) hsqpos |>.mpr hsq
    rw [Real.sqrt_div (le_of_lt hRpos)] at this
    rwa [inv_div] at this
  have hnn : (0 : ℝ) ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ := by positivity
  calc ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ p
      ≤ (Real.sqrt (4 * (d : ℝ)) / Real.sqrt (R : ℝ)) ^ p := pow_le_pow_left₀ hnn hinv p
    _ = (Real.sqrt (4 * (d : ℝ))) ^ p * ((Real.sqrt (R : ℝ)) ^ p)⁻¹ := by
        rw [div_pow, div_eq_mul_inv]

/-- The tail term with an arbitrary natural exponent `p` in place of `d`. -/
lemma tail_le_pow (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (p : ℕ) :
    (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))
      ≤ (d : ℝ) * (Nat.factorial p : ℝ) * (4 * (d : ℝ)) ^ p * ((Real.sqrt (R : ℝ)) ^ p)⁻¹ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  set s : ℝ := (R : ℝ) / (4 * (d : ℝ)) with hs
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hterm : s ^ p / (Nat.factorial p : ℝ) ≤ Real.exp s := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (le_of_lt hspos) (p + 1))
    refine Finset.single_le_sum (f := fun i => s ^ i / (Nat.factorial i : ℝ)) ?_ ?_
    · intro i _
      positivity
    · simp
  have hpos : (0 : ℝ) < s ^ p / (Nat.factorial p : ℝ) := by positivity
  have hexp : Real.exp (-s) ≤ (Nat.factorial p : ℝ) / s ^ p := by
    rw [Real.exp_neg]
    have h := (inv_le_inv₀ (lt_of_lt_of_le hpos hterm) hpos).mpr hterm
    rwa [inv_div] at h
  have hsd : s ^ p = (R : ℝ) ^ p / (4 * (d : ℝ)) ^ p := by rw [hs, div_pow]
  have hfac : (Nat.factorial p : ℝ) / s ^ p
      = (Nat.factorial p : ℝ) * (4 * (d : ℝ)) ^ p / (R : ℝ) ^ p := by
    rw [hsd]
    field_simp
  have hsr : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
    have h1 : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (R : ℝ) ≤ Real.sqrt ((R : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (R : ℝ) := Real.sqrt_sq (le_of_lt hRpos)
  have hge : (Real.sqrt (R : ℝ)) ^ p ≤ (R : ℝ) ^ p :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr p
  have hinvle : ((R : ℝ) ^ p)⁻¹ ≤ ((Real.sqrt (R : ℝ)) ^ p)⁻¹ := by
    have h1 : (0 : ℝ) < (Real.sqrt (R : ℝ)) ^ p := by
      have : (0 : ℝ) < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr hRpos
      positivity
    exact inv_le_inv₀ (lt_of_lt_of_le h1 hge) h1 |>.mpr hge
  have hcpos : (0 : ℝ) ≤ (d : ℝ) * (Nat.factorial p : ℝ) * (4 * (d : ℝ)) ^ p := by positivity
  rw [show -(R : ℝ) / (4 * (d : ℝ)) = -s from by rw [hs]; ring]
  calc (d : ℝ) * Real.exp (-s)
      ≤ (d : ℝ) * ((Nat.factorial p : ℝ) * (4 * (d : ℝ)) ^ p / (R : ℝ) ^ p) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hexp (le_of_lt hdR)
    _ = ((d : ℝ) * (Nat.factorial p : ℝ) * (4 * (d : ℝ)) ^ p) * ((R : ℝ) ^ p)⁻¹ := by
        field_simp
    _ ≤ ((d : ℝ) * (Nat.factorial p : ℝ) * (4 * (d : ℝ)) ^ p) * ((Real.sqrt (R : ℝ)) ^ p)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvle hcpos

/-! ### The product with one extra factor -/

/-- Either some coordinate is updated at most `a` times, or each of the `d + 1`
factors of the weighted product is at most `(a+2)^{-1/2}`. -/
lemma sched_prod_extra_bound {r : ℕ} (c : Fin r → Fin d) (i₀ : Fin d) (a : ℕ) :
    ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1)) * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1)
        + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
  by_cases hex : ∃ i : Fin d, cnt c i ≤ a
  · obtain ⟨j, hj⟩ := hex
    have hone : (1 : ℝ) ≤ ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
      calc (1 : ℝ) = (if cnt c j ≤ a then (1 : ℝ) else 0) := by rw [if_pos hj]
        _ ≤ _ := Finset.single_le_sum (f := fun i => (if cnt c i ≤ a then (1 : ℝ) else 0))
              (fun i _ => by split <;> norm_num) (Finset.mem_univ j)
    have hprod : ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ 1 := by
      calc ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ ∏ _i : Fin d, (1 : ℝ) :=
            Finset.prod_le_prod (fun i _ => one_div_sqrt_cnt_nonneg c i)
              (fun i _ => one_div_sqrt_cnt_le_one c i)
        _ = 1 := by simp
    have hprodnn : (0 : ℝ) ≤ ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) :=
      Finset.prod_nonneg fun i _ => one_div_sqrt_cnt_nonneg c i
    have hleft : ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
        * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ 1 := by
      calc ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
            * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ 1 * 1 :=
            mul_le_mul (one_div_sqrt_cnt_le_one c i₀) hprod hprodnn (by norm_num)
        _ = 1 := by norm_num
    have : (0 : ℝ) ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1) := by positivity
    linarith
  · push Not at hex
    have hfac : ∀ i : Fin d,
        (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ := by
      intro i
      have ha : (a : ℝ) + 2 ≤ (cnt c i : ℝ) + 1 := by
        have : a + 1 ≤ cnt c i := hex i
        have : ((a : ℝ) + 1) ≤ (cnt c i : ℝ) := by exact_mod_cast this
        linarith
      have hpos : (0 : ℝ) < Real.sqrt ((a : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
      rw [one_div, inv_le_inv₀ (by positivity) hpos]
      exact Real.sqrt_le_sqrt ha
    have hsum : (0 : ℝ) ≤ ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun i _ => by split <;> norm_num
    have hprod : ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by
      calc ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ ∏ _i : Fin d, (Real.sqrt ((a : ℝ) + 2))⁻¹ :=
            Finset.prod_le_prod (fun i _ => one_div_sqrt_cnt_nonneg c i) (fun i _ => hfac i)
        _ = ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by simp
    have hprodnn : (0 : ℝ) ≤ ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) :=
      Finset.prod_nonneg fun i _ => one_div_sqrt_cnt_nonneg c i
    have hleft : ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
        * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1) := by
      calc ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
            * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ * ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d :=
            mul_le_mul (hfac i₀) hprod hprodnn (by positivity)
        _ = ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1) := by
            rw [pow_succ]
            ring
    linarith

/-! ### The sharper schedule average -/

/-- The Chernoff step for the weighted product: the schedule sum splits into a
bulk term with exponent `d + 1` and `d` tail terms. -/
lemma sched_sum_extra_bound (hd : 0 < d) (R : ℕ) (i₀ : Fin d) :
    ∑ c : Fin R → Fin d, (((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
        * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1))
      ≤ (d : ℝ) ^ R * ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ (d + 1)
        + (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
  classical
  set a : ℕ := R / (4 * d) with ha
  have step1 : ∑ c : Fin R → Fin d, (((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
        * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1))
      ≤ ∑ c : Fin R → Fin d, (((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1)
          + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum fun c _ => sched_prod_extra_bound c i₀ a
  have step2 : ∑ c : Fin R → Fin d, (((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1)
        + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0))
      = (d : ℝ) ^ R * ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ (d + 1)
        + ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_sched, Finset.sum_comm]
  have step3 : ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
      ≤ (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
    calc ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin d, ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) :=
          Finset.sum_le_sum fun i _ => sum_indicator_cnt_le hd R i
      _ = (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [step1, step2.le, step3]

/-- The constant in the sharper schedule-average bound. -/
noncomputable def gradConst (d : ℕ) : ℝ :=
  (Real.sqrt (4 * (d : ℝ))) ^ (d + 1)
    + (d : ℝ) * (Nat.factorial (d + 1) : ℝ) * (4 * (d : ℝ)) ^ (d + 1)

/-- Confirms the constant of the sharper bound is nonnegative. -/
lemma gradConst_nonneg (d : ℕ) : 0 ≤ gradConst d := by
  unfold gradConst
  have h1 : (0 : ℝ) ≤ (Real.sqrt (4 * (d : ℝ))) ^ (d + 1) := by positivity
  have h2 : (0 : ℝ) ≤ (d : ℝ) * (Nat.factorial (d + 1) : ℝ) * (4 * (d : ℝ)) ^ (d + 1) := by
    positivity
  linarith

/-- The schedule average of `∏_i (N_i+1)^{-1/2}` with one extra factor
`(N_{i₀}+1)^{-1/2}` is `O(R^{-(d+1)/2})`. -/
theorem sched_avg_extra_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (i₀ : Fin d) :
    (∑ c : Fin R → Fin d,
        ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
          * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ R
      ≤ gradConst d * (R : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdRpow : (0 : ℝ) < (d : ℝ) ^ R := by positivity
  have h2 := sched_sum_extra_bound (d := d) hd R i₀
  have h3 : (∑ c : Fin R → Fin d, ((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
        * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ R
      ≤ ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ (d + 1)
        + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ))) := by
    rw [div_le_iff₀ hdRpow]
    calc ∑ c : Fin R → Fin d, (((1 : ℝ) / Real.sqrt ((cnt c i₀ : ℝ) + 1))
          * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1))
        ≤ _ := h2
      _ = (((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ (d + 1)
            + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) * (d : ℝ) ^ R := by ring
  have hexp : (R : ℝ) ^ (-((d : ℝ) + 1) / 2) = ((Real.sqrt (R : ℝ)) ^ (d + 1))⁻¹ := by
    have h := rpow_neg_half_eq (d + 1) R
    push_cast at h
    exact h
  rw [hexp, gradConst, add_mul]
  linarith [h3, bulk_le_pow (d := d) hd hR (d + 1), tail_le_pow (d := d) hd hR (d + 1)]

end LatticeProb
