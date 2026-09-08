/-
The number of steps a coordinate schedule gives to a block of coordinates, and
the average of the inverse square root of that number.

The gradient estimates read off `LatticeProb.srwHeat_eq_schedRot` and
`LatticeProb.srwHeat_eq_sched` bound the total-variation distance, schedule by
schedule, by the one-dimensional gradient at the number of steps the schedule
gives to a block `B` of coordinates.  Averaging that bound over the `d^r`
schedules is the last step, and it is the statement that

    d^{-r} ∑_c (K_B(c) + 1)^{-1/2} ≤ √(d / (|B| (r+1))) ,

where `K_B(c)` counts the times at which `c` selects a coordinate in `B`.

Two elementary facts do it.  First, the generating function: since the schedule
is a function on `Fin r` with values in `Fin d`, the sum of `u^{K_B(c)}` over all
schedules is a product over the times of the same one-step sum, so it equals
`(|B| u + (d - |B|))^r`.  Second, `1/(k+1)` is the integral of `u^k` over the
unit interval, so the average of `1/(K_B+1)` is an integral of a polynomial,
computed exactly:

    d^{-r} ∑_c 1/(K_B(c)+1) = (d^{r+1} - (d - |B|)^{r+1}) / (|B| (r+1) d^r) ≤ d/(|B|(r+1)) .

Cauchy-Schwarz turns that into the bound on the inverse SQUARE ROOT, which is
what a one-dimensional gradient of size `K^{-1/2}` needs.  No large deviation
estimate for the block count is required, and no binomial coefficient appears.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- How many of the `r` steps of the schedule `c` select a coordinate in `B`. -/
def blockCnt {r : ℕ} (B : Finset (Fin d)) (c : Fin r → Fin d) : ℕ :=
  (Finset.univ.filter fun t => c t ∈ B).card

theorem sum_pow_blockCnt (B : Finset (Fin d)) (r : ℕ) (u : ℝ) :
    ∑ c : Fin r → Fin d, u ^ blockCnt B c
      = (∑ a : Fin d, if a ∈ B then u else 1) ^ r := by
  classical
  have h1 : ∀ c : Fin r → Fin d,
      u ^ blockCnt B c = ∏ t : Fin r, (if c t ∈ B then u else 1) := by
    intro c
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  rw [← Fintype.piFinset_univ (α := Fin r) (β := fun _ => Fin d),
    ← Finset.prod_univ_sum (fun _ : Fin r => (Finset.univ : Finset (Fin d)))
      (fun _ : Fin r => fun a : Fin d => if a ∈ B then u else 1),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sum_ite_mem (B : Finset (Fin d)) (u : ℝ) :
    ∑ a : Fin d, (if a ∈ B then u else 1) = (B.card : ℝ) * u + ((d : ℝ) - B.card) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have h1 : (Finset.univ.filter fun a : Fin d => a ∈ B) = B := by
    ext a; simp
  have h2 : (Finset.univ.filter fun a : Fin d => a ∉ B).card = d - B.card := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d)))
      (p := fun a => a ∈ B)
    rw [h1, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [h1, h2]
  have hle : B.card ≤ d := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ B)
  simp only [nsmul_eq_mul, mul_one]
  push_cast [Nat.cast_sub hle]
  ring


theorem integral_add_mul_pow (m b : ℝ) (hb : b ≠ 0) (r : ℕ) :
    (∫ u in (0:ℝ)..1, (m + b * u) ^ r)
      = ((m + b) ^ (r + 1) - m ^ (r + 1)) / (b * ((r : ℝ) + 1)) := by
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have h := intervalIntegral.integral_comp_add_mul (a := (0:ℝ)) (b := (1:ℝ)) (c := b)
    (fun x : ℝ => x ^ r) hb m
  rw [h, integral_pow]
  simp only [mul_zero, mul_one, add_zero, smul_eq_mul]
  field_simp

theorem sum_inv_succ_blockCnt (B : Finset (Fin d)) (hB : 0 < B.card) (r : ℕ) :
    ∑ c : Fin r → Fin d, (1 : ℝ) / (blockCnt B c + 1)
      = ((d : ℝ) ^ (r + 1) - ((d : ℝ) - B.card) ^ (r + 1)) / (B.card * ((r : ℝ) + 1)) := by
  classical
  have hbne : ((B.card : ℝ)) ≠ 0 := by positivity
  have hterm : ∀ c : Fin r → Fin d,
      (1 : ℝ) / (blockCnt B c + 1) = ∫ u in (0:ℝ)..1, u ^ blockCnt B c := by
    intro c
    rw [integral_pow]
    simp
  rw [Finset.sum_congr rfl fun c _ => hterm c]
  rw [← intervalIntegral.integral_finsetSum
    (fun c _ => (Continuous.intervalIntegrable (by fun_prop) 0 1))]
  have hint : ∀ u : ℝ, ∑ c : Fin r → Fin d, u ^ blockCnt B c
      = (((d : ℝ) - B.card) + (B.card : ℝ) * u) ^ r := by
    intro u
    rw [sum_pow_blockCnt, sum_ite_mem]
    ring_nf
  rw [intervalIntegral.integral_congr (g := fun u => (((d : ℝ) - B.card) + (B.card : ℝ) * u) ^ r)
    (fun u _ => hint u)]
  rw [integral_add_mul_pow _ _ hbne]
  ring_nf

theorem sum_inv_succ_blockCnt_le (B : Finset (Fin d)) (hB : 0 < B.card) (r : ℕ) :
    ∑ c : Fin r → Fin d, (1 : ℝ) / (blockCnt B c + 1)
      ≤ (d : ℝ) ^ (r + 1) / (B.card * ((r : ℝ) + 1)) := by
  rw [sum_inv_succ_blockCnt B hB r]
  have hle : B.card ≤ d := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ B)
  have hnn : (0 : ℝ) ≤ (d : ℝ) - B.card := by
    have : ((B.card : ℝ)) ≤ (d : ℝ) := by exact_mod_cast hle
    linarith
  have hpos : (0 : ℝ) < (B.card : ℝ) * ((r : ℝ) + 1) := by
    have : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
    positivity
  have h2 : (d : ℝ) ^ (r + 1) - ((d : ℝ) - B.card) ^ (r + 1) ≤ (d : ℝ) ^ (r + 1) := by
    have hp : (0 : ℝ) ≤ ((d : ℝ) - B.card) ^ (r + 1) := pow_nonneg hnn _
    linarith
  exact (div_le_div_iff_of_pos_right hpos).mpr h2


/-! ### The average of the inverse square root of the block count -/

theorem sum_le_sqrt_card_mul_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, (a i) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  have hnn : (0 : ℝ) ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hy : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * ∑ i, (a i) ^ 2 := by positivity
  exact (Real.le_sqrt hnn hy).mpr hcs

/-- **The binomial average.**  Averaged over the `d^r` schedules, the inverse
square root of one more than the number of steps the schedule gives to the block
`B` is at most `√(d / (|B| (r+1)))`.  The proof is Cauchy-Schwarz against the
exact average of `1/(K+1)`, which is computed by integrating `u^K` over the unit
interval. -/
theorem avg_inv_sqrt_succ_blockCnt_le (hd : 0 < d) (B : Finset (Fin d)) (hB : 0 < B.card)
    (r : ℕ) :
    (∑ c : Fin r → Fin d, 1 / Real.sqrt ((blockCnt B c : ℝ) + 1)) / (d : ℝ) ^ r
      ≤ Real.sqrt ((d : ℝ) / (B.card * ((r : ℝ) + 1))) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdr : (0 : ℝ) < (d : ℝ) ^ r := by positivity
  have hbR : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
  have hrR : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  set a : (Fin r → Fin d) → ℝ := fun c => 1 / Real.sqrt ((blockCnt B c : ℝ) + 1) with hadef
  have ha : ∀ c, 0 ≤ a c := fun c => by positivity
  have hsq : ∀ c, (a c) ^ 2 = 1 / ((blockCnt B c : ℝ) + 1) := by
    intro c
    have hx : (0 : ℝ) ≤ (blockCnt B c : ℝ) + 1 := by positivity
    rw [hadef]
    simp only [div_pow, one_pow, Real.sq_sqrt hx]
  have hcard : (Fintype.card (Fin r → Fin d) : ℝ) = (d : ℝ) ^ r := by
    simp
  have h1 := sum_le_sqrt_card_mul_sum_sq a ha
  rw [hcard, Finset.sum_congr rfl fun c _ => hsq c] at h1
  have h2 : ∑ c : Fin r → Fin d, (1 : ℝ) / ((blockCnt B c : ℝ) + 1)
      ≤ (d : ℝ) ^ (r + 1) / (B.card * ((r : ℝ) + 1)) := by
    have := sum_inv_succ_blockCnt_le B hB r
    simpa using this
  have h3 : (d : ℝ) ^ r * ∑ c : Fin r → Fin d, (1 : ℝ) / ((blockCnt B c : ℝ) + 1)
      ≤ ((d : ℝ) ^ r) ^ 2 * ((d : ℝ) / (B.card * ((r : ℝ) + 1))) := by
    have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt hdr)
    calc (d : ℝ) ^ r * ∑ c : Fin r → Fin d, (1 : ℝ) / ((blockCnt B c : ℝ) + 1)
        ≤ (d : ℝ) ^ r * ((d : ℝ) ^ (r + 1) / (B.card * ((r : ℝ) + 1))) := hmul
      _ = ((d : ℝ) ^ r) ^ 2 * ((d : ℝ) / (B.card * ((r : ℝ) + 1))) := by
          field_simp
          ring
  have h4 : ∑ c : Fin r → Fin d, a c
      ≤ Real.sqrt (((d : ℝ) ^ r) ^ 2 * ((d : ℝ) / (B.card * ((r : ℝ) + 1)))) :=
    h1.trans (Real.sqrt_le_sqrt h3)
  have h5 : Real.sqrt (((d : ℝ) ^ r) ^ 2 * ((d : ℝ) / (B.card * ((r : ℝ) + 1))))
      = (d : ℝ) ^ r * Real.sqrt ((d : ℝ) / (B.card * ((r : ℝ) + 1))) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hdr)]
  rw [h5] at h4
  rw [div_le_iff₀ hdr]
  linarith [h4]

end LatticeProb
