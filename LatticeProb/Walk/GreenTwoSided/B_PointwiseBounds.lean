import LatticeProb.Site
import LatticeProb.Graph.Zd
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Network.Killed
import LatticeProb.Network.KilledGreen
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.LocalCLTOne
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.ExitBox


/-!
# Pointwise heat-kernel bounds

Elementary real-analysis lemmas feeding the Gaussian heat-kernel bound `srwHeat_gaussian`,
culminating in the uniform off-diagonal bound `srwHeat d k w ≤ C / r ^ d` for `r ≤ graphNorm w`
and the on-diagonal bound `srwHeat d k w ≤ C * k ^ (-d/2)`, both uniform in the dimension `d ≥ 1`.
-/

open Finset
open scoped Classical

namespace LatticeProb

namespace GreenTwoSided

variable {d : ℕ}

-- y^{d/2} ≤ 1 + y^d for y ≥ 0: if y ≤ 1 then Real.rpow_le_one; else
-- Real.rpow_le_rpow_of_exponent_le (d/2 ≤ d) and Real.rpow_natCast.
/-- For `y ≥ 0`, the half-power `y ^ (d / 2)` is bounded by `1 + y ^ d`. -/
private theorem rpow_half_le_one_add_pow (y : ℝ) (hy : 0 ≤ y) : y ^ ((d : ℝ) / 2) ≤ 1 + y ^ d := by
  have hd : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  rcases le_total y 1 with hy1 | hy1
  · have h1 : y ^ ((d:ℝ)/2) ≤ 1 := Real.rpow_le_one hy hy1 (by linarith)
    have h2 : (0:ℝ) ≤ y ^ d := pow_nonneg hy d
    linarith
  · have h1 : y ^ ((d:ℝ)/2) ≤ y ^ (d:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : (0:ℝ) ≤ y ^ d := pow_nonneg hy d
    linarith


-- (1 + y^d) e^{-y} ≤ 1 + d!:  e^{-y} ≤ 1 (Real.exp_le_one_iff) and
-- y^d ≤ d! e^y (Real.pow_div_factorial_le_exp, div_le_iff₀), Real.exp_neg, mul_inv_cancel₀.
/-- For `y ≥ 0`, `(1 + y ^ d) * Real.exp (-y) ≤ 1 + d!`. -/
private theorem one_add_pow_mul_exp_neg_le (y : ℝ) (hy : 0 ≤ y) :
    (1 + y ^ d) * Real.exp (-y) ≤ 1 + (d.factorial : ℝ) := by
  nlinarith [mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos d))).mp
        (Real.pow_div_factorial_le_exp y hy d)) (Real.exp_nonneg (-y)),
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy),
    (by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] : Real.exp y * Real.exp (-y) = 1)]


-- With y := ρ²/(8u): u^{-d/2} = 8^{d/2} ρ^{-d} y^{d/2} (Real.rpow_neg, Real.div_rpow,
-- Real.rpow_natCast, Real.sqrt_eq_rpow ...), then rpow_half_le_one_add_pow,
-- one_add_pow_mul_exp_neg_le, 8^{d/2} ≤ 8^d.  SPLIT?
/-- A Gaussian-times-power bound: `u ^ (-d/2) * exp (-ρ²/(8u)) ≤ 8^d (1 + d!) / ρ^d` for `u, ρ >
0`. -/
private theorem rpow_neg_half_mul_exp_le_div_pow (u ρ : ℝ) (hu : 0 < u) (hρ : 0 < ρ) :
    u ^ (-(d : ℝ) / 2) * Real.exp (-ρ ^ 2 / (8 * u))
      ≤ 8 ^ d * (1 + (d.factorial : ℝ)) / ρ ^ d := by
  have hu_nn : (0 : ℝ) ≤ u := le_of_lt hu
  have hρ_nn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have h8nn : (0 : ℝ) ≤ 8 := (by norm_num)
  have hρd_pos : (0 : ℝ) < ρ ^ d := pow_pos hρ d
  have hρ2_nn : (0 : ℝ) ≤ ρ ^ 2 := (by positivity)
  have h3 : (ρ ^ 2) ^ ((d : ℝ) / 2) = ρ ^ d := (by
    rw [← Real.rpow_natCast ρ d, ← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ_nn]
    congr 1
    push_cast
    ring)
  rw [le_div_iff₀ hρd_pos]
  simp only [neg_div]
  set y : ℝ := ρ ^ 2 / (8 * u) with hydef
  have hy_nn : (0 : ℝ) ≤ y := (by rw [hydef]; positivity)
  have hu_pow_pos : (0 : ℝ) < u ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hu _
  have huy : 8 * u * y = ρ ^ 2 := (by
    rw [hydef]; field_simp)
  have h8y : 8 * y = ρ ^ 2 / u := (by
    rw [hydef]; field_simp)
  have hA : (8 : ℝ) ^ ((d : ℝ) / 2) * y ^ ((d : ℝ) / 2) = (8 * y) ^ ((d : ℝ) / 2) :=
    (Real.mul_rpow h8nn hy_nn).symm
  have hBC : (8 * y) ^ ((d : ℝ) / 2) = ρ ^ d / u ^ ((d : ℝ) / 2) := (
    by rw [h8y, Real.div_rpow hρ2_nn hu_nn, h3])
  have hAy : (8 : ℝ) ^ ((d : ℝ) / 2) * y ^ ((d : ℝ) / 2) = ρ ^ d / u ^ ((d : ℝ) / 2) := (
    by rw [hA, hBC])
  have hkey : u ^ (-((d : ℝ) / 2)) * ρ ^ d = (8 : ℝ) ^ ((d : ℝ) / 2) * y ^ ((d : ℝ) / 2) := (
    by rw [Real.rpow_neg hu_nn, hAy, inv_mul_eq_div])
  have hL : u ^ (-((d : ℝ) / 2)) * Real.exp (-y) * ρ ^ d
      = (8 : ℝ) ^ ((d : ℝ) / 2) * (y ^ ((d : ℝ) / 2) * Real.exp (-y)) := (
    by rw [mul_assoc, mul_comm (Real.exp (-y)) (ρ ^ d), ← mul_assoc, hkey, mul_assoc])
  rw [hL]
  have hg : y ^ ((d : ℝ) / 2) * Real.exp (-y) ≤ 1 + (d.factorial : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (rpow_half_le_one_add_pow y hy_nn) (Real.exp_nonneg _))
      (one_add_pow_mul_exp_neg_le y hy_nn)
  have hd2 : (d : ℝ) / 2 ≤ (d : ℝ) := (by
    have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith)
  have h8le : (8 : ℝ) ^ ((d : ℝ) / 2) ≤ (8 : ℝ) ^ d :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hd2)
      (le_of_eq (Real.rpow_natCast 8 d))
  refine le_trans (mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg h8nn _)) ?_
  exact mul_le_mul_of_nonneg_right h8le (by positivity)


-- k + 2d ≤ (1 + 2d) k for k ≥ 1; Real.rpow_le_rpow on exponent d/2, then Real.rpow_neg /
-- inv_le_inv₀; Real.mul_rpow.
/-- For `k ≥ 1`, `k ^ (-d/2) ≤ (1 + 2d) ^ (d/2) * (k + 2d) ^ (-d/2)`, absorbing an additive shift
of `2d` at the cost of a constant. -/
private theorem rpow_neg_half_le_rpow_neg_half_add (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ (-(d : ℝ) / 2)
      ≤ (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) * ((k : ℝ) + 2 * d) ^ (-(d : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := (by exact_mod_cast hk)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hu : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1
  have hv : (0 : ℝ) < (k : ℝ) + 2 * (d : ℝ) := (by positivity)
  have hA : (0 : ℝ) < 1 + 2 * (d : ℝ) := (by positivity)
  have hD : (0 : ℝ) ≤ (d : ℝ) / 2 := (by positivity)
  have hD2 : -(d : ℝ) / 2 = -((d : ℝ) / 2) := (by ring)
  have hvv : (k : ℝ) + 2 * (d : ℝ) ≤ (1 + 2 * (d : ℝ)) * (k : ℝ) :=
    (by nlinarith [hd0, hk1, mul_nonneg hd0 (sub_nonneg.mpr hk1)])
  have hstep : ((k : ℝ) + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
      ≤ (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) * (k : ℝ) ^ ((d : ℝ) / 2) :=
    Real.mul_rpow hA.le hu.le ▸ Real.rpow_le_rpow hv.le hvv hD
  have hL : ((k : ℝ) ^ ((d : ℝ) / 2))⁻¹ = 1 / ((k : ℝ) ^ ((d : ℝ) / 2)) :=
    inv_eq_one_div _
  have hR : (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) * (((k : ℝ) + 2 * (d : ℝ)) ^ ((d : ℝ) / 2))⁻¹
      = (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) / ((k : ℝ) + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) :=
    (div_eq_mul_inv _ _).symm
  rw [hD2]
  rw [Real.rpow_neg hu.le ((d : ℝ) / 2), Real.rpow_neg hv.le ((d : ℝ) / 2)]
  rw [hL, hR, div_le_div_iff₀ (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)]
  simp only [one_mul]
  exact hstep


-- Uniform off-diagonal bound.  C := 3^d greenConst d (1+2d)^{d/2} 8^d (1+d!) + 1.
-- k = 0: srwHeat_zero, w ≠ 0 since graphNorm w ≥ 1 (graphNorm_eq_zero_iff).
-- k ≥ 1: srwHeat_gaussian hd, rpow_neg_half_le_rpow_neg_half_add, rpow_neg_half_mul_exp_le_div_pow
-- (u = k + 2d, ρ = graphNorm w),
-- then 1/(graphNorm w)^d ≤ 1/r^d (pow_le_pow_left₀, one_div_le_one_div_of_le).  SPLIT?
/-- Implementation lemma for `srwHeat_le_div_pow_of_le_graphNorm`: produces the uniform
off-diagonal Gaussian bound `srwHeat d k w ≤ C / r ^ d` whenever `1 ≤ r ≤ graphNorm w`. -/
private theorem srwHeat_le_div_pow_of_le_graphNorm' (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w →
      srwHeat d k w ≤ C / (r : ℝ) ^ d := by
  have hd0 : 0 < d := hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hA : (0 : ℝ) ≤ 1 + 2 * (d : ℝ) := by positivity
  have hB : (0 : ℝ) ≤ (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2) := Real.rpow_nonneg hA _
  have hAB : (0 : ℝ) ≤ 3 ^ d * greenConst d :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) d) (greenConst_nonneg d)
  have hM : (0 : ℝ) ≤ 8 ^ d * (1 + (d.factorial : ℝ)) :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) d) (by positivity)
  have hABM : (0 : ℝ) ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
      * (8 ^ d * (1 + (d.factorial : ℝ))) := mul_nonneg (mul_nonneg hAB hB) hM
  have hCpos : 0 < 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
      * (8 ^ d * (1 + (d.factorial : ℝ))) + 1 :=
    lt_of_le_of_lt hABM (lt_add_one _)
  refine ⟨_, hCpos, ?_⟩
  intro k w r hr1 hrw
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
  have hRpos : (0 : ℝ) < (r : ℝ) ^ d := pow_pos hrpos d
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [srwHeat_zero]
    by_cases hw : w = 0
    · subst hw
      rw [graphNorm_zero] at hrw
      exfalso
      omega
    · rw [if_neg hw]
      exact div_nonneg (by linarith) (le_of_lt hRpos)
  · have hk1 : 1 ≤ k := hk
    have h11 := rpow_neg_half_le_rpow_neg_half_add (d := d) k hk1
    have hg := srwHeat_gaussian (d := d) hd0 hk1 w
    have hu0 : (0 : ℝ) < (k : ℝ) + 2 * (d : ℝ) :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by linarith)
    have hwpos : (0 : ℝ) < (graphNorm w : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans hr1 hrw))
    have hrw' : (r : ℝ) ≤ (graphNorm w : ℝ) := by exact_mod_cast hrw
    have hpow : (r : ℝ) ^ d ≤ (graphNorm w : ℝ) ^ d :=
      pow_le_pow_left₀ (le_of_lt hrpos) hrw' d
    have h10 := rpow_neg_half_mul_exp_le_div_pow (d := d) ((k : ℝ) + 2 * (d : ℝ)) (graphNorm w : ℝ)
        hu0 hwpos
    have hMle : 8 ^ d * (1 + (d.factorial : ℝ)) / (graphNorm w : ℝ) ^ d
        ≤ 8 ^ d * (1 + (d.factorial : ℝ)) / (r : ℝ) ^ d :=
      div_le_div_of_nonneg_left hM hRpos hpow
    have hkey : srwHeat d k w
        ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
          * (8 ^ d * (1 + (d.factorial : ℝ))) / (r : ℝ) ^ d := by
      have hstep3 : Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
            * (k : ℝ) ^ (-((d : ℝ)) / 2)
          ≤ Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
            * ((1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * ((k : ℝ) + 2 * (d : ℝ)) ^ (-((d : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_left h11 (Real.exp_nonneg _)
      calc srwHeat d k w
          ≤ 3 ^ d * greenConst d * (k : ℝ) ^ (-((d : ℝ)) / 2)
            * Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ)))) := hg
        _ = 3 ^ d * greenConst d *
            (Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
              * (k : ℝ) ^ (-((d : ℝ)) / 2)) := by ring
        _ ≤ 3 ^ d * greenConst d *
            (Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))
              * ((1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
                * ((k : ℝ) + 2 * (d : ℝ)) ^ (-((d : ℝ)) / 2))) :=
              mul_le_mul_of_nonneg_left hstep3 hAB
        _ = 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (((k : ℝ) + 2 * (d : ℝ)) ^ (-((d : ℝ)) / 2)
                * Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ))))) := by ring
        _ ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (8 ^ d * (1 + (d.factorial : ℝ)) / (graphNorm w : ℝ) ^ d) :=
              mul_le_mul_of_nonneg_left h10 (mul_nonneg hAB hB)
        _ ≤ 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (8 ^ d * (1 + (d.factorial : ℝ)) / (r : ℝ) ^ d) :=
              mul_le_mul_of_nonneg_left hMle (mul_nonneg hAB hB)
        _ = 3 ^ d * greenConst d * (1 + 2 * (d : ℝ)) ^ ((d : ℝ) / 2)
              * (8 ^ d * (1 + (d.factorial : ℝ))) / (r : ℝ) ^ d := by ring
    rw [add_div]
    have hone : (0 : ℝ) ≤ 1 / (r : ℝ) ^ d := by positivity
    linarith

/-- The uniform off-diagonal Gaussian heat-kernel bound: there is `C > 0` with `srwHeat d k w ≤ C
/ r ^ d` for all `k`, whenever `1 ≤ r ≤ graphNorm w`. -/
theorem srwHeat_le_div_pow_of_le_graphNorm (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (w : Site d) (r : ℕ), 1 ≤ r → r ≤ graphNorm w →
      srwHeat d k w ≤ C / (r : ℝ) ^ d := by
  exact srwHeat_le_div_pow_of_le_graphNorm' hd


-- On-diagonal: srwHeat_gaussian with Real.exp_le_one_iff (the exponent is ≤ 0);
-- C := 3^d greenConst d + 1 (greenConst_nonneg).
/-- The on-diagonal Gaussian heat-kernel bound: there is `C > 0` with `srwHeat d k w ≤ C * k ^
(-d/2)` for all `k ≥ 1` and all `w`. -/
theorem srwHeat_le_mul_rpow_neg_half (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ w : Site d,
      srwHeat d k w ≤ C * (k : ℝ) ^ (-(d : ℝ) / 2) := by
  have hd0 : 0 < d := hd
  have hA : (0 : ℝ) ≤ 3 ^ d * greenConst d := mul_nonneg (pow_nonneg (by
    norm_num : (0:ℝ) ≤ 3) d) (greenConst_nonneg d)
  refine ⟨3 ^ d * greenConst d + 1, by linarith, ?_⟩
  intro k hk w
  have hpow : (0 : ℝ) ≤ (k : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hg := srwHeat_gaussian (d := d) hd0 hk w
  have hexp : Real.exp (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by
    positivity))
  have hstep : 3 ^ d * greenConst d * (k : ℝ) ^ (-(d : ℝ) / 2) * Real.exp
      (-(graphNorm w : ℝ) ^ 2 / (8 * ((k : ℝ) + 2 * (d : ℝ)))) ≤ 3 ^ d * greenConst d * (k : ℝ) ^
          (-(d : ℝ) / 2) := (by
    have h := mul_le_mul_of_nonneg_left hexp (mul_nonneg hA hpow)
    simpa using h)
  have hfin : 3 ^ d * greenConst d * (k : ℝ) ^ (-(d : ℝ) / 2) ≤ (3 ^ d * greenConst d + 1) * (k : ℝ)
      ^ (-(d : ℝ) / 2) := (by
    nlinarith [hpow])
  exact le_trans (le_trans hg hstep) hfin

end GreenTwoSided

end LatticeProb
