/-
A discrete gradient bound for the one-dimensional lazy walk kernel `P1`.

Writing `p_m(k) = 4^{-m} binom(2m, m+k)`, the Pascal recurrence gives, for
`0 ≤ k ≤ m`, the exact difference

  `p_m(k) - p_m(k+1) = p_m(k) (2k+1) / (m+k+1)`,

which is nonnegative.  Feeding in the Gaussian bound
`p_m(k) ≤ (m+1)^{-1/2} exp(-k^2 / (2(m+1)))` and splitting the exponential into
two halves, the factor `(2k+1)/((m+1)^{1/2})` is absorbed by one half through
the elementary inequality `2 w^{1/2} e^{-w} ≤ 2`, leaving

  `|p_m(k) - p_m(k+1)| ≤ 5 (m+1)^{-1} exp(-k^2 / (4(m+1)))`.

Reflecting to the negative half shifts the site by one, which costs a factor
`e^{1/4}` once the Gaussian rate is relaxed from `4(m+1)` to `8(m+1)`, and
`5 e^{1/4} ≤ 8`.
-/
import Mathlib
import LatticeProb.Walk.OneDimGauss

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

/-- The elementary sup bound behind the gradient estimate: a square root is
dominated by an exponential, so `2 w^{1/2} e^{-w}` never exceeds `2`. -/
lemma two_sqrt_mul_exp_neg_le (w : ℝ) (hw : 0 ≤ w) :
    2 * Real.sqrt w * Real.exp (-w) ≤ 2 := by
  have h1 : Real.sqrt w ≤ 1 + w := by
    have h := Real.sqrt_le_sqrt (show w ≤ (1 + w) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have h2 : 1 + w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
  have h3 : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : (0 : ℝ) < Real.exp (-w) := Real.exp_pos _
  have h5 : Real.sqrt w * Real.exp (-w) ≤ Real.exp w * Real.exp (-w) :=
    mul_le_mul_of_nonneg_right (h1.trans h2) h4.le
  rw [h3] at h5
  linarith

/-- The sup bound in the scaled form used for the kernel: the linear factor
produced by the Pascal recurrence is absorbed by half of the Gaussian. -/
lemma div_sqrt_mul_exp_le (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x / Real.sqrt ((m : ℝ) + 1) * Real.exp (-(x ^ 2) / (4 * ((m : ℝ) + 1))) ≤ 2 := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hM
  have hsne : Real.sqrt ((m : ℝ) + 1) ≠ 0 := ne_of_gt hs
  have hs2 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt hM.le
  have hw : (0 : ℝ) ≤ x ^ 2 / (4 * ((m : ℝ) + 1)) := by positivity
  have he : x ^ 2 / (4 * ((m : ℝ) + 1)) = (x / (2 * Real.sqrt ((m : ℝ) + 1))) ^ 2 := by
    rw [div_pow, mul_pow, hs2]; norm_num
  have hsq : Real.sqrt (x ^ 2 / (4 * ((m : ℝ) + 1))) = x / (2 * Real.sqrt ((m : ℝ) + 1)) := by
    rw [he, Real.sqrt_sq (by positivity)]
  have hb := two_sqrt_mul_exp_neg_le _ hw
  rw [hsq] at hb
  have h2x : (2 : ℝ) * (x / (2 * Real.sqrt ((m : ℝ) + 1))) = x / Real.sqrt ((m : ℝ) + 1) := by
    field_simp
  rw [h2x] at hb
  rw [neg_div]
  exact hb

/-- The gradient bound at nonnegative integer sites, with the Gaussian rate
`4(m+1)` produced by splitting the rate `2(m+1)` of the kernel estimate. -/
lemma P1_gradient_nat (m k : ℕ) :
    |P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)|
      ≤ 5 / ((m : ℝ) + 1) * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hMne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hM
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hs : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hM
  have hsne : Real.sqrt ((m : ℝ) + 1) ≠ 0 := ne_of_gt hs
  have hE0 : (0 : ℝ) ≤ Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := Real.exp_nonneg _
  by_cases hk : k ≤ m
  · have hanti : P1 m ((k : ℤ) + 1) ≤ P1 m (k : ℤ) := P1_antitone m (by omega)
    have habs : |P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)| = P1 m (k : ℤ) - P1 m ((k : ℤ) + 1) :=
      abs_of_nonneg (by linarith)
    have hpas := P1_pascal_ratio m k hk
    have hdiff : (P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)) * ((m : ℝ) + (k : ℝ) + 1)
        = P1 m (k : ℤ) * (2 * (k : ℝ) + 1) := by linear_combination -hpas
    have hP1k : P1 m (k : ℤ)
        ≤ 1 / Real.sqrt ((m : ℝ) + 1) * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) :=
      (P1_gaussian_natCast m k).trans
        (mul_le_mul_of_nonneg_right (P1_zero_le_inv_sqrt m) (Real.exp_nonneg _))
    have hsplit : Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))
        = Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
          * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
      have hadd : -((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))
          = -((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)) + -((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)) := by
        field_simp
        ring
      rw [hadd, Real.exp_add]
    rw [hsplit] at hP1k
    have hE1 : Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) ≤ 1 := by
      have h0 : -((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)) ≤ 0 := by
        have hpos : (0 : ℝ) ≤ (k : ℝ) ^ 2 / (4 * ((m : ℝ) + 1)) := by positivity
        rw [neg_div]; linarith
      have h := Real.exp_le_exp.mpr h0
      rwa [Real.exp_zero] at h
    have hbrk : (2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)
        * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) ≤ 5 := by
      have h1 : (k : ℝ) / Real.sqrt ((m : ℝ) + 1)
          * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) ≤ 2 :=
        div_sqrt_mul_exp_le m (k : ℝ) hk0
      have hs1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
        have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (m : ℝ) + 1 by linarith)
        rwa [Real.sqrt_one] at h
      have hinv : (1 : ℝ) / Real.sqrt ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hs]; exact hs1
      have hB : 1 / Real.sqrt ((m : ℝ) + 1)
          * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) ≤ 1 := by
        nlinarith
      have hid : (2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)
          * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
          = 2 * ((k : ℝ) / Real.sqrt ((m : ℝ) + 1)
              * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))))
            + 1 / Real.sqrt ((m : ℝ) + 1)
              * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
        field_simp
      rw [hid]
      linarith
    have hkey : (P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)) * ((m : ℝ) + 1)
        ≤ 5 * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
      have hD0 : 0 ≤ P1 m (k : ℤ) - P1 m ((k : ℤ) + 1) := by linarith
      have hstep1 : (P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)) * ((m : ℝ) + 1)
          ≤ (P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)) * ((m : ℝ) + (k : ℝ) + 1) := by
        nlinarith
      have hstep2 : P1 m (k : ℤ) * (2 * (k : ℝ) + 1)
          ≤ (1 / Real.sqrt ((m : ℝ) + 1)
              * (Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
                * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))))) * (2 * (k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hP1k (by linarith)
      have hstep3 : (1 / Real.sqrt ((m : ℝ) + 1)
              * (Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
                * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))))) * (2 * (k : ℝ) + 1)
          = ((2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)
              * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))))
            * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
        field_simp
      have hstep4 : ((2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)
              * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))))
            * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
          ≤ 5 * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hbrk hE0
      calc (P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)) * ((m : ℝ) + 1)
          ≤ (P1 m (k : ℤ) - P1 m ((k : ℤ) + 1)) * ((m : ℝ) + (k : ℝ) + 1) := hstep1
        _ = P1 m (k : ℤ) * (2 * (k : ℝ) + 1) := hdiff
        _ ≤ _ := hstep2
        _ = _ := hstep3
        _ ≤ _ := hstep4
    rw [habs, show (5 : ℝ) / ((m : ℝ) + 1)
        * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
        = 5 * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) / ((m : ℝ) + 1) from by ring,
      le_div_iff₀ hM]
    exact hkey
  · push Not at hk
    have h1 : P1 m (k : ℤ) = 0 := by
      refine P1_eq_zero ?_
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ))]
      omega
    have h2 : P1 m ((k : ℤ) + 1) = 0 := by
      refine P1_eq_zero ?_
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ) + 1)]
      omega
    rw [h1, h2, sub_zero, abs_zero]
    positivity

/-- The numerical constant paid for shifting the site by one when reflecting the
gradient bound to the negative half of the range. -/
lemma exp_quarter_le : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
  have h1 : (3 : ℝ) / 4 ≤ Real.exp (-(1 / 4 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
    linarith
  have h2 : Real.exp (1 / 4 : ℝ) * Real.exp (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : (0 : ℝ) < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
  nlinarith [mul_nonneg h3.le (by linarith : (0 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) - 3 / 4)]

/-- The discrete gradient of the one-dimensional lazy walk kernel obeys a
Gaussian bound with the extra factor `(m+1)^{-1}` coming from the exact
difference formula. -/
theorem P1_gradient (m : ℕ) (k : ℤ) :
    |P1 m k - P1 m (k + 1)|
      ≤ 8 / ((m : ℝ) + 1) * Real.exp (-((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hMne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hM
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  by_cases hk : 0 ≤ k
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = (t : ℤ) := ⟨k.toNat, by omega⟩
    rw [Int.cast_natCast]
    have hb := P1_gradient_nat m t
    have hexp : Real.exp (-((t : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
        ≤ Real.exp (-((t : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
      refine Real.exp_le_exp.mpr ?_
      have hd : -((t : ℝ) ^ 2) / (8 * ((m : ℝ) + 1)) - -((t : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))
          = (t : ℝ) ^ 2 / (8 * ((m : ℝ) + 1)) := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (t : ℝ) ^ 2 / (8 * ((m : ℝ) + 1)) := by positivity
      linarith
    have hcoef : (5 : ℝ) / ((m : ℝ) + 1) ≤ 8 / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hM hM]
      linarith
    have hF : (0 : ℝ) ≤ Real.exp (-((t : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := Real.exp_nonneg _
    have h5 : (0 : ℝ) ≤ 5 / ((m : ℝ) + 1) := by positivity
    calc |P1 m (t : ℤ) - P1 m ((t : ℤ) + 1)|
        ≤ 5 / ((m : ℝ) + 1) * Real.exp (-((t : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := hb
      _ ≤ 5 / ((m : ℝ) + 1) * Real.exp (-((t : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hexp h5
      _ ≤ 8 / ((m : ℝ) + 1) * Real.exp (-((t : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right hcoef hF
  · push Not at hk
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) - 1 := ⟨(-k - 1).toNat, by omega⟩
    have e1 : P1 m (-(j : ℤ) - 1) = P1 m ((j : ℤ) + 1) := by
      rw [show -(j : ℤ) - 1 = -((j : ℤ) + 1) from by ring, P1_symm]
    have e2 : P1 m (-(j : ℤ) - 1 + 1) = P1 m (j : ℤ) := by
      rw [show -(j : ℤ) - 1 + 1 = -(j : ℤ) from by ring, P1_symm]
    rw [e1, e2, abs_sub_comm,
      show ((-(j : ℤ) - 1 : ℤ) : ℝ) = -(j : ℝ) - 1 from by push_cast; ring]
    have hb := P1_gradient_nat m j
    have hF : (0 : ℝ) ≤ Real.exp (-((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1))) :=
      Real.exp_nonneg _
    have hexpineq : Real.exp (-((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
        ≤ 4 / 3 * Real.exp (-((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1))) := by
      have hstep : -((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))
          ≤ 1 / 4 + -((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1)) := by
        have hd : (1 / 4 + -((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1)))
              - -((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))
            = (2 * ((m : ℝ) + 1) - ((j : ℝ) + 1) ^ 2 + 2 * (j : ℝ) ^ 2)
              / (8 * ((m : ℝ) + 1)) := by
          field_simp
          ring
        have hnum : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1) - ((j : ℝ) + 1) ^ 2 + 2 * (j : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((j : ℝ) - 1)]
        have hq := div_nonneg hnum (show (0 : ℝ) ≤ 8 * ((m : ℝ) + 1) by positivity)
        linarith
      have h1 := Real.exp_le_exp.mpr hstep
      rw [Real.exp_add] at h1
      have h2 := mul_le_mul_of_nonneg_right exp_quarter_le hF
      linarith
    have h5 : (0 : ℝ) ≤ 5 / ((m : ℝ) + 1) := by positivity
    have hcc : (5 : ℝ) / ((m : ℝ) + 1) * (4 / 3) ≤ 8 / ((m : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hM hM]
      linarith
    calc |P1 m (j : ℤ) - P1 m ((j : ℤ) + 1)|
        ≤ 5 / ((m : ℝ) + 1) * Real.exp (-((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := hb
      _ ≤ 5 / ((m : ℝ) + 1)
            * (4 / 3 * Real.exp (-((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left hexpineq h5
      _ = 5 / ((m : ℝ) + 1) * (4 / 3)
            * Real.exp (-((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1))) := by ring
      _ ≤ 8 / ((m : ℝ) + 1) * Real.exp (-((-(j : ℝ) - 1) ^ 2) / (8 * ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right hcc hF

end LatticeProb
