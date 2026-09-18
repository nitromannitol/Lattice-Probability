/-
Small `Real.rpow`/floor/absolute-value arithmetic facts used throughout the Kolmogorov-Chentsov
moment chain: bounding a sum's `p`-th power by cardinality times the sum of `p`-th powers
(`abs_sum_rpow_le`), raising a `2/p`-rooted moment bound to the `p`-th moment
(`le_rpow_half_of_rpow_two_div_le`), the `n^{-p/4}` power algebra used to carry a scale prefactor
through a moment bound (`rpow_neg_half_rpow_half`, `rpow_quarter_mul_rpow_neg_quarter`,
`sqrt_rpow_half_mul_rpow_neg_quarter`), how nearby real numbers' floors compare
(`abs_intFloor_sub_le`, `abs_floor_sub_le`, `abs_intFloor_sub_le_two`,
`abs_floor_sub_half_floor_sub_le`), the `p`-th power of a three-term sum
(`abs_add_add_rpow_le`), and the cast of a nonnegative integer's natural clamp
(`toNat_cast_real`).  Every statement is for abstract reals, sequences, or finite sets: none
depends on a particular choice of random field.
-/
import Mathlib

noncomputable section

namespace LatticeProb.KolmogorovChentsov

/-- **The `p`-th power of a sum is bounded by the cardinality power times the
sum of the `p`-th powers.** -/
theorem abs_sum_rpow_le {ι : Type*} (S : Finset ι) (a : ι → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    |∑ c ∈ S, a c| ^ p ≤ (S.card : ℝ) ^ p * ∑ c ∈ S, |a c| ^ p := by
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    rw [Finset.sum_empty, Finset.sum_empty, abs_zero,
      Real.zero_rpow (ne_of_gt (lt_of_lt_of_le one_pos hp))]
    positivity
  · obtain ⟨c₀, hc₀, hmax⟩ := S.exists_max_image (fun c => |a c|) hS
    have h1 : |∑ c ∈ S, a c| ≤ (S.card : ℝ) * |a c₀| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [show (∑ c ∈ S, |a c|) = ∑ c ∈ S, |a c| from rfl]
      have := Finset.sum_le_card_nsmul S (fun c => |a c|) (|a c₀|) (fun c hc => hmax c hc)
      rwa [nsmul_eq_mul] at this
    have h2 : |a c₀| ^ p ≤ ∑ c ∈ S, |a c| ^ p :=
      Finset.single_le_sum (fun c _ => Real.rpow_nonneg (abs_nonneg _) _) hc₀
    calc |∑ c ∈ S, a c| ^ p ≤ ((S.card : ℝ) * |a c₀|) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) h1 hp0
      _ = (S.card : ℝ) ^ p * |a c₀| ^ p :=
          Real.mul_rpow (Nat.cast_nonneg _) (abs_nonneg _)
      _ ≤ (S.card : ℝ) ^ p * ∑ c ∈ S, |a c| ^ p :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **From a `2/p`-rooted bound to the `p`-th moment bound.** -/
theorem le_rpow_half_of_rpow_two_div_le {x Y p : ℝ} (hx : 0 ≤ x) (_hY : 0 ≤ Y) (hp : 0 < p)
    (h : x ^ (2 / p) ≤ Y) : x ≤ Y ^ (p / 2) := by
  have h1 : x = (x ^ (2 / p)) ^ (p / 2) := by
    rw [← Real.rpow_mul hx]
    have h2 : (2 : ℝ) / p * (p / 2) = 1 := by field_simp
    rw [h2, Real.rpow_one]
  conv_lhs => rw [h1]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx _) h (by positivity)

/-- **The `(n^{-1/2})^{p/2} = n^{-p/4}` power algebra of the moment bound.** -/
theorem rpow_neg_half_rpow_half (n : ℕ) (p : ℝ) :
    ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ (p / 2) = (n : ℝ) ^ (-(p / 4)) := by
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring


/-- **Floors of nearby points differ by at most one.** -/
theorem abs_intFloor_sub_le {x y : ℝ} (h : |x - y| ≤ 1) : |⌊x⌋ - ⌊y⌋| ≤ 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have h5 := abs_le.mp h
  have hlo : (-2 : ℝ) < (⌊x⌋ : ℝ) - ⌊y⌋ := by linarith
  have hhi : (⌊x⌋ : ℝ) - ⌊y⌋ < 2 := by linarith
  have hlo' : (-2 : ℤ) < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast hlo
  have hhi' : ⌊x⌋ - ⌊y⌋ < 2 := by exact_mod_cast hhi
  rw [abs_le]
  constructor <;> omega


/-- **The floor difference is bounded by the real difference plus one.** -/
theorem abs_floor_sub_le (x y : ℝ) : |(⌊x⌋ : ℝ) - ⌊y⌋| ≤ |x - y| + 1 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h4 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have h5 := neg_abs_le (x - y)
  have h6 := le_abs_self (x - y)
  rw [abs_le]
  constructor <;> linarith

/-- **The `p`-th power of a three-term sum.** -/
theorem abs_add_add_rpow_le (a b c p : ℝ) (hp : 1 ≤ p) :
    |a + b + c| ^ p ≤ 3 ^ p * (|a| ^ p + |b| ^ p + |c| ^ p) := by
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  set M := max (max |a| |b|) |c| with hM
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (le_max_right _ _)
  have ha : |a| ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb : |b| ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc : |c| ≤ M := le_max_right _ _
  have h1 : |a + b + c| ≤ 3 * M := by
    calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 3 * M := by linarith
  have h2 : M ^ p ≤ |a| ^ p + |b| ^ p + |c| ^ p := by
    rcases le_total (max |a| |b|) |c| with hmc | hmc
    · rw [hM, max_eq_right hmc]
      exact le_add_of_nonneg_left
        (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _))
    · rw [hM, max_eq_left hmc]
      rcases le_total |a| |b| with hab | hab
      · rw [max_eq_right hab]
        exact le_trans (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
      · rw [max_eq_left hab]
        exact le_trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
  calc |a + b + c| ^ p ≤ (3 * M) ^ p := Real.rpow_le_rpow (abs_nonneg _) h1 hp0
    _ = 3 ^ p * M ^ p := Real.mul_rpow (by norm_num) hM0
    _ ≤ 3 ^ p * (|a| ^ p + |b| ^ p + |c| ^ p) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)


/-- **The centered difference of two floor pairs** is the centered real
difference up to the rounding error `3/2`. -/
theorem abs_floor_sub_half_floor_sub_le (a b c d : ℝ) :
    |(⌊a⌋ : ℝ) - ⌊b⌋ - (((⌊c⌋ : ℝ) - ⌊d⌋) / 2)| ≤ |a - b - (c - d) / 2| + 3 / 2 := by
  have ha0 : (0 : ℝ) ≤ a - ⌊a⌋ := sub_nonneg.mpr (Int.floor_le a)
  have ha1 : a - ⌊a⌋ < 1 := by linarith [Int.lt_floor_add_one a]
  have hb0 : (0 : ℝ) ≤ b - ⌊b⌋ := sub_nonneg.mpr (Int.floor_le b)
  have hb1 : b - ⌊b⌋ < 1 := by linarith [Int.lt_floor_add_one b]
  have hc0 : (0 : ℝ) ≤ c - ⌊c⌋ := sub_nonneg.mpr (Int.floor_le c)
  have hc1 : c - ⌊c⌋ < 1 := by linarith [Int.lt_floor_add_one c]
  have hd0 : (0 : ℝ) ≤ d - ⌊d⌋ := sub_nonneg.mpr (Int.floor_le d)
  have hd1 : d - ⌊d⌋ < 1 := by linarith [Int.lt_floor_add_one d]
  have h5 := neg_abs_le (a - b - (c - d) / 2)
  have h6 := le_abs_self (a - b - (c - d) / 2)
  rw [abs_le]
  constructor <;> linarith

/-- **The power cancellation** `n^{p/4} · n^{-p/4} = 1`. -/
theorem rpow_quarter_mul_rpow_neg_quarter (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    (n : ℝ) ^ (p / 4) * (n : ℝ) ^ (-(p / 4)) = 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add hn0]
  simp

/-- **The square-root-to-power scaling** `(√(nρ))^{p/2} · n^{-p/4} = ρ^{p/4}`. -/
theorem sqrt_rpow_half_mul_rpow_neg_quarter (n : ℕ) (hn : 1 ≤ n) {ρ p : ℝ} (hρ : 0 ≤ ρ) :
    (Real.sqrt ((n : ℝ) * ρ)) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) = ρ ^ (p / 4) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg hn0.le hρ),
    show (1 : ℝ) / 2 * (p / 2) = p / 4 by ring, Real.mul_rpow hn0.le hρ, mul_assoc,
    mul_comm (ρ ^ (p / 4)) ((n : ℝ) ^ (-(p / 4))), ← mul_assoc,
    rpow_quarter_mul_rpow_neg_quarter n hn p, one_mul]

/-- **Cast of the natural clamp.** -/
theorem toNat_cast_real {m : ℤ} (hm : 0 ≤ m) : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg hm


/-- **Floors of points within `3/2` differ by at most two.** -/
theorem abs_intFloor_sub_le_two {x y : ℝ} (h : |x - y| ≤ 3 / 2) : |⌊x⌋ - ⌊y⌋| ≤ 2 := by
  have hR : |(⌊x⌋ : ℝ) - ⌊y⌋| ≤ 5 / 2 := le_trans (abs_floor_sub_le x y) (by linarith)
  rw [abs_le] at hR
  have h1 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) ≤ 5 / 2 := by exact_mod_cast hR.2
  have h3 : -(5 / 2 : ℝ) ≤ ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast hR.1
  rw [abs_le]
  constructor
  · by_contra hlt
    have h5 : (⌊x⌋ - ⌊y⌋ : ℤ) ≤ -3 := by omega
    have h6 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) ≤ -3 := by exact_mod_cast h5
    linarith
  · by_contra hlt
    have h5 : (3 : ℤ) ≤ ⌊x⌋ - ⌊y⌋ := by omega
    have h6 : (3 : ℝ) ≤ ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast h5
    linarith


end LatticeProb.KolmogorovChentsov

end
