/-
Summing a heat-kernel gradient bound `r^{-(d+1)/2}` against its Gaussian factor
`exp(-n^2 / (8 (r + d)))` over all times `1 ≤ r < R` produces the spatial decay
`|n|^{1-d}`.  The argument is elementary: the sum is cut at `r = n^2`, the
Gaussian factor is discarded on the far side and expanded through a single
term of the exponential series on the near side.
-/
import Mathlib
import LatticeProb.Walk.Series
import LatticeProb.Walk.GreenBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

/-- A single term of the exponential series inverted: for `t > 0` and any `k`,
`exp (-t) ≤ k! / t ^ k`.  This is the only place where the Gaussian factor is
converted into a power of `t`. -/
lemma exp_neg_le_factorial_div (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ (Nat.factorial k : ℝ) / t ^ k := by
  have hterm : t ^ k / (Nat.factorial k : ℝ) ≤ Real.exp t := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg ht.le (k + 1))
    refine Finset.single_le_sum (f := fun i => t ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) ?_
    simp
  have hpos : (0 : ℝ) < t ^ k / (Nat.factorial k : ℝ) := by positivity
  rw [Real.exp_neg]
  have h := (inv_le_inv₀ (lt_of_lt_of_le hpos hterm) hpos).mpr hterm
  rwa [inv_div] at h

/-- The head estimate, one term at a time.  For `1 ≤ r ≤ n ^ 2` the Gaussian
factor is small enough that `r ^ {-(d+1)/2} exp(-n^2/(8(r+d)))` is at most a
constant times `n ^ {-d-1}`. -/
lemma head_term_le {d : ℕ} (hd : 2 ≤ d) {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n ^ 2) :
    (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ (Nat.factorial d : ℝ) * (8 * (1 + (d : ℝ))) ^ d * (n : ℝ) ^ (-(d : ℝ) - 1) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : (0 : ℝ) < 8 * ((r : ℝ) + (d : ℝ)) := by linarith
  have ht : 0 < (n : ℝ) ^ 2 / (8 * ((r : ℝ) + (d : ℝ))) := div_pos (pow_pos hn0 2) hden
  have harg : (-((n : ℝ)) ^ 2) / (8 * ((r : ℝ) + (d : ℝ)))
      = -((n : ℝ) ^ 2 / (8 * ((r : ℝ) + (d : ℝ)))) := by ring
  have htd : ((n : ℝ) ^ 2 / (8 * ((r : ℝ) + (d : ℝ)))) ^ d
      = (n : ℝ) ^ (2 * d) / (8 * ((r : ℝ) + (d : ℝ))) ^ d := by
    rw [div_pow, ← pow_mul]
  have hrd : (8 : ℝ) * ((r : ℝ) + (d : ℝ)) ≤ 8 * (1 + (d : ℝ)) * (r : ℝ) := by nlinarith
  have hpow : (8 * ((r : ℝ) + (d : ℝ))) ^ d ≤ (8 * (1 + (d : ℝ))) ^ d * (r : ℝ) ^ d := by
    calc (8 * ((r : ℝ) + (d : ℝ))) ^ d
        ≤ (8 * (1 + (d : ℝ)) * (r : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 8 * ((r : ℝ) + (d : ℝ))) hrd d
      _ = (8 * (1 + (d : ℝ))) ^ d * (r : ℝ) ^ d := mul_pow _ _ d
  have hexp2 : Real.exp (-((n : ℝ) ^ 2 / (8 * ((r : ℝ) + (d : ℝ)))))
      ≤ (Nat.factorial d : ℝ) * ((8 * (1 + (d : ℝ))) ^ d * (r : ℝ) ^ d) / (n : ℝ) ^ (2 * d) := by
    refine (exp_neg_le_factorial_div d ht).trans ?_
    rw [htd, div_div_eq_mul_div]
    gcongr
  have hkey : (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * (r : ℝ) ^ d ≤ (n : ℝ) ^ ((d : ℝ) - 1) := by
    have h1 : (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * (r : ℝ) ^ d
        = (r : ℝ) ^ ((d : ℝ) - ((d : ℝ) + 1) / 2) := by
      rw [← Real.rpow_natCast (r : ℝ) d, ← Real.rpow_add hr0]
      congr 1
      ring
    have h2 : (0 : ℝ) ≤ (d : ℝ) - ((d : ℝ) + 1) / 2 := by linarith
    have h3 : (r : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hrn
    rw [h1]
    refine (Real.rpow_le_rpow hr0.le h3 h2).trans ?_
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hn0.le]
    refine le_of_eq ?_
    congr 1
    push_cast
    ring
  have hn2d : (n : ℝ) ^ (2 * d) = (n : ℝ) ^ ((2 : ℝ) * (d : ℝ)) := by
    rw [← Real.rpow_natCast (n : ℝ) (2 * d)]
    congr 1
    push_cast
    ring
  rw [harg]
  calc (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ) ^ 2 / (8 * ((r : ℝ) + (d : ℝ)))))
      ≤ (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
          * ((Nat.factorial d : ℝ) * ((8 * (1 + (d : ℝ))) ^ d * (r : ℝ) ^ d)
              / (n : ℝ) ^ (2 * d)) :=
        mul_le_mul_of_nonneg_left hexp2 (Real.rpow_nonneg hr0.le _)
    _ = (Nat.factorial d : ℝ) * (8 * (1 + (d : ℝ))) ^ d
          * ((r : ℝ) ^ (-((d : ℝ) + 1) / 2) * (r : ℝ) ^ d) / (n : ℝ) ^ (2 * d) := by
        ring
    _ ≤ (Nat.factorial d : ℝ) * (8 * (1 + (d : ℝ))) ^ d
          * ((n : ℝ) ^ ((d : ℝ) - 1)) / (n : ℝ) ^ (2 * d) := by
        gcongr
    _ = (Nat.factorial d : ℝ) * (8 * (1 + (d : ℝ))) ^ d
          * ((n : ℝ) ^ ((d : ℝ) - 1) / (n : ℝ) ^ ((2 : ℝ) * (d : ℝ))) := by
        rw [hn2d]; ring
    _ = (Nat.factorial d : ℝ) * (8 * (1 + (d : ℝ))) ^ d * (n : ℝ) ^ (-(d : ℝ) - 1) := by
        rw [← Real.rpow_sub hn0, show (d : ℝ) - 1 - 2 * (d : ℝ) = -(d : ℝ) - 1 from by ring]

/-- The constant produced by the head of the sum, `1 ≤ r ≤ n ^ 2`. -/
noncomputable def headConst (d : ℕ) : ℝ := (Nat.factorial d : ℝ) * (8 * (1 + (d : ℝ))) ^ d

/-- The constant produced by the tail of the sum, `n ^ 2 < r < R`. -/
noncomputable def tailConst (d : ℕ) : ℝ := 2 / ((d : ℝ) - 1)

/-- Confirms that the head constant is nonnegative. -/
lemma headConst_nonneg (d : ℕ) : 0 ≤ headConst d := by
  unfold headConst
  positivity

/-- Confirms that the tail constant is positive once `d ≥ 2`. -/
lemma tailConst_pos {d : ℕ} (hd : 2 ≤ d) : 0 < tailConst d := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold tailConst
  exact div_pos (by norm_num) (by linarith)

/-- The head of the sum, `1 ≤ r ≤ n ^ 2`, contributes at most
`headConst d * n ^ {1-d}`: each of the `n ^ 2` terms is at most
`headConst d * n ^ {-d-1}`. -/
lemma head_sum_le {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    ∑ r ∈ Finset.Ico (1 : ℕ) (n ^ 2 + 1),
        (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ headConst d * (n : ℝ) ^ (1 - (d : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcard : (Finset.Ico (1 : ℕ) (n ^ 2 + 1)).card = n ^ 2 := by
    rw [Nat.card_Ico]
    omega
  have hlast : ((n : ℝ) ^ 2) * (headConst d * (n : ℝ) ^ (-(d : ℝ) - 1))
      = headConst d * (n : ℝ) ^ (1 - (d : ℝ)) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← mul_assoc, mul_comm ((n : ℝ) ^ (((2 : ℕ) : ℝ)))
      (headConst d), mul_assoc, ← Real.rpow_add hn0]
    congr 2
    push_cast
    ring
  calc ∑ r ∈ Finset.Ico (1 : ℕ) (n ^ 2 + 1),
        (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ ∑ _r ∈ Finset.Ico (1 : ℕ) (n ^ 2 + 1), headConst d * (n : ℝ) ^ (-(d : ℝ) - 1) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        rw [Finset.mem_Ico] at hr
        exact head_term_le hd hn hr.1 (by omega)
    _ = ((n : ℝ) ^ 2) * (headConst d * (n : ℝ) ^ (-(d : ℝ) - 1)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring
    _ = headConst d * (n : ℝ) ^ (1 - (d : ℝ)) := hlast

/-- Reindexing the tail so that the summand has the shape `f (i+1)` demanded by
the sum-integral comparison. -/
lemma tail_reindex {c : ℝ} {n R : ℕ} :
    ∑ r ∈ Finset.Ico (n ^ 2 + 1) R, (r : ℝ) ^ c
      = ∑ i ∈ Finset.Ico (n ^ 2) (R - 1), (fun x : ℝ => x ^ c) ((i + 1 : ℕ) : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show R - (n ^ 2 + 1) = R - 1 - n ^ 2 from by omega]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show n ^ 2 + 1 + i = n ^ 2 + i + 1 from by omega]

/-- The pure power sum over the tail range `n ^ 2 < r < R` is at most
`tailConst d * n ^ {1-d}`, by comparison with the integral of `x ^ {-(d+1)/2}`. -/
lemma tail_rpow_sum_le {d : ℕ} (hd : 2 ≤ d) {n R : ℕ} (hn : 1 ≤ n) :
    ∑ r ∈ Finset.Ico (n ^ 2 + 1) R, (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
      ≤ tailConst d * (n : ℝ) ^ (1 - (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdm : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hRHS : (0 : ℝ) ≤ tailConst d * (n : ℝ) ^ (1 - (d : ℝ)) :=
    mul_nonneg (tailConst_pos hd).le (Real.rpow_nonneg hn0.le _)
  by_cases hR : R ≤ n ^ 2 + 1
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact hRHS
  · push Not at hR
    have hab : n ^ 2 ≤ R - 1 := by omega
    have ha0 : (0 : ℝ) < ((n ^ 2 : ℕ) : ℝ) := by
      have : 0 < n ^ 2 := by positivity
      exact_mod_cast this
    have hab' : ((n ^ 2 : ℕ) : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := by exact_mod_cast hab
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-((d : ℝ) + 1) / 2))
        (Set.Icc ((n ^ 2 : ℕ) : ℝ) ((R - 1 : ℕ) : ℝ)) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le ha0 hx.1) hxy (by linarith)
    have hsum := AntitoneOn.sum_le_integral_Ico
      (f := fun x : ℝ => x ^ (-((d : ℝ) + 1) / 2)) hab hanti
    have hnotmem : (0 : ℝ) ∉ Set.uIcc ((n ^ 2 : ℕ) : ℝ) ((R - 1 : ℕ) : ℝ) := by
      intro hmem
      rw [Set.uIcc_of_le hab', Set.mem_Icc] at hmem
      linarith [hmem.1]
    have hexpne : (-((d : ℝ) + 1) / 2) ≠ -1 := by
      intro h
      linarith
    have hint := integral_rpow (a := ((n ^ 2 : ℕ) : ℝ)) (b := ((R - 1 : ℕ) : ℝ))
      (r := -((d : ℝ) + 1) / 2) (Or.inr ⟨hexpne, hnotmem⟩)
    have hc : -((d : ℝ) + 1) / 2 + 1 = (1 - (d : ℝ)) / 2 := by ring
    have hacast : ((n ^ 2 : ℕ) : ℝ) ^ ((1 - (d : ℝ)) / 2) = (n : ℝ) ^ (1 - (d : ℝ)) := by
      rw [show ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ (2 : ℕ) from by push_cast; ring,
        ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hn0.le]
      congr 1
      push_cast
      ring
    have hbnn : (0 : ℝ) ≤ ((R - 1 : ℕ) : ℝ) ^ ((1 - (d : ℝ)) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hne1 : (1 : ℝ) - (d : ℝ) ≠ 0 := by intro h; linarith
    have hne2 : (d : ℝ) - 1 ≠ 0 := ne_of_gt hdm
    have hdiff : tailConst d * (n : ℝ) ^ (1 - (d : ℝ))
        - (((R - 1 : ℕ) : ℝ) ^ ((1 - (d : ℝ)) / 2)
            - ((n ^ 2 : ℕ) : ℝ) ^ ((1 - (d : ℝ)) / 2)) / ((1 - (d : ℝ)) / 2)
        = 2 * (((R - 1 : ℕ) : ℝ) ^ ((1 - (d : ℝ)) / 2)) / ((d : ℝ) - 1) := by
      rw [← hacast]
      unfold tailConst
      field_simp
      ring
    have hpos2 : (0 : ℝ) ≤ 2 * (((R - 1 : ℕ) : ℝ) ^ ((1 - (d : ℝ)) / 2)) / ((d : ℝ) - 1) :=
      div_nonneg (by linarith) hdm.le
    calc ∑ r ∈ Finset.Ico (n ^ 2 + 1) R, (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
        = ∑ i ∈ Finset.Ico (n ^ 2) (R - 1),
            (fun x : ℝ => x ^ (-((d : ℝ) + 1) / 2)) ((i + 1 : ℕ) : ℝ) := tail_reindex
      _ ≤ ∫ x in ((n ^ 2 : ℕ) : ℝ)..((R - 1 : ℕ) : ℝ), x ^ (-((d : ℝ) + 1) / 2) := hsum
      _ = (((R - 1 : ℕ) : ℝ) ^ (-((d : ℝ) + 1) / 2 + 1)
            - ((n ^ 2 : ℕ) : ℝ) ^ (-((d : ℝ) + 1) / 2 + 1)) / (-((d : ℝ) + 1) / 2 + 1) := hint
      _ ≤ tailConst d * (n : ℝ) ^ (1 - (d : ℝ)) := by
          rw [hc]
          linarith

/-- The tail of the sum, `n ^ 2 < r < R`, contributes at most
`tailConst d * n ^ {1-d}`: there the Gaussian factor is simply discarded. -/
lemma tail_sum_le {d : ℕ} (hd : 2 ≤ d) {n R : ℕ} (hn : 1 ≤ n) :
    ∑ r ∈ Finset.Ico (n ^ 2 + 1) R,
        (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ tailConst d * (n : ℝ) ^ (1 - (d : ℝ)) := by
  refine le_trans (Finset.sum_le_sum (fun r hr => ?_)) (tail_rpow_sum_le hd (R := R) hn)
  rw [Finset.mem_Ico] at hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : 1 ≤ r := by omega
    exact_mod_cast this
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hexp1 : Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + (d : ℝ)))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ((n : ℝ))]) (by linarith)
  calc (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + (d : ℝ))))
      ≤ (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp1 (Real.rpow_nonneg hr0.le _)
    _ = (r : ℝ) ^ (-((d : ℝ) + 1) / 2) := mul_one _

/-- Splitting the range `1 ≤ r < R` at `r = n ^ 2`. -/
lemma sum_split_le {d n R : ℕ} :
    ∑ r ∈ Finset.Ico 1 R,
        (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ (∑ r ∈ Finset.Ico (1 : ℕ) (n ^ 2 + 1),
            (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d))))
        + ∑ r ∈ Finset.Ico (n ^ 2 + 1) R,
            (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d))) := by
  classical
  have hnn : ∀ r : ℕ, (0 : ℝ)
      ≤ (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d))) :=
    fun r => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _) (Real.exp_nonneg _)
  have hsub : Finset.Ico 1 R ⊆ Finset.Ico (1 : ℕ) (n ^ 2 + 1) ∪ Finset.Ico (n ^ 2 + 1) R := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.Ico (1 : ℕ) (n ^ 2 + 1)) (Finset.Ico (n ^ 2 + 1) R) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_Ico] at hr hr'
    omega
  calc ∑ r ∈ Finset.Ico 1 R,
        (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ ∑ r ∈ Finset.Ico (1 : ℕ) (n ^ 2 + 1) ∪ Finset.Ico (n ^ 2 + 1) R,
          (r : ℝ) ^ (-((d : ℝ) + 1) / 2) * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hnn r)
    _ = _ := Finset.sum_union hdisj

/-- The `n = 0` case: the Gaussian factor is `1` and the remaining power sum is
bounded by `3`. -/
lemma sum_zero_le {d : ℕ} (hd : 2 ≤ d) (R : ℕ) :
    ∑ r ∈ Finset.Ico 1 R,
        (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
          * Real.exp (-(((0 : ℕ) : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      ≤ 3 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hrw : ∑ r ∈ Finset.Ico 1 R,
      (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
        * Real.exp (-(((0 : ℕ) : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
      = ∑ r ∈ Finset.Ico 1 R, (r : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    norm_num
  rw [hrw]
  refine le_trans (Finset.sum_le_sum (fun r hr => ?_)) (sum_rpow_three_halves_le R)
  rw [Finset.mem_Ico] at hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
  exact Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)

/-- The constant in the summation estimate, explicit. -/
noncomputable def sumConst (d : ℕ) : ℝ :=
  3 + (headConst d + tailConst d) * (2 : ℝ) ^ ((d : ℝ) - 1)

/-- Confirms that the constant of the summation estimate is positive. -/
lemma sumConst_pos {d : ℕ} (hd : 2 ≤ d) : 0 < sumConst d := by
  have h1 : (0 : ℝ) ≤ (headConst d + tailConst d) * (2 : ℝ) ^ ((d : ℝ) - 1) :=
    mul_nonneg (by linarith [headConst_nonneg d, (tailConst_pos hd).le])
      (Real.rpow_nonneg (by norm_num) _)
  unfold sumConst
  linarith

/-- Passing from decay in `n` to decay in `1 + n`, which costs the factor
`2 ^ {d-1}` because the exponent `1 - d` is negative. -/
lemma shift_one_le {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) {K : ℝ} (hK : 0 ≤ K) :
    K * (n : ℝ) ^ (1 - (d : ℝ))
      ≤ (K * (2 : ℝ) ^ ((d : ℝ) - 1)) * (1 + (n : ℝ)) ^ (1 - (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h2d : (2 : ℝ) ^ ((d : ℝ) - 1) * (2 : ℝ) ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmul : (2 * (n : ℝ)) ^ (1 - (d : ℝ))
      = (2 : ℝ) ^ (1 - (d : ℝ)) * (n : ℝ) ^ (1 - (d : ℝ)) :=
    Real.mul_rpow (by norm_num) hn0.le
  have hcmp : (2 * (n : ℝ)) ^ (1 - (d : ℝ)) ≤ (1 + (n : ℝ)) ^ (1 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hKnn : (0 : ℝ) ≤ K * (2 : ℝ) ^ ((d : ℝ) - 1) :=
    mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
  calc K * (n : ℝ) ^ (1 - (d : ℝ))
      = (K * (2 : ℝ) ^ ((d : ℝ) - 1))
          * ((2 : ℝ) ^ (1 - (d : ℝ)) * (n : ℝ) ^ (1 - (d : ℝ))) := by
        rw [show (K * (2 : ℝ) ^ ((d : ℝ) - 1))
              * ((2 : ℝ) ^ (1 - (d : ℝ)) * (n : ℝ) ^ (1 - (d : ℝ)))
            = K * ((2 : ℝ) ^ ((d : ℝ) - 1) * (2 : ℝ) ^ (1 - (d : ℝ)))
              * (n : ℝ) ^ (1 - (d : ℝ)) from by ring, h2d]
        ring
    _ = (K * (2 : ℝ) ^ ((d : ℝ) - 1)) * (2 * (n : ℝ)) ^ (1 - (d : ℝ)) := by rw [hmul]
    _ ≤ (K * (2 : ℝ) ^ ((d : ℝ) - 1)) * (1 + (n : ℝ)) ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hcmp hKnn

/-- Summing the heat-kernel gradient bound `r ^ {-(d+1)/2}` against its Gaussian
factor over all times gives the spatial decay `(1+n) ^ {1-d}`. -/
theorem exists_sum_rpow_exp_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R n : ℕ),
      ∑ r ∈ Finset.Ico 1 R, (r : ℝ) ^ (-((d : ℝ) + 1) / 2)
          * Real.exp (-((n : ℝ)) ^ 2 / (8 * ((r : ℝ) + d)))
        ≤ C * (1 + (n : ℝ)) ^ (1 - (d : ℝ)) := by
  refine ⟨sumConst d, sumConst_pos hd, fun R n => ?_⟩
  have hhead : (0 : ℝ) ≤ headConst d := headConst_nonneg d
  have htail : (0 : ℝ) < tailConst d := tailConst_pos hd
  have hK : (0 : ℝ) ≤ headConst d + tailConst d := by linarith
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (1 + ((0 : ℕ) : ℝ)) ^ (1 - (d : ℝ)) = 1 := by
      norm_num
    rw [h1, mul_one]
    refine (sum_zero_le hd R).trans ?_
    unfold sumConst
    nlinarith
  · refine le_trans sum_split_le ?_
    refine le_trans (add_le_add (head_sum_le hd hn) (tail_sum_le hd hn)) ?_
    have hsum : headConst d * (n : ℝ) ^ (1 - (d : ℝ)) + tailConst d * (n : ℝ) ^ (1 - (d : ℝ))
        = (headConst d + tailConst d) * (n : ℝ) ^ (1 - (d : ℝ)) := by ring
    rw [hsum]
    refine (shift_one_le hd hn hK).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
    unfold sumConst
    linarith

end LatticeProb
