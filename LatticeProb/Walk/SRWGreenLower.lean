import LatticeProb.Walk.SRWDiag
import LatticeProb.Walk.VarianceScale
import LatticeProb.Walk.SRWGreenSup
import LatticeProb.Walk.Range

/-!
# Lower bounds for the truncated Green function

Lower bounds for the truncated Green function of the simple random walk at the origin.

`exists_le_srwGreen_one_dim` and `exists_le_srwGreen_two_dim` give the matching lower halves of
the max-norm rates proved in `LatticeProb/Walk/SRWGreenSup.lean`: `srwGreen 1 n 0 ≳ √n` and
`srwGreen 2 n 0 ≳ log n`.  They are the two-sided companion of the upper bounds
`srwGreen_one_dim_le` and `srwGreen_two_dim_le`, and the `d ≥ 3` case needs nothing new
(`LatticeProb.one_le_srwGreen_origin`).

Route.  `srwGreen d N 0 = ∑_{j < N} srwHeat d j 0`; dropping the odd terms and using the
on-diagonal heat lower bound `exists_srwHeat_diag_lower` at the even times `j = 2s` gives
`srwGreen d N 0 ≥ c ∑_{s < N/2} s^{-d/2}`, and the two elementary sums
`∑_{s < m} s^{-1/2} ≥ √m / 2` and `∑_{s < m} s^{-1} ≥ log m / 2` finish.

-/

open Finset
open scoped Classical

namespace LatticeProb

/-- A lower bound `√m / 2 ≤ ∑_{s<m} s^{-1/2}`. -/
theorem sum_Ico_inv_sqrt_ge {m : ℕ} (hm : 2 ≤ m) :
    Real.sqrt (m : ℝ) / 2 ≤ ∑ s ∈ Finset.Ico 1 m, (Real.sqrt (s : ℝ))⁻¹ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by positivity
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hterm : ∀ s ∈ Finset.Ico 1 m, (Real.sqrt (m : ℝ))⁻¹ ≤ (Real.sqrt (s : ℝ))⁻¹ := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hle : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs.2.le
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hspos) (Real.sqrt_le_sqrt hle)
  have hsum : ∑ s ∈ Finset.Ico 1 m, (Real.sqrt (m : ℝ))⁻¹
      = ((m : ℝ) - 1) * (Real.sqrt (m : ℝ))⁻¹ := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [hsum]
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  rw [show (↑m - 1) * (√↑m)⁻¹ * 2 = 2 * (↑m - 1) / √↑m by ring]
  rw [le_div_iff₀ hsm]
  nlinarith [hsq, hm2R, hsm]

/-- `log m / 2 ≤ ∑_{s < m} 1/s`. -/
theorem log_half_le_sum_inv (m : ℕ) :
    Real.log (m : ℝ) / 2 ≤ ∑ s ∈ Finset.Ico 1 m, ((s : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hm)
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    have h := log_le_sum_inv m
    linarith

/-- `Real.log 23 ≤ 4`. -/
theorem log_23_le_four : Real.log 23 ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  nlinarith [h1, sq_nonneg (Real.exp 1 - 2.72), sq_nonneg (Real.exp 1 ^ 2 - 7.4)]

/-- `Real.log n ≤ 4` for `2 ≤ n < 24`. -/
theorem log_le_four_of_lt (n : ℕ) (hn : n < 24) (h2 : 2 ≤ n) : Real.log (n : ℝ) ≤ 4 := by
  have hnR : (n : ℝ) ≤ 23 := by exact_mod_cast (by omega : n ≤ 23)
  exact le_trans (Real.log_le_log (by positivity) hnR) log_23_le_four

/-- A matching lower bound `c log n ≤ srwGreen 2 n 0` for the two-dimensional truncated Green function at the origin. -/
theorem exists_le_srwGreen_two_dim :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → c * Real.log (n : ℝ) ≤ srwGreen 2 n 0 := by
  obtain ⟨c, hc, hlow⟩ := exists_srwHeat_diag_lower (d := 2) (by norm_num)
  refine ⟨min (c / 4) (1 / 4), by positivity, fun n hn => ?_⟩
  have hmin : min (c / 4) (1 / 4) ≤ c / 4 := min_le_left _ _
  have hmin2 : min (c / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rcases Nat.lt_or_ge n 24 with hn24 | hn24
  · have h1 : (1 : ℝ) ≤ srwGreen 2 n 0 := by
      rw [srwGreen]
      have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => srwHeat 2 j 0)
        (fun j _ => srwHeat_nonneg j 0) h0)
      rw [srwHeat_zero]
      simp
    have h2 : Real.log (n : ℝ) ≤ 4 := log_le_four_of_lt n hn24 hn
    have h3 : min (c / 4) (1 / 4) * Real.log (n : ℝ) ≤ (1 / 4) * 4 :=
      mul_le_mul hmin2 h2 hlogpos (by norm_num)
    linarith
  · have hm2 : 2 ≤ n / 4 := by omega
    have hsum := log_half_le_sum_inv (n / 4)
    have hstep : ∑ s ∈ Finset.Ico 1 (n / 4), srwHeat 2 (2 * s) 0 ≤ srwGreen 2 n 0 := by
      rw [srwGreen]
      have himg : ∑ s ∈ Finset.Ico 1 (n / 4), srwHeat 2 (2 * s) 0
          = ∑ j ∈ (Finset.Ico 1 (n / 4)).image (fun s => 2 * s), srwHeat 2 j 0 := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨s, hs, rfl⟩ := hj
        rw [Finset.mem_Ico] at hs
        rw [Finset.mem_range]
        have h2 : 2 * (n / 4) ≤ n := by omega
        omega
      · intro j _ _
        exact srwHeat_nonneg j 0
    have hlow' : ∑ s ∈ Finset.Ico 1 (n / 4), c / (s : ℝ) ≤
        ∑ s ∈ Finset.Ico 1 (n / 4), srwHeat 2 (2 * s) 0 := by
      refine Finset.sum_le_sum fun s hs => ?_
      rw [Finset.mem_Ico] at hs
      have h := hlow s hs.1
      have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
      rw [Real.sq_sqrt hspos.le] at h
      exact h
    have hc0 : 0 ≤ c := hc.le
    have hsum2 : c * (Real.log ((n / 4 : ℕ) : ℝ) / 2) ≤
        ∑ s ∈ Finset.Ico 1 (n / 4), c / (s : ℝ) := by
      have h1 : c * (Real.log ((n / 4 : ℕ) : ℝ) / 2)
          ≤ c * ∑ s ∈ Finset.Ico 1 (n / 4), ((s : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hc0
      have h2 : c * ∑ s ∈ Finset.Ico 1 (n / 4), ((s : ℝ))⁻¹
          = ∑ s ∈ Finset.Ico 1 (n / 4), c / (s : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [div_eq_mul_inv]
      linarith [h1, h2.le, h2.ge]
    have hlogn : Real.log (n : ℝ) / 2 ≤ Real.log ((n / 4 : ℕ) : ℝ) := by
      have h4 : Real.sqrt (n : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by
        have h6 : (0 : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by positivity
        have h9 : (n : ℝ) ≤ ((n / 4 : ℕ) : ℝ) ^ 2 := by
          have h12 : (24 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn24
          have h13 : (n : ℝ) / 4 - 1 ≤ ((n / 4 : ℕ) : ℝ) := by
            have h14 : n < n / 4 * 4 + 4 := Nat.lt_div_mul_add (by norm_num : 0 < 4)
            have h15 : (n : ℝ) < ((n / 4 : ℕ) : ℝ) * 4 + 4 := by exact_mod_cast h14
            linarith
          have h18 : ((n : ℝ) / 4 - 1) ^ 2 ≤ ((n / 4 : ℕ) : ℝ) ^ 2 := by
            have h19 : (0 : ℝ) ≤ (n : ℝ) / 4 - 1 := by linarith
            exact pow_le_pow_left₀ h19 h13 2
          have h20 : (n : ℝ) ≤ ((n : ℝ) / 4 - 1) ^ 2 := by
            have h21 : 16 * ((n : ℝ) / 4 - 1) ^ 2 = (n : ℝ) ^ 2 - 8 * (n : ℝ) + 16 := by ring
            have h22 : (0 : ℝ) ≤ ((n : ℝ) - 12) ^ 2 := sq_nonneg _
            have h23 : ((n : ℝ) - 12) ^ 2 = (n : ℝ) ^ 2 - 24 * (n : ℝ) + 144 := by ring
            rw [h23] at h22
            nlinarith [h12, h21, h22]
          linarith [h18, h20]
        calc Real.sqrt (n : ℝ) ≤ Real.sqrt (((n / 4 : ℕ) : ℝ) ^ 2) := Real.sqrt_le_sqrt h9
          _ = ((n / 4 : ℕ) : ℝ) := Real.sqrt_sq h6
      calc Real.log (n : ℝ) / 2 = Real.log (Real.sqrt (n : ℝ)) := by
            rw [Real.log_sqrt (by positivity)]
        _ ≤ Real.log ((n / 4 : ℕ) : ℝ) :=
            Real.log_le_log (Real.sqrt_pos.mpr (by positivity)) h4
    have hlogpos4 : 0 ≤ Real.log ((n / 4 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n / 4))
    have hchain : min (c / 4) (1 / 4) * Real.log (n : ℝ) ≤ srwGreen 2 n 0 := by
      have hA : min (c / 4) (1 / 4) * Real.log (n : ℝ) ≤ c / 4 * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hmin hlogpos
      have hB : c / 4 * Real.log (n : ℝ) = c * (Real.log (n : ℝ) / 2) / 2 := by ring
      have hC : c * (Real.log (n : ℝ) / 2) / 2 ≤ c * Real.log ((n / 4 : ℕ) : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_left hlogn hc0
        linarith
      have hD : c * Real.log ((n / 4 : ℕ) : ℝ) / 2
          = c * (Real.log ((n / 4 : ℕ) : ℝ) / 2) := by ring
      have hE : c * (Real.log ((n / 4 : ℕ) : ℝ) / 2) ≤ srwGreen 2 n 0 :=
        le_trans hsum2 (le_trans hlow' hstep)
      linarith [hA, hB.le, hB.ge, hC, hD.le, hD.ge, hE]
    exact hchain

/-- A matching lower bound `c √n ≤ srwGreen 1 n 0` for the one-dimensional truncated Green function at the origin. -/
theorem exists_le_srwGreen_one_dim :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) ≤ srwGreen 1 n 0 := by
  obtain ⟨c, hc, hlow⟩ := exists_srwHeat_diag_lower (d := 1) (by norm_num)
  refine ⟨min (c / 4) (1 / 2), by positivity, fun n hn => ?_⟩
  have hmin : min (c / 4) (1 / 2) ≤ c / 4 := min_le_left _ _
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · have h1 : (1 : ℝ) ≤ srwGreen 1 n 0 := by
      rw [srwGreen]
      have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => srwHeat 1 j 0)
        (fun j _ => srwHeat_nonneg j 0) h0)
      rw [srwHeat_zero]
      simp
    have h2 : Real.sqrt (n : ℝ) ≤ 2 := by
      have : (n : ℝ) ≤ 4 := by
        have : n ≤ 3 := by omega
        exact_mod_cast (by omega : n ≤ 4)
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt this
        _ = 2 := by norm_num
    have h3 : min (c / 4) (1 / 2) * Real.sqrt (n : ℝ) ≤ (1 / 2) * 2 := by
      refine mul_le_mul (min_le_right _ _) h2 (Real.sqrt_nonneg _) (by norm_num)
    linarith
  · have hm2 : 2 ≤ n / 2 := by omega
    have hsum := sum_Ico_inv_sqrt_ge (m := n / 2) hm2
    have hstep : ∑ s ∈ Finset.Ico 1 (n / 2), srwHeat 1 (2 * s) 0 ≤ srwGreen 1 n 0 := by
      rw [srwGreen]
      have himg : ∑ s ∈ Finset.Ico 1 (n / 2), srwHeat 1 (2 * s) 0
          = ∑ j ∈ (Finset.Ico 1 (n / 2)).image (fun s => 2 * s), srwHeat 1 j 0 := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨s, hs, rfl⟩ := hj
        rw [Finset.mem_Ico] at hs
        rw [Finset.mem_range]
        have h2 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
        omega
      · intro j _ _
        exact srwHeat_nonneg j 0
    have hlow' : ∑ s ∈ Finset.Ico 1 (n / 2), c / Real.sqrt (s : ℝ) ≤
        ∑ s ∈ Finset.Ico 1 (n / 2), srwHeat 1 (2 * s) 0 := by
      refine Finset.sum_le_sum fun s hs => ?_
      rw [Finset.mem_Ico] at hs
      have h := hlow s hs.1
      rw [pow_one] at h
      exact h
    have hc0 : 0 ≤ c := hc.le
    have hsum2 : c * (Real.sqrt ((n / 2 : ℕ) : ℝ) / 2) ≤
        ∑ s ∈ Finset.Ico 1 (n / 2), c / Real.sqrt (s : ℝ) := by
      have h1 : c * (Real.sqrt ((n / 2 : ℕ) : ℝ) / 2)
          ≤ c * ∑ s ∈ Finset.Ico 1 (n / 2), (Real.sqrt (s : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hc0
      have h2 : c * ∑ s ∈ Finset.Ico 1 (n / 2), (Real.sqrt (s : ℝ))⁻¹
          = ∑ s ∈ Finset.Ico 1 (n / 2), c / Real.sqrt (s : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [div_eq_mul_inv]
      linarith [h1, h2.le, h2.ge]
    have hsqrt : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt ((n / 2 : ℕ) : ℝ) := by
      have h4 : Real.sqrt ((n : ℝ) / 4) = Real.sqrt (n : ℝ) / 2 := by
        rw [Real.sqrt_div' (n : ℝ) (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
      rw [← h4]
      exact Real.sqrt_le_sqrt (by
        have h2 : n ≤ 4 * (n / 2) := by omega
        have h3 : (n : ℝ) ≤ 4 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h2
        linarith)
    calc min (c / 4) (1 / 2) * Real.sqrt (n : ℝ)
        ≤ c / 4 * Real.sqrt (n : ℝ) := by
          exact mul_le_mul_of_nonneg_right hmin (Real.sqrt_nonneg _)
      _ = c * (Real.sqrt (n : ℝ) / 2) / 2 := by ring
      _ ≤ c * Real.sqrt ((n / 2 : ℕ) : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_left hsqrt hc0
        linarith
      _ = c * (Real.sqrt ((n / 2 : ℕ) : ℝ) / 2) := by ring
      _ ≤ ∑ s ∈ Finset.Ico 1 (n / 2), c / Real.sqrt (s : ℝ) := hsum2
      _ ≤ ∑ s ∈ Finset.Ico 1 (n / 2), srwHeat 1 (2 * s) 0 := hlow'
      _ ≤ srwGreen 1 n 0 := hstep


/-- The max-norm of the truncated Green function is at least the diagonal value. -/
theorem le_srwGreen_sup (d n : ℕ) : srwGreen d n 0 ≤ ⨆ x : Site d, srwGreen d n x := by
  have hb : BddAbove (Set.range fun x : Site d => srwGreen d n x) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨0, ?_⟩
      rintro y ⟨x, rfl⟩
      simp
    · rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        refine ⟨srwGreen 0 n 0, ?_⟩
        rintro y ⟨x, rfl⟩
        rw [Subsingleton.elim x 0]
      · rcases Nat.lt_or_ge d 3 with hd2 | hd3
        · interval_cases d
          · refine ⟨1 + 2 * (Real.sqrt 2 * greenConst 1) * Real.sqrt (n : ℝ), ?_⟩
            rintro y ⟨x, rfl⟩
            exact srwGreen_one_dim_le n hn x
          · refine ⟨1 + (Real.sqrt 2 ^ 2 * greenConst 2) * (1 + Real.log (n : ℝ)), ?_⟩
            rintro y ⟨x, rfl⟩
            exact srwGreen_two_dim_le n hn x
        · refine ⟨1 + 3 * (Real.sqrt 2 ^ d * greenConst d), ?_⟩
          rintro y ⟨x, rfl⟩
          exact srwGreen_high_dim_le hd3 n hn x
  exact le_ciSup hb 0

/-- The max-norm of the truncated Green function is at least `c √n` in one dimension. -/
theorem exists_le_srwGreen_sup_one_dim :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) ≤ ⨆ x : Site 1, srwGreen 1 n x := by
  obtain ⟨c, hc, h⟩ := exists_le_srwGreen_one_dim
  exact ⟨c, hc, fun n hn => le_trans (h n hn) (le_srwGreen_sup 1 n)⟩

/-- The max-norm of the truncated Green function is at least `c log n` in two dimensions. -/
theorem exists_le_srwGreen_sup_two_dim :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → c * Real.log (n : ℝ) ≤ ⨆ x : Site 2, srwGreen 2 n x := by
  obtain ⟨c, hc, h⟩ := exists_le_srwGreen_two_dim
  exact ⟨c, hc, fun n hn => le_trans (h n hn) (le_srwGreen_sup 2 n)⟩


/-- The max-norm of the truncated Green function is at least `1` in dimension at least three. -/
theorem exists_le_srwGreen_sup_high_dim (d : ℕ) (_hd : 3 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c ≤ ⨆ x : Site d, srwGreen d n x := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  have h1 : (1 : ℝ) ≤ srwGreen d n 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact one_le_srwGreen_origin m
  exact le_trans h1 (le_srwGreen_sup d n)


end LatticeProb
