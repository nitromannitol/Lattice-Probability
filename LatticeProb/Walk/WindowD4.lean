/-
The dimension-four window estimates.

In dimension four the return probability is of order `s^{-2}`, so the kernel
summed over a window of times `[m, n)` is of order `1/m`, and the `ℓ²` mass of
that window is of order `log(n/m)`.  Both are elementary consequences of the
identity of `LatticeProb/Walk/GreenSq.lean`,

  `∑_z (∑_{a ∈ S} p_a(0,z)) (∑_{b ∈ T} p_b(0,z)) = ∑_{a ∈ S} ∑_{b ∈ T} p_{a+b}(0,0)`,

taken with `S = T = [m, n)`, together with two comparisons of a sum with an
integral over an interval: `∑_{m ≤ k < n} k^{-2} ≤ 2/m` and
`∑_{m ≤ k < n} k^{-1} ≤ 2 log(n/m)`.  Neither is in the library, and the second
is the one whose direction is easy to get wrong: the correct comparison is
`1/(k+1) ≤ log(k+1) - log k`, the left endpoint rule, and the factor two is the
price of reading it at `1/k` instead.
-/
import LatticeProb.Walk.VarianceScale

noncomputable section

namespace LatticeProb

variable {d : ℕ}

/-! ### Two elementary sums over an interval -/

theorem inv_succ_le_log_sub {k : ℕ} (hk : 1 ≤ k) :
    (((k : ℝ) + 1))⁻¹ ≤ Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : (0 : ℝ) < (k : ℝ) / ((k : ℝ) + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos h1
  rw [Real.log_div hkpos.ne' (by positivity)] at h
  have h2 : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(((k : ℝ) + 1))⁻¹ := by
    field_simp
    ring
  rw [h2] at h
  linarith

/-- `∑_{m ≤ k < n} 1/(k+1) ≤ log n - log m`, the left endpoint rule. -/
theorem sum_Ico_inv_succ_le {m : ℕ} (hm : 1 ≤ m) :
    ∀ n : ℕ, m ≤ n →
      ∑ k ∈ Finset.Ico m n, (((k : ℝ) + 1))⁻¹ ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := by omega
        have hn1 : 1 ≤ n := by omega
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [Finset.sum_Ico_succ_top hmn, hcast]
        have := ih hmn
        have hstep := inv_succ_le_log_sub hn1
        linarith
      · have hmn : m = n + 1 := by omega
        subst hmn
        rw [Finset.Ico_self, Finset.sum_empty]
        linarith

/-- `∑_{m ≤ k < n} 1/k ≤ 2 (log n - log m)`. -/
theorem sum_Ico_inv_le {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, ((k : ℝ))⁻¹ ≤ 2 * (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
  have hterm : ∀ k ∈ Finset.Ico m n, ((k : ℝ))⁻¹ ≤ 2 * (((k : ℝ) + 1))⁻¹ := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hm hk.1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hkp1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    calc ((k : ℝ))⁻¹ = 1 / (k : ℝ) := by rw [one_div]
      _ ≤ 2 / ((k : ℝ) + 1) := by
          rw [div_le_div_iff₀ hkpos hkp1]
          linarith
      _ = 2 * (((k : ℝ) + 1))⁻¹ := by rw [div_eq_mul_inv]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have := sum_Ico_inv_succ_le hm n hmn
  linarith

/-- `∑_{m ≤ k < n} 1/k^2 ≤ 2/m`. -/
theorem sum_Ico_inv_sq_le {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    ∑ k ∈ Finset.Ico m n, (((k : ℝ)) ^ 2)⁻¹ ≤ 2 / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htel : ∀ n : ℕ, m ≤ n →
      ∑ k ∈ Finset.Ico m n, (((k : ℝ))⁻¹ - (((k : ℝ) + 1))⁻¹)
        = ((m : ℝ))⁻¹ - (((n : ℝ)))⁻¹ := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
        intro h
        rcases Nat.lt_or_ge m (n + 1) with hlt | hge
        · have hmn : m ≤ n := by omega
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
          rw [Finset.sum_Ico_succ_top hmn, ih hmn, hcast]
          ring
        · have hmn : m = n + 1 := by omega
          subst hmn
          rw [Finset.Ico_self, Finset.sum_empty]
          ring
  rcases Nat.lt_or_ge n m with hlt | hge
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hterm : ∀ k ∈ Finset.Ico m n,
        (((k : ℝ)) ^ 2)⁻¹ ≤ 2 * (((k : ℝ))⁻¹ - (((k : ℝ) + 1))⁻¹) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hm hk.1
      have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
      have hstep : ((k : ℝ))⁻¹ - (((k : ℝ) + 1))⁻¹ = (((k : ℝ)) * ((k : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [hstep]
      have hkp1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      calc (((k : ℝ)) ^ 2)⁻¹ = 1 / ((k : ℝ)) ^ 2 := by rw [one_div]
        _ ≤ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * (((k : ℝ) * ((k : ℝ) + 1)))⁻¹ := by rw [div_eq_mul_inv]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, htel n hge]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    rw [div_eq_mul_inv]
    linarith

/-! ### The window kernel -/

/-- The kernel summed over the window of times `[m, n)`. -/
def srwWindow (d : ℕ) (m n : ℕ) (y : Site d) : ℝ := ∑ k ∈ Finset.Ico m n, srwHeat d k y

theorem srwWindow_nonneg (m n : ℕ) (y : Site d) : 0 ≤ srwWindow d m n y :=
  Finset.sum_nonneg fun k _ => srwHeat_nonneg k y

theorem tsum_srwWindow_sq (m n : ℕ) :
    ∑' y : Site d, srwWindow d m n y ^ 2
      = ∑ a ∈ Finset.Ico m n, ∑ b ∈ Finset.Ico m n, srwHeat d (a + b) 0 := by
  rw [← tsum_sum_srwHeat_mul (Finset.Ico m n) (Finset.Ico m n)]
  exact tsum_congr fun y => by rw [srwWindow, sq]

/-! ### Dimension four -/

theorem srwHeat_four_le {s : ℕ} (hs : 1 ≤ s) (y : Site 4) :
    srwHeat 4 s y ≤ diagConst 4 / ((s : ℝ)) ^ 2 := by
  have h := srwHeat_sup_le (d := 4) (by norm_num) hs y
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  rwa [sqrt_pow_four _ hspos.le] at h

/-- **`eq:d4-window-linfty`**: the window kernel is at most `C/m`. -/
theorem srwWindow_le {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (y : Site 4) :
    srwWindow 4 m n y ≤ 2 * diagConst 4 / (m : ℝ) := by
  have hterm : ∀ k ∈ Finset.Ico m n,
      srwHeat 4 k y ≤ diagConst 4 * (((k : ℝ)) ^ 2)⁻¹ := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : 1 ≤ k := le_trans hm hk.1
    have := srwHeat_four_le hk1 y
    rwa [div_eq_mul_inv] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h := sum_Ico_inv_sq_le hm n
  have hK := (diagConst_pos 4).le
  calc diagConst 4 * ∑ k ∈ Finset.Ico m n, (((k : ℝ)) ^ 2)⁻¹
      ≤ diagConst 4 * (2 / (m : ℝ)) := mul_le_mul_of_nonneg_left h hK
    _ = 2 * diagConst 4 / (m : ℝ) := by ring

/-- **`eq:d4-window-l2`**: the `ℓ²` mass of the window is at most
`C log(n/m)` plus a constant. -/
theorem tsum_srwWindow_sq_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑' y : Site 4, srwWindow 4 m n y ^ 2
      ≤ 4 * diagConst 4 * (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [tsum_srwWindow_sq]
  have hinner : ∀ a ∈ Finset.Ico m n,
      ∑ b ∈ Finset.Ico m n, srwHeat 4 (a + b) 0
        ≤ 2 * diagConst 4 * (((a : ℝ) + (m : ℝ)))⁻¹ := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have ha1 : 1 ≤ a := le_trans hm ha.1
    have hstep : ∀ b ∈ Finset.Ico m n,
        srwHeat 4 (a + b) 0 ≤ diagConst 4 * ((((a + b : ℕ) : ℝ)) ^ 2)⁻¹ := by
      intro b hb
      rw [Finset.mem_Ico] at hb
      have hab : 1 ≤ a + b := by omega
      have := srwHeat_four_le hab (0 : Site 4)
      rwa [div_eq_mul_inv] at this
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum]
    have hre : ∑ b ∈ Finset.Ico m n, ((((a + b : ℕ) : ℝ)) ^ 2)⁻¹
        = ∑ j ∈ Finset.Ico (a + m) (a + n), (((j : ℝ)) ^ 2)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      have hlen : a + n - (a + m) = n - m := by omega
      rw [hlen]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hassoc : a + (m + i) = a + m + i := by omega
      rw [hassoc]
    rw [hre]
    have ham : 1 ≤ a + m := by omega
    have h := sum_Ico_inv_sq_le ham (a + n)
    have hcast : ((a + m : ℕ) : ℝ) = (a : ℝ) + (m : ℝ) := by push_cast; ring
    rw [hcast] at h
    have hK := (diagConst_pos 4).le
    calc diagConst 4 * ∑ j ∈ Finset.Ico (a + m) (a + n), (((j : ℝ)) ^ 2)⁻¹
        ≤ diagConst 4 * (2 / ((a : ℝ) + (m : ℝ))) := mul_le_mul_of_nonneg_left h hK
      _ = 2 * diagConst 4 * (((a : ℝ) + (m : ℝ)))⁻¹ := by rw [div_eq_mul_inv]; ring
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [← Finset.mul_sum]
  have hre2 : ∑ a ∈ Finset.Ico m n, (((a : ℝ) + (m : ℝ)))⁻¹
      = ∑ j ∈ Finset.Ico (2 * m) (n + m), (((j : ℝ)))⁻¹ := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hlen : n + m - 2 * m = n - m := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    push_cast
    ring
  rw [hre2]
  have h2m : 1 ≤ 2 * m := by omega
  have hmn2 : 2 * m ≤ n + m := by omega
  have h := sum_Ico_inv_le h2m hmn2
  have hlog : Real.log ((n + m : ℕ) : ℝ) - Real.log ((2 * m : ℕ) : ℝ)
      ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hc1 : ((n + m : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) := by push_cast; ring
    have hc2 : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [hc1, hc2]
    have hd1 : Real.log ((n : ℝ) + (m : ℝ)) - Real.log (2 * (m : ℝ))
        = Real.log (((n : ℝ) + (m : ℝ)) / (2 * (m : ℝ))) := by
      rw [Real.log_div (by positivity) (by positivity)]
    have hd2 : Real.log (n : ℝ) - Real.log (m : ℝ) = Real.log ((n : ℝ) / (m : ℝ)) := by
      rw [Real.log_div hnpos.ne' hmpos.ne']
    rw [hd1, hd2]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) hmpos]
    have hnm : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith
  have hK := (diagConst_pos 4).le
  calc 2 * diagConst 4 * ∑ j ∈ Finset.Ico (2 * m) (n + m), (((j : ℝ)))⁻¹
      ≤ 2 * diagConst 4 *
          (2 * (Real.log ((n + m : ℕ) : ℝ) - Real.log ((2 * m : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ 2 * diagConst 4 * (2 * (Real.log (n : ℝ) - Real.log (m : ℝ))) := by
        have h2K : (0 : ℝ) ≤ 2 * diagConst 4 := by linarith
        nlinarith
    _ = 4 * diagConst 4 * (Real.log (n : ℝ) - Real.log (m : ℝ)) := by ring

/-- **`eq:d4-full-window-bounds`, the sup half**: the truncated Green function
in dimension four is bounded. -/
theorem srwGreen_four_le (n : ℕ) (y : Site 4) :
    srwGreen 4 n y ≤ 1 + 2 * diagConst 4 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [srwGreen, Finset.range_zero, Finset.sum_empty]
    have := (diagConst_pos 4).le
    linarith
  · have hsplit : srwGreen 4 n y = srwHeat 4 0 y + srwWindow 4 1 n y := by
      rw [srwGreen, srwWindow, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot hn]
    rw [hsplit]
    have h0 : srwHeat 4 0 y ≤ 1 := by
      rw [srwHeat_zero]
      split_ifs <;> norm_num
    have h1 := srwWindow_le (m := 1) le_rfl n y
    rw [Nat.cast_one, div_one] at h1
    linarith

/-- **`eq:d4-full-window-bounds`, the `ℓ²` half**: the truncated Green function
in dimension four has `ℓ²` mass at most `C log(n+2)`. -/
theorem exists_tsum_srwGreen_four_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∑' y : Site 4, srwGreen 4 n y ^ 2 ≤ C * Real.log ((n : ℝ) + 2) := by
  obtain ⟨C, hC, h⟩ := exists_tsum_srwGreen_sq_le (d := 4) (by norm_num)
  refine ⟨C, hC, fun n hn => ?_⟩
  have h1 := h n hn
  rw [varianceRate, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl] at h1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hnpos (by linarith)
  nlinarith

end LatticeProb
