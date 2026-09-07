/-
The correlation of two truncated Green functions, `eq:corr-bound`.

`LatticeProb/Walk/GreenSq.lean` makes `∑_y g_m(y) g_n(y)` the double sum
`∑_{a<m} ∑_{b<n} p_{a+b}(0,0)`.  Grouping by `s = a+b` and using that the number
of pairs at level `s` is at most `min(s+1, m)`, the double sum splits at the
smaller horizon into

  `∑_{s<m} (s+1) p_s(0,0)`  and  `m · ∑_{m ≤ s < m+n} p_s(0,0)`,

and the four dimensional regimes of `sandpile.tex` are the four regimes of those
two elementary sums.  The comparison with `√(V_m V_n)` is then EXACT rather than
asymptotic: with `ρ'_d` the rate of `eq:Qt-table` modified at `d = 4` to
`1 + log t` (so that it is positive at `t = 1` as well),

  `corrRate d m n · √(ρ'_d(m)) · √(ρ'_d(n))`

equals `m√n`, `m(1+log(n/m))`, `√m` and `1 + log m` in dimensions one to four,
which is exactly what the two sums above give.  That identity is what makes the
whole clause four lines of algebra once the sums are estimated.
-/
import LatticeProb.Walk.WindowD4

noncomputable section

namespace LatticeProb

variable {d : ℕ}

/-! ### Two more elementary sums over an interval -/

/-- Telescoping of `1/√s - 1/√(s+1)` over an interval. -/
theorem sum_Ico_inv_sqrt_telescope {m : ℕ} (hm : 1 ≤ m) :
    ∀ N : ℕ, m ≤ N →
      ∑ s ∈ Finset.Ico m N, ((Real.sqrt (s : ℝ))⁻¹ - (Real.sqrt ((s : ℝ) + 1))⁻¹)
        = (Real.sqrt (m : ℝ))⁻¹ - (Real.sqrt (N : ℝ))⁻¹ := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
      intro h
      rcases Nat.lt_or_ge m (N + 1) with hlt | hge
      · have hmN : m ≤ N := by omega
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [Finset.sum_Ico_succ_top hmN, ih hmN, hcast]
        ring
      · have hmN : m = N + 1 := by omega
        subst hmN
        rw [Finset.Ico_self, Finset.sum_empty]
        ring

/-- `∑_{m ≤ s < N} s^{-3/2} ≤ 6/√m`, in the form `(s √s)⁻¹`. -/
theorem sum_Ico_inv_mul_sqrt_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, (((s : ℝ)) * Real.sqrt (s : ℝ))⁻¹ ≤ 6 / Real.sqrt (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  rcases Nat.lt_or_ge N m with hlt | hge
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hterm : ∀ s ∈ Finset.Ico m N,
        (((s : ℝ)) * Real.sqrt (s : ℝ))⁻¹
          ≤ 6 * ((Real.sqrt (s : ℝ))⁻¹ - (Real.sqrt ((s : ℝ) + 1))⁻¹) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast le_trans hm hs.1
      have hspos : (0 : ℝ) < (s : ℝ) := by linarith
      set u := Real.sqrt (s : ℝ) with hu
      set v := Real.sqrt ((s : ℝ) + 1) with hv
      have hu2 : u ^ 2 = (s : ℝ) := Real.sq_sqrt hspos.le
      have hv2 : v ^ 2 = (s : ℝ) + 1 := Real.sq_sqrt (by linarith)
      have hu0 : 0 < u := Real.sqrt_pos.mpr hspos
      have hv0 : 0 < v := Real.sqrt_pos.mpr (by linarith)
      have hu1 : 1 ≤ u := by nlinarith
      have huv : u < v := by nlinarith
      have h2uv : v ≤ 2 * u := by nlinarith
      have hdiff : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
        field_simp
      have hvu : (v - u) * (v + u) = 1 := by nlinarith
      rw [hdiff, ← hu2, inv_eq_one_div, div_le_iff₀ (by positivity)]
      have hexp : 6 * ((v - u) / (u * v)) * (u ^ 2 * u) = 6 * (v - u) * u ^ 2 / v := by
        field_simp
      rw [hexp, le_div_iff₀ hv0]
      nlinarith [hvu, hu0, hv0, h2uv, hu1, mul_pos hu0 hv0]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, sum_Ico_inv_sqrt_telescope hm N hge]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hpos : (0 : ℝ) < (Real.sqrt (N : ℝ))⁻¹ := by positivity
    rw [div_eq_mul_inv]
    linarith

/-- `∑_{m ≤ s < N} s^{-1/2} ≤ 2√N`. -/
theorem sum_Ico_inv_sqrt_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, (Real.sqrt (s : ℝ))⁻¹ ≤ 2 * Real.sqrt (N : ℝ) := by
  have hsub : ∑ s ∈ Finset.Ico m N, (Real.sqrt (s : ℝ))⁻¹
      ≤ ∑ s ∈ Finset.Ico 1 N, (Real.sqrt (s : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s _ _ => by positivity)
    intro s hs
    rw [Finset.mem_Ico] at hs ⊢
    omega
  refine hsub.trans ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hre : ∑ s ∈ Finset.Ico 1 N, (Real.sqrt (s : ℝ))⁻¹
        = ∑ r ∈ Finset.range (N - 1), (1 : ℝ) / Real.sqrt ((r : ℝ) + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hcast : ((1 + r : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
      rw [hcast, one_div]
    rw [hre]
    refine (sum_inv_sqrt_le (N - 1)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
    have : N - 1 ≤ N := by omega
    exact_mod_cast this

/-! ### The structural split of the correlation -/

/-- The part of the double sum below the smaller horizon. -/
theorem sum_range_succ_srwHeat_le (hd : 0 < d) (m : ℕ) :
    ∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat d s 0
      ≤ 1 + 2 * diagConst d * diagSum d m := by
  have hK := (diagConst_pos d).le
  have hDS : 0 ≤ diagSum d m := by
    rw [diagSum]
    exact Finset.sum_nonneg fun s _ => by positivity
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Finset.range_zero, Finset.sum_empty]
    nlinarith
  · have hsplit : ∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat d s 0
        = ((0 : ℝ) + 1) * srwHeat d 0 0 + ∑ s ∈ Finset.Ico 1 m, ((s : ℝ) + 1) * srwHeat d s 0 := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
      norm_num
    rw [hsplit]
    have h0 : ((0 : ℝ) + 1) * srwHeat d 0 (0 : Site d) = 1 := by
      rw [srwHeat_zero, if_pos rfl]
      ring
    rw [h0]
    have hterm : ∀ s ∈ Finset.Ico 1 m,
        ((s : ℝ) + 1) * srwHeat d s 0
          ≤ 2 * diagConst d * ((s : ℝ) / Real.sqrt s ^ d) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      have hs1 : 1 ≤ s := hs.1
      have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
      have hpow : (0 : ℝ) < Real.sqrt (s : ℝ) ^ d := pow_pos (Real.sqrt_pos.mpr hspos) d
      have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have h2 : srwHeat d s 0 ≤ diagConst d / Real.sqrt s ^ d := srwHeat_diag_le hd hs1
      have h3 : (0 : ℝ) ≤ srwHeat d s 0 := srwHeat_nonneg s 0
      have h4 : ((s : ℝ) + 1) ≤ 2 * (s : ℝ) := by linarith
      have h5 : (0 : ℝ) ≤ diagConst d / Real.sqrt s ^ d := by positivity
      calc ((s : ℝ) + 1) * srwHeat d s 0 ≤ (2 * (s : ℝ)) * (diagConst d / Real.sqrt s ^ d) := by
            nlinarith
        _ = 2 * diagConst d * ((s : ℝ) / Real.sqrt s ^ d) := by field_simp
    have hfin : ∑ s ∈ Finset.Ico 1 m, ((s : ℝ) + 1) * srwHeat d s 0
        ≤ 2 * diagConst d * diagSum d m := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [diagSum, Finset.mul_sum]
    linarith

/-- **The correlation splits at the smaller horizon.** -/
theorem tsum_srwGreen_mul_le_split {m n : ℕ} :
    ∑' y : Site d, srwGreen d m y * srwGreen d n y
      ≤ (∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat d s 0)
        + (m : ℝ) * ∑ s ∈ Finset.Ico m (m + n), srwHeat d s 0 := by
  rw [tsum_srwGreen_mul, sum_sum_add_eq m n (fun s => srwHeat d s 0)]
  have hsplit : Finset.range (m + n) = Finset.range m ∪ Finset.Ico m (m + n) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdisj : Disjoint (Finset.range m) (Finset.Ico m (m + n)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_range] at hs
    rw [Finset.mem_Ico] at hs'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun s _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (srwHeat_nonneg s 0)
    have := pairCount_le m n s
    have h1 : pairCount m n s ≤ s + 1 := le_trans this (min_le_left _ _)
    exact_mod_cast h1
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (srwHeat_nonneg s 0)
    have := pairCount_le m n s
    have h1 : pairCount m n s ≤ m := le_trans this (min_le_right _ _)
    exact_mod_cast h1

/-- The tail of the kernel over a window, in the `√s ^ d` form. -/
theorem sum_Ico_srwHeat_le (hd : 0 < d) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, srwHeat d s 0
      ≤ diagConst d * ∑ s ∈ Finset.Ico m N, (Real.sqrt (s : ℝ) ^ d)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Finset.mem_Ico] at hs
  have hs1 : 1 ≤ s := le_trans hm hs.1
  have h := srwHeat_diag_le hd hs1
  rwa [div_eq_mul_inv] at h

/-! ### The rate of `eq:corr-bound`, and the exact product identity -/

/-- The `d`-dependent rate of `eq:corr-bound` (`sandpile.tex:1206-1217`):
`(1+log(n/m))√(m/n)` in dimension two, `√((1+log m)/(1+log n))` in dimension
four, and `(m/n)^{1/4}` in dimensions one and three. -/
def corrRate (d : ℕ) (m n : ℕ) : ℝ :=
  if d = 2 then (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ))
  else if d = 4 then Real.sqrt ((1 + Real.log (m : ℝ)) / (1 + Real.log (n : ℝ)))
  else ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4)

/-- The rate of `eq:Qt-table`, modified in dimension four to `1 + log t`, so
that it is positive at `t = 1` too.  It agrees with `varianceRate` up to a
constant on `t ≥ 2`, and the correlation bound is cleanest in this form. -/
def corrScale (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then (t : ℝ) * Real.sqrt (t : ℝ)
  else if d = 2 then (t : ℝ)
  else if d = 3 then Real.sqrt (t : ℝ)
  else 1 + Real.log (t : ℝ)

/-- The target of the correlation bound, the product of the rate and the two
scales. -/
def corrTarget (d : ℕ) (m n : ℕ) : ℝ :=
  if d = 1 then (m : ℝ) * Real.sqrt (n : ℝ)
  else if d = 2 then (m : ℝ) * (1 + Real.log ((n : ℝ) / (m : ℝ)))
  else if d = 3 then Real.sqrt (m : ℝ)
  else 1 + Real.log (m : ℝ)

theorem rpow_quarter_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- **The product identity.**  `corrRate · √(corrScale m) · √(corrScale n)` IS
the target, exactly, in each of the four dimensions. -/
theorem corrRate_mul_corrScale {d : ℕ} (hd : 1 ≤ d) (hd4 : d ≤ 4) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    corrRate d m n * Real.sqrt (corrScale d m) * Real.sqrt (corrScale d n)
      = corrTarget d m n := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hq : Real.sqrt (Real.sqrt ((m : ℝ) / (n : ℝ)))
      = Real.sqrt (Real.sqrt (m : ℝ)) / Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_div' _ (by positivity)]
  by_cases h1 : d = 1
  · subst h1
    have hcr : corrRate 1 m n = ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [corrRate, if_neg (by norm_num), if_neg (by norm_num)]
    have hcm : corrScale 1 m = (m : ℝ) * Real.sqrt (m : ℝ) := by rw [corrScale, if_pos rfl]
    have hcn : corrScale 1 n = (n : ℝ) * Real.sqrt (n : ℝ) := by rw [corrScale, if_pos rfl]
    have hct : corrTarget 1 m n = (m : ℝ) * Real.sqrt (n : ℝ) := by
      rw [corrTarget, if_pos rfl]
    rw [hcr, hcm, hcn, hct, rpow_quarter_eq (by positivity), hq]
    set a := Real.sqrt (Real.sqrt (m : ℝ)) with ha
    set b := Real.sqrt (Real.sqrt (n : ℝ)) with hb
    have ha2 : a ^ 2 = Real.sqrt (m : ℝ) := Real.sq_sqrt hsm.le
    have hb2 : b ^ 2 = Real.sqrt (n : ℝ) := Real.sq_sqrt hsn.le
    have hb0 : 0 < b := Real.sqrt_pos.mpr hsn
    have ha4 : a ^ 4 = (m : ℝ) := by
      have h : a ^ 4 = (a ^ 2) ^ 2 := by ring
      rw [h, ha2, Real.sq_sqrt hmpos.le]
    have hsm3 : Real.sqrt ((m : ℝ) * Real.sqrt (m : ℝ)) = a ^ 2 * a := by
      rw [Real.sqrt_mul hmpos.le, ← ha2, Real.sqrt_sq (by positivity)]
    have hsn3 : Real.sqrt ((n : ℝ) * Real.sqrt (n : ℝ)) = b ^ 2 * b := by
      rw [Real.sqrt_mul hnpos.le, ← hb2, Real.sqrt_sq (by positivity)]
    rw [hsm3, hsn3, ← ha4, ← hb2]
    field_simp
  by_cases h2 : d = 2
  · subst h2
    have hcr : corrRate 2 m n
        = (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ)) := by
      rw [corrRate, if_pos rfl]
    have hcm : corrScale 2 m = (m : ℝ) := by
      rw [corrScale, if_neg (by norm_num), if_pos rfl]
    have hcn : corrScale 2 n = (n : ℝ) := by
      rw [corrScale, if_neg (by norm_num), if_pos rfl]
    have hct : corrTarget 2 m n = (m : ℝ) * (1 + Real.log ((n : ℝ) / (m : ℝ))) := by
      rw [corrTarget, if_neg (by norm_num), if_pos rfl]
    rw [hcr, hcm, hcn, hct]
    have hsq : Real.sqrt ((m : ℝ) / (n : ℝ)) * Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)
        = (m : ℝ) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
        show (m : ℝ) / (n : ℝ) * (m : ℝ) * (n : ℝ) = (m : ℝ) ^ 2 by field_simp]
      exact Real.sqrt_sq hmpos.le
    calc (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ))
          * Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)
        = (1 + Real.log ((n : ℝ) / (m : ℝ)))
            * (Real.sqrt ((m : ℝ) / (n : ℝ)) * Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ)) := by
          ring
      _ = (m : ℝ) * (1 + Real.log ((n : ℝ) / (m : ℝ))) := by rw [hsq]; ring
  by_cases h3 : d = 3
  · subst h3
    have hcr : corrRate 3 m n = ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [corrRate, if_neg (by norm_num), if_neg (by norm_num)]
    have hcm : corrScale 3 m = Real.sqrt (m : ℝ) := by
      rw [corrScale, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    have hcn : corrScale 3 n = Real.sqrt (n : ℝ) := by
      rw [corrScale, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    have hct : corrTarget 3 m n = Real.sqrt (m : ℝ) := by
      rw [corrTarget, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    rw [hcr, hcm, hcn, hct, rpow_quarter_eq (by positivity), hq]
    set a := Real.sqrt (Real.sqrt (m : ℝ)) with ha
    set b := Real.sqrt (Real.sqrt (n : ℝ)) with hb
    have ha2 : a ^ 2 = Real.sqrt (m : ℝ) := Real.sq_sqrt hsm.le
    have hb0 : 0 < b := Real.sqrt_pos.mpr hsn
    rw [← ha2]
    field_simp
  · have h4 : d = 4 := by omega
    subst h4
    have hlm : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hln : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hcr : corrRate 4 m n
        = Real.sqrt ((1 + Real.log (m : ℝ)) / (1 + Real.log (n : ℝ))) := by
      rw [corrRate, if_neg (by norm_num), if_pos rfl]
    have hcm : corrScale 4 m = 1 + Real.log (m : ℝ) := by
      rw [corrScale, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
    have hcn : corrScale 4 n = 1 + Real.log (n : ℝ) := by
      rw [corrScale, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
    have hct : corrTarget 4 m n = 1 + Real.log (m : ℝ) := by
      rw [corrTarget, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
    rw [hcr, hcm, hcn, hct, Real.sqrt_div' _ (by linarith)]
    have hsn4 : (0 : ℝ) < Real.sqrt (1 + Real.log (n : ℝ)) :=
      Real.sqrt_pos.mpr (by linarith)
    have hstep : Real.sqrt (1 + Real.log (m : ℝ)) / Real.sqrt (1 + Real.log (n : ℝ))
        * Real.sqrt (1 + Real.log (m : ℝ)) * Real.sqrt (1 + Real.log (n : ℝ))
        = Real.sqrt (1 + Real.log (m : ℝ)) * Real.sqrt (1 + Real.log (m : ℝ)) := by
      field_simp
    rw [hstep, Real.mul_self_sqrt (by linarith)]

/-! ### The scale is comparable with the variance -/

theorem tsum_srwGreen_one_sq : ∑' y : Site d, srwGreen d 1 y ^ 2 = 1 := by
  have hfun : (fun y : Site d => srwGreen d 1 y ^ 2)
      = fun y : Site d => if y = 0 then (1 : ℝ) else 0 := by
    funext y
    rw [srwGreen, Finset.sum_range_one, srwHeat_zero]
    by_cases h : y = 0
    · simp [h]
    · simp [h]
  rw [hfun]
  exact tsum_ite_eq (0 : Site d) (fun _ => (1 : ℝ))

theorem corrScale_one_eq (_hd4 : d ≤ 4) : corrScale d 1 = 1 := by
  rw [corrScale]
  split_ifs <;> simp

theorem corrScale_le_varianceRate {t : ℕ} (ht : 2 ≤ t) (hd : 1 ≤ d) (hd4 : d ≤ 4) :
    corrScale d t ≤ (1 + 1 / Real.log 2) * varianceRate d t := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlogt : Real.log 2 ≤ Real.log (t : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hA : (1 : ℝ) ≤ 1 + 1 / Real.log 2 := by
    have : (0 : ℝ) < 1 / Real.log 2 := by positivity
    linarith
  by_cases h1 : d = 1
  · subst h1
    rw [corrScale, if_pos rfl, varianceRate, if_pos rfl,
      show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add htpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    nlinarith [hA, mul_nonneg htpos.le (Real.sqrt_nonneg (t : ℝ))]
  by_cases h2 : d = 2
  · subst h2
    rw [corrScale, if_neg (by norm_num), if_pos rfl, varianceRate, if_neg (by norm_num),
      if_pos rfl]
    nlinarith [hA, htpos]
  by_cases h3 : d = 3
  · subst h3
    rw [corrScale, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, varianceRate,
      if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, ← Real.sqrt_eq_rpow]
    nlinarith [hA, Real.sqrt_nonneg (t : ℝ)]
  · have h4 : d = 4 := by omega
    subst h4
    rw [corrScale, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
      varianceRate, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
      if_pos rfl]
    have hkey : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (t : ℝ) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hlog2, one_mul]
      exact hlogt
    nlinarith [hkey]

/-- **The scale is a lower bound for the variance at every `t ≥ 1`**, including
`t = 1`, where the dimension-four rate `log t` vanishes but `1 + log t` does not. -/
theorem exists_le_tsum_srwGreen_sq_corrScale (hd : 1 ≤ d) (hd4 : d ≤ 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 1 ≤ t →
      c * corrScale d t ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_le_tsum_srwGreen_sq hd
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := 1 + 1 / Real.log 2 with hA
  have hApos : (0 : ℝ) < A := by rw [hA]; positivity
  refine ⟨min (c₀ / A) 1, by positivity, fun t ht => ?_⟩
  have hcs : 0 ≤ corrScale d t := by
    rw [corrScale]
    split_ifs with e1 e2 e3
    · positivity
    · positivity
    · positivity
    · have : (0 : ℝ) ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht)
      linarith
  rcases Nat.lt_or_ge t 2 with hlt | hge
  · have ht1 : t = 1 := by omega
    subst ht1
    rw [corrScale_one_eq hd4, tsum_srwGreen_one_sq, mul_one]
    exact min_le_right _ _
  · have h1 := hlow t hge
    have h2 := corrScale_le_varianceRate hge hd hd4
    have hrn : 0 ≤ varianceRate d t := varianceRate_nonneg d hge
    have hstep : c₀ / A * corrScale d t ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hApos]
      nlinarith
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hcs) hstep

/-! ### The tail of the kernel, dimension by dimension -/

theorem sum_Ico_srwHeat_one_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, srwHeat 1 s 0 ≤ diagConst 1 * (2 * Real.sqrt (N : ℝ)) := by
  refine (sum_Ico_srwHeat_le (by norm_num) hm N).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (diagConst_pos 1).le
  have hcongr : ∀ s ∈ Finset.Ico m N,
      (Real.sqrt (s : ℝ) ^ 1)⁻¹ = (Real.sqrt (s : ℝ))⁻¹ := fun s _ => by rw [pow_one]
  rw [Finset.sum_congr rfl hcongr]
  exact sum_Ico_inv_sqrt_le hm N

theorem sum_Ico_srwHeat_two_le {m : ℕ} (hm : 1 ≤ m) {N : ℕ} (hmN : m ≤ N) :
    ∑ s ∈ Finset.Ico m N, srwHeat 2 s 0
      ≤ diagConst 2 * (2 * (Real.log (N : ℝ) - Real.log (m : ℝ))) := by
  refine (sum_Ico_srwHeat_le (by norm_num) hm N).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (diagConst_pos 2).le
  have hcongr : ∀ s ∈ Finset.Ico m N, (Real.sqrt (s : ℝ) ^ 2)⁻¹ = ((s : ℝ))⁻¹ := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    rw [Real.sq_sqrt hspos.le]
  rw [Finset.sum_congr rfl hcongr]
  exact sum_Ico_inv_le hm hmN

theorem sum_Ico_srwHeat_three_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, srwHeat 3 s 0
      ≤ diagConst 3 * (6 / Real.sqrt (m : ℝ)) := by
  refine (sum_Ico_srwHeat_le (by norm_num) hm N).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (diagConst_pos 3).le
  have hcongr : ∀ s ∈ Finset.Ico m N,
      (Real.sqrt (s : ℝ) ^ 3)⁻¹ = ((s : ℝ) * Real.sqrt (s : ℝ))⁻¹ := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    rw [sqrt_pow_three _ hspos.le]
  rw [Finset.sum_congr rfl hcongr]
  exact sum_Ico_inv_mul_sqrt_le hm N

theorem sum_Ico_srwHeat_four_le {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ s ∈ Finset.Ico m N, srwHeat 4 s 0 ≤ diagConst 4 * (2 / (m : ℝ)) := by
  refine (sum_Ico_srwHeat_le (by norm_num) hm N).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (diagConst_pos 4).le
  have hcongr : ∀ s ∈ Finset.Ico m N,
      (Real.sqrt (s : ℝ) ^ 4)⁻¹ = (((s : ℝ)) ^ 2)⁻¹ := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    rw [sqrt_pow_four _ hspos.le]
  rw [Finset.sum_congr rfl hcongr]
  exact sum_Ico_inv_sq_le hm N

/-! ### The correlation against the target -/

/-- **The correlation is at most a constant times the target.** -/
theorem exists_tsum_srwGreen_mul_le_target (hd : 1 ≤ d) (hd4 : d ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → m ≤ n →
      ∑' y : Site d, srwGreen d m y * srwGreen d n y ≤ C * corrTarget d m n := by
  by_cases h1 : d = 1
  · subst h1
    have hK : 0 < diagConst 1 := diagConst_pos 1
    refine ⟨1 + 6 * diagConst 1, by linarith, fun m n hm hmn => ?_⟩
    have hn : 1 ≤ n := le_trans hm hmn
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hsm : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hmR
    have hsn : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnR
    have hsmn : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hmnR
    set P1 : ℝ := ∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat 1 s 0 with hP1def
    set P2 : ℝ := ∑ s ∈ Finset.Ico m (m + n), srwHeat 1 s 0 with hP2def
    have hsplit := tsum_srwGreen_mul_le_split (d := 1) (m := m) (n := n)
    have hP1 := sum_range_succ_srwHeat_le (d := 1) (by norm_num) m
    have hDS := diagSum_one_le m
    have hP2 := sum_Ico_srwHeat_one_le hm (m + n)
    have hsq : Real.sqrt ((m + n : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
      have h4 : ((m + n : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by push_cast; linarith
      have hh := Real.sqrt_le_sqrt h4
      rwa [show (4 : ℝ) * (n : ℝ) = 2 ^ 2 * (n : ℝ) by norm_num,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at hh
    have hct : corrTarget 1 m n = (m : ℝ) * Real.sqrt (n : ℝ) := by
      rw [corrTarget, if_pos rfl]
    rw [hct]
    have hstep1 : P1 ≤ 1 + 2 * diagConst 1 * ((m : ℝ) * Real.sqrt (m : ℝ)) := by
      refine hP1.trans ?_
      have := mul_le_mul_of_nonneg_left hDS (show (0 : ℝ) ≤ 2 * diagConst 1 by linarith)
      linarith
    have hstep2 : P2 ≤ 4 * diagConst 1 * Real.sqrt (n : ℝ) := by
      refine hP2.trans ?_
      have := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 2 * diagConst 1 by linarith)
      linarith
    have hstep3 : (m : ℝ) * P2 ≤ 4 * diagConst 1 * ((m : ℝ) * Real.sqrt (n : ℝ)) := by
      calc (m : ℝ) * P2 ≤ (m : ℝ) * (4 * diagConst 1 * Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hstep2 (by linarith)
        _ = 4 * diagConst 1 * ((m : ℝ) * Real.sqrt (n : ℝ)) := by ring
    have hmono : (m : ℝ) * Real.sqrt (m : ℝ) ≤ (m : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsmn (by linarith)
    have hstep4 : 2 * diagConst 1 * ((m : ℝ) * Real.sqrt (m : ℝ))
        ≤ 2 * diagConst 1 * ((m : ℝ) * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    have hone : (1 : ℝ) ≤ (m : ℝ) * Real.sqrt (n : ℝ) := by nlinarith
    nlinarith [hsplit, hstep1, hstep3, hstep4, hone]
  by_cases h2 : d = 2
  · subst h2
    have hK : 0 < diagConst 2 := diagConst_pos 2
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    refine ⟨1 + 2 * diagConst 2 * (2 + Real.log 2), by nlinarith, fun m n hm hmn => ?_⟩
    have hn : 1 ≤ n := le_trans hm hmn
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    set L : ℝ := Real.log ((n : ℝ) / (m : ℝ)) with hLdef
    have hL : (0 : ℝ) ≤ L := Real.log_nonneg ((one_le_div hmpos).mpr hmnR)
    have hLeq : L = Real.log (n : ℝ) - Real.log (m : ℝ) := Real.log_div hnpos.ne' hmpos.ne'
    set P1 : ℝ := ∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat 2 s 0 with hP1def
    set P2 : ℝ := ∑ s ∈ Finset.Ico m (m + n), srwHeat 2 s 0 with hP2def
    have hsplit := tsum_srwGreen_mul_le_split (d := 2) (m := m) (n := n)
    have hP1 := sum_range_succ_srwHeat_le (d := 2) (by norm_num) m
    have hDS := diagSum_two_le m
    have hP2 := sum_Ico_srwHeat_two_le hm (le_trans hmn (by omega : n ≤ m + n))
    have hlog : Real.log ((m + n : ℕ) : ℝ) - Real.log (m : ℝ) ≤ Real.log 2 + L := by
      have hc : ((m + n : ℕ) : ℝ) = (m : ℝ) + (n : ℝ) := by push_cast; ring
      rw [hc, hLeq]
      have hle : Real.log ((m : ℝ) + (n : ℝ)) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hnpos.ne'] at hle
      linarith
    have hct : corrTarget 2 m n = (m : ℝ) * (1 + L) := by
      rw [corrTarget, if_neg (by norm_num), if_pos rfl]
    rw [hct]
    have hstep1 : P1 ≤ 1 + 2 * diagConst 2 * (m : ℝ) := by
      refine hP1.trans ?_
      have := mul_le_mul_of_nonneg_left hDS (show (0 : ℝ) ≤ 2 * diagConst 2 by linarith)
      linarith
    have hstep2 : P2 ≤ 2 * diagConst 2 * (Real.log 2 + L) := by
      refine hP2.trans ?_
      have := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 2 * diagConst 2 by linarith)
      linarith
    have hstep3 : (m : ℝ) * P2
        ≤ 2 * diagConst 2 * (Real.log 2 * (m : ℝ) + (m : ℝ) * L) := by
      calc (m : ℝ) * P2 ≤ (m : ℝ) * (2 * diagConst 2 * (Real.log 2 + L)) :=
            mul_le_mul_of_nonneg_left hstep2 (by linarith)
        _ = 2 * diagConst 2 * (Real.log 2 * (m : ℝ) + (m : ℝ) * L) := by ring
    have hmL : (0 : ℝ) ≤ (m : ℝ) * L := by positivity
    have hgoal : 1 + 2 * diagConst 2 * (m : ℝ)
          + 2 * diagConst 2 * (Real.log 2 * (m : ℝ) + (m : ℝ) * L)
        ≤ (1 + 2 * diagConst 2 * (2 + Real.log 2)) * ((m : ℝ) * (1 + L)) := by
      have e1 : (0 : ℝ) ≤ diagConst 2 * (m : ℝ) := by positivity
      have e2 : (0 : ℝ) ≤ diagConst 2 * ((m : ℝ) * L) := by positivity
      have e3 : (0 : ℝ) ≤ diagConst 2 * Real.log 2 * ((m : ℝ) * L) := by positivity
      nlinarith [hmR, hmL, e1, e2, e3]
    linarith [hsplit, hstep1, hstep3, hgoal]
  by_cases h3 : d = 3
  · subst h3
    have hK : 0 < diagConst 3 := diagConst_pos 3
    refine ⟨1 + 10 * diagConst 3, by linarith, fun m n hm hmn => ?_⟩
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hsm : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hmR
    have hsm2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
    set P1 : ℝ := ∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat 3 s 0 with hP1def
    set P2 : ℝ := ∑ s ∈ Finset.Ico m (m + n), srwHeat 3 s 0 with hP2def
    have hsplit := tsum_srwGreen_mul_le_split (d := 3) (m := m) (n := n)
    have hP1 := sum_range_succ_srwHeat_le (d := 3) (by norm_num) m
    have hDS := diagSum_three_le m
    have hP2 := sum_Ico_srwHeat_three_le hm (m + n)
    have hct : corrTarget 3 m n = Real.sqrt (m : ℝ) := by
      rw [corrTarget, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    rw [hct]
    have hstep1 : P1 ≤ 1 + 4 * diagConst 3 * Real.sqrt (m : ℝ) := by
      refine hP1.trans ?_
      have := mul_le_mul_of_nonneg_left hDS (show (0 : ℝ) ≤ 2 * diagConst 3 by linarith)
      linarith
    have hmul : (m : ℝ) * (diagConst 3 * (6 / Real.sqrt (m : ℝ)))
        = 6 * diagConst 3 * Real.sqrt (m : ℝ) := by
      have hsmpos : (0 : ℝ) < Real.sqrt (m : ℝ) := by linarith
      field_simp
      nlinarith [hsm2]
    have hstep3 : (m : ℝ) * P2 ≤ 6 * diagConst 3 * Real.sqrt (m : ℝ) := by
      calc (m : ℝ) * P2 ≤ (m : ℝ) * (diagConst 3 * (6 / Real.sqrt (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hP2 (by linarith)
        _ = 6 * diagConst 3 * Real.sqrt (m : ℝ) := hmul
    nlinarith [hsplit, hstep1, hstep3, hsm, hK]
  · have h4 : d = 4 := by omega
    subst h4
    have hK : 0 < diagConst 4 := diagConst_pos 4
    refine ⟨1 + 4 * diagConst 4, by linarith, fun m n hm hmn => ?_⟩
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hlm : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    set P1 : ℝ := ∑ s ∈ Finset.range m, ((s : ℝ) + 1) * srwHeat 4 s 0 with hP1def
    set P2 : ℝ := ∑ s ∈ Finset.Ico m (m + n), srwHeat 4 s 0 with hP2def
    have hsplit := tsum_srwGreen_mul_le_split (d := 4) (m := m) (n := n)
    have hP1 := sum_range_succ_srwHeat_le (d := 4) (by norm_num) m
    have hDS := diagSum_four_le m
    have hP2 := sum_Ico_srwHeat_four_le hm (m + n)
    have hct : corrTarget 4 m n = 1 + Real.log (m : ℝ) := by
      rw [corrTarget, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
    rw [hct]
    have hstep1 : P1 ≤ 1 + 2 * diagConst 4 * (1 + Real.log (m : ℝ)) := by
      refine hP1.trans ?_
      have := mul_le_mul_of_nonneg_left hDS (show (0 : ℝ) ≤ 2 * diagConst 4 by linarith)
      linarith
    have hmul : (m : ℝ) * (diagConst 4 * (2 / (m : ℝ))) = 2 * diagConst 4 := by
      field_simp
    have hstep3 : (m : ℝ) * P2 ≤ 2 * diagConst 4 := by
      calc (m : ℝ) * P2 ≤ (m : ℝ) * (diagConst 4 * (2 / (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hP2 (by linarith)
        _ = 2 * diagConst 4 := hmul
    nlinarith [hsplit, hstep1, hstep3, hlm, hK]

theorem corrRate_nonneg {d m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : 0 ≤ corrRate d m n := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  rw [corrRate]
  split_ifs
  · have hlog : (0 : ℝ) ≤ Real.log ((n : ℝ) / (m : ℝ)) :=
      Real.log_nonneg ((one_le_div hmpos).mpr hmnR)
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  · exact Real.sqrt_nonneg _
  · exact Real.rpow_nonneg (by positivity) _

/-- **`eq:corr-bound`.**  The correlation of two truncated Green functions is at
most a constant times the rate times the two `ℓ²` norms, in dimensions one to
four. -/
theorem exists_tsum_srwGreen_mul_le (hd : 1 ≤ d) (hd4 : d ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → m ≤ n →
      ∑' y : Site d, srwGreen d m y * srwGreen d n y
        ≤ C * corrRate d m n * Real.sqrt (∑' y : Site d, srwGreen d m y ^ 2)
            * Real.sqrt (∑' y : Site d, srwGreen d n y ^ 2) := by
  obtain ⟨C₁, hC₁, hT⟩ := exists_tsum_srwGreen_mul_le_target hd hd4
  obtain ⟨c, hc, hlow⟩ := exists_le_tsum_srwGreen_sq_corrScale hd hd4
  refine ⟨C₁ / c, by positivity, fun m n hm hmn => ?_⟩
  have hn : 1 ≤ n := le_trans hm hmn
  have hcr : 0 ≤ corrRate d m n := corrRate_nonneg hm hmn
  have hsm : Real.sqrt c * Real.sqrt (corrScale d m)
      ≤ Real.sqrt (∑' y : Site d, srwGreen d m y ^ 2) := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt (hlow m hm)
  have hsn : Real.sqrt c * Real.sqrt (corrScale d n)
      ≤ Real.sqrt (∑' y : Site d, srwGreen d n y ^ 2) := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt (hlow n hn)
  have hprod : c * (Real.sqrt (corrScale d m) * Real.sqrt (corrScale d n))
      ≤ Real.sqrt (∑' y : Site d, srwGreen d m y ^ 2)
        * Real.sqrt (∑' y : Site d, srwGreen d n y ^ 2) := by
    have h := mul_le_mul hsm hsn (by positivity) (Real.sqrt_nonneg _)
    have hcs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
    have hcc : Real.sqrt c * Real.sqrt (corrScale d m)
        * (Real.sqrt c * Real.sqrt (corrScale d n))
        = c * (Real.sqrt (corrScale d m) * Real.sqrt (corrScale d n)) := by
      calc Real.sqrt c * Real.sqrt (corrScale d m)
            * (Real.sqrt c * Real.sqrt (corrScale d n))
          = (Real.sqrt c * Real.sqrt c)
              * (Real.sqrt (corrScale d m) * Real.sqrt (corrScale d n)) := by ring
        _ = c * (Real.sqrt (corrScale d m) * Real.sqrt (corrScale d n)) := by rw [hcs]
    rwa [hcc] at h
  have hid := corrRate_mul_corrScale hd hd4 hm hn
  have hstep : C₁ * corrTarget d m n
      ≤ C₁ / c * corrRate d m n * Real.sqrt (∑' y : Site d, srwGreen d m y ^ 2)
          * Real.sqrt (∑' y : Site d, srwGreen d n y ^ 2) := by
    rw [← hid]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
    have hfac : C₁ * corrRate d m n
        * (c * (Real.sqrt (corrScale d m) * Real.sqrt (corrScale d n)))
        = C₁ * (corrRate d m n * Real.sqrt (corrScale d m)
            * Real.sqrt (corrScale d n)) * c := by ring
    nlinarith [mul_le_mul_of_nonneg_left hprod
      (show (0 : ℝ) ≤ C₁ * corrRate d m n by positivity), hfac]
  exact (hT m n hm hmn).trans hstep

end LatticeProb
