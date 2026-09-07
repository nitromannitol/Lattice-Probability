/-
The variance scale of the truncated Green function: the upper half of the table.

`LatticeProb/Walk/GreenSq.lean` reduces `∑_y g_t(y)^2` to the one-dimensional
sum `∑_{s < 2t} min(s+1, t) p_s(0,0)`, and `LatticeProb/Walk/SRWDiag.lean`
bounds the return probability by `s^{-d/2}`.  What is left is elementary: split
the sum at the horizon `t`, use `min(s+1,t) ≤ 2s` below it and `min(s+1,t) ≤ t`
above it, and read off the five dimensional regimes from

  `∑_{1 ≤ s < t} s^{1-d/2}` and `t^{2-d/2}`,

which are `t^{3/2}`, `t`, `t^{1/2}`, `log t` and `O(1)` in dimensions one to
five and above.  Everything is written with `√s ^ d` in place of `s^{d/2}`, so
that in each fixed dimension the exponent is a natural number and no real power
appears; the two forms agree by `Real.sqrt_eq_rpow`.
-/
import LatticeProb.Walk.GreenSq
import LatticeProb.Walk.SRWGaussBound
import LatticeProb.Walk.Series

noncomputable section

namespace LatticeProb

variable {d : ℕ}

/-- The constant in the on-diagonal upper bound. -/
def diagConst (d : ℕ) : ℝ := 3 ^ d * greenConst d + 1

theorem diagConst_pos (d : ℕ) : 0 < diagConst d := by
  have h := greenConst_nonneg d
  have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
  rw [diagConst]
  nlinarith

/-- **The on-diagonal upper bound at every time**, in the `√s ^ d` form. -/
theorem srwHeat_diag_le (hd : 0 < d) {s : ℕ} (hs : 1 ≤ s) :
    srwHeat d s (0 : Site d) ≤ diagConst d / Real.sqrt s ^ d := by
  have h := srwHeat_gaussian (d := d) hd hs (0 : Site d)
  have hgn : graphNorm (0 : Site d) = 0 := by simp
  rw [hgn] at h
  norm_num at h
  refine h.trans ?_
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hrp : ((s : ℝ)) ^ (-(d : ℝ) / 2) = (Real.sqrt (s : ℝ) ^ d)⁻¹ := by
    rw [neg_div, Real.rpow_neg hspos.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((s : ℝ) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul hspos.le]
    ring_nf
  rw [hrp, div_eq_mul_inv, diagConst]
  have hpos : (0 : ℝ) < Real.sqrt (s : ℝ) ^ d := pow_pos (Real.sqrt_pos.mpr hspos) d
  have hinv : (0 : ℝ) < (Real.sqrt (s : ℝ) ^ d)⁻¹ := inv_pos.mpr hpos
  nlinarith [greenConst_nonneg d, (by positivity : (0:ℝ) ≤ (3:ℝ) ^ d)]

/-- **The Gaussian upper bound off the diagonal too**, in the `√s ^ d` form:
the exponential factor is at most one. -/
theorem srwHeat_sup_le (hd : 0 < d) {s : ℕ} (hs : 1 ≤ s) (y : Site d) :
    srwHeat d s y ≤ diagConst d / Real.sqrt s ^ d := by
  have h := srwHeat_gaussian (d := d) hd hs y
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hexp : Real.exp (-((graphNorm y : ℝ)) ^ 2 / (8 * ((s : ℝ) + 2 * d))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hden : (0 : ℝ) < 8 * ((s : ℝ) + 2 * d) := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden.le
  have hrp : ((s : ℝ)) ^ (-(d : ℝ) / 2) = (Real.sqrt (s : ℝ) ^ d)⁻¹ := by
    rw [neg_div, Real.rpow_neg hspos.le]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((s : ℝ) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul hspos.le]
    ring_nf
  have hpos : (0 : ℝ) < Real.sqrt (s : ℝ) ^ d := pow_pos (Real.sqrt_pos.mpr hspos) d
  have hgc : (0 : ℝ) ≤ 3 ^ d * greenConst d := by
    have := greenConst_nonneg d
    positivity
  have hinv : (0 : ℝ) < (Real.sqrt (s : ℝ) ^ d)⁻¹ := inv_pos.mpr hpos
  refine h.trans ?_
  rw [hrp, div_eq_mul_inv, diagConst]
  have h1 : 3 ^ d * greenConst d * (Real.sqrt (s : ℝ) ^ d)⁻¹
        * Real.exp (-((graphNorm y : ℝ)) ^ 2 / (8 * ((s : ℝ) + 2 * d)))
      ≤ 3 ^ d * greenConst d * (Real.sqrt (s : ℝ) ^ d)⁻¹ :=
    mul_le_of_le_one_right (mul_nonneg hgc hinv.le) hexp
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hinv.le

/-- The one-dimensional sum the variance scale reduces to. -/
def diagSum (d : ℕ) (t : ℕ) : ℝ := ∑ s ∈ Finset.Ico 1 t, (s : ℝ) / Real.sqrt s ^ d

/-- **The master upper bound.**  The variance scale is at most `1` plus a
constant times `2 · diagSum d t + t^2 / √t^d`. -/
theorem tsum_srwGreen_sq_le_master (hd : 0 < d) {t : ℕ} (ht : 1 ≤ t) :
    ∑' y : Site d, srwGreen d t y ^ 2
      ≤ 1 + diagConst d * (2 * diagSum d t + (t : ℝ) ^ 2 / Real.sqrt t ^ d) := by
  refine (tsum_srwGreen_sq_le t).trans ?_
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsplit : Finset.range (2 * t) = Finset.range 1 ∪ Finset.Ico 1 t ∪ Finset.Ico t (2 * t) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega),
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hd1 : Disjoint (Finset.range 1 ∪ Finset.Ico 1 t) (Finset.Ico t (2 * t)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_Ico] at hs'
    rcases Finset.mem_union.mp hs with h | h
    · rw [Finset.mem_range] at h; omega
    · rw [Finset.mem_Ico] at h; omega
  have hd2 : Disjoint (Finset.range 1) (Finset.Ico 1 t) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_range] at hs
    rw [Finset.mem_Ico] at hs'
    omega
  rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2]
  have hzero : ∑ s ∈ Finset.range 1, (min (s + 1) t : ℝ) * srwHeat d s 0 ≤ 1 := by
    rw [Finset.sum_range_one]
    have h0 : srwHeat d 0 (0 : Site d) = 1 := by simp
    rw [h0, mul_one]
    have h1 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
    rw [h1, min_eq_left (by exact_mod_cast ht : (1 : ℝ) ≤ (t : ℝ))]
  have hlow : ∑ s ∈ Finset.Ico 1 t, (min (s + 1) t : ℝ) * srwHeat d s 0
      ≤ diagConst d * (2 * diagSum d t) := by
    rw [diagSum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [Finset.mem_Ico] at hs
    have hs1 : 1 ≤ s := hs.1
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    have hpow : (0 : ℝ) < Real.sqrt (s : ℝ) ^ d := pow_pos (Real.sqrt_pos.mpr hspos) d
    have hmin : (min (s + 1) t : ℝ) ≤ 2 * (s : ℝ) := by
      have : (min (s + 1) t : ℕ) ≤ 2 * s := by omega
      exact_mod_cast this
    calc (min ((s : ℝ) + 1) (t : ℝ)) * srwHeat d s 0
        ≤ (2 * (s : ℝ)) * (diagConst d / Real.sqrt s ^ d) := by
          have h2 : srwHeat d s 0 ≤ diagConst d / Real.sqrt s ^ d := srwHeat_diag_le hd hs1
          have h3 : (0 : ℝ) ≤ srwHeat d s 0 := srwHeat_nonneg s 0
          have h4 : (0 : ℝ) ≤ 2 * (s : ℝ) := by positivity
          nlinarith
      _ = diagConst d * (2 * ((s : ℝ) / Real.sqrt s ^ d)) := by field_simp
  have hhigh : ∑ s ∈ Finset.Ico t (2 * t), (min (s + 1) t : ℝ) * srwHeat d s 0
      ≤ diagConst d * ((t : ℝ) ^ 2 / Real.sqrt t ^ d) := by
    have hpowt : (0 : ℝ) < Real.sqrt (t : ℝ) ^ d := pow_pos (Real.sqrt_pos.mpr htpos) d
    have hterm : ∀ s ∈ Finset.Ico t (2 * t), (min (s + 1) t : ℝ) * srwHeat d s 0
        ≤ (t : ℝ) * (diagConst d / Real.sqrt t ^ d) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      have hs1 : 1 ≤ s := by omega
      have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
      have hst : (t : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs.1
      have hsq : Real.sqrt (t : ℝ) ^ d ≤ Real.sqrt (s : ℝ) ^ d :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hst) d
      have hmin : (min (s + 1) t : ℝ) ≤ (t : ℝ) := by
        have : (min (s + 1) t : ℕ) ≤ t := by omega
        exact_mod_cast this
      refine mul_le_mul hmin ?_ (srwHeat_nonneg s 0) (Nat.cast_nonneg _)
      refine (srwHeat_diag_le hd hs1).trans ?_
      exact div_le_div_of_nonneg_left (diagConst_pos d).le hpowt hsq
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((2 * t - t : ℕ) : ℝ) = (t : ℝ) := by
      have : 2 * t - t = t := by omega
      rw [this]
    rw [hcard]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : (t : ℝ) * ((t : ℝ) * (diagConst d * (Real.sqrt t ^ d)⁻¹))
        = diagConst d * ((t : ℝ) ^ 2 * (Real.sqrt t ^ d)⁻¹) := by ring
    rw [this]
  have hexp : diagConst d * (2 * diagSum d t + (t : ℝ) ^ 2 / Real.sqrt t ^ d)
      = diagConst d * (2 * diagSum d t) + diagConst d * ((t : ℝ) ^ 2 / Real.sqrt t ^ d) := by
    ring
  rw [hexp]
  linarith

/-! ### The five dimensional regimes of the one-dimensional sum -/

theorem sqrt_pow_three (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 3 = x * Real.sqrt x := by
  have h : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x := by ring
    _ = x * Real.sqrt x := by rw [h]

theorem sqrt_pow_four (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 4 = x ^ 2 := by
  have h : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 := by ring
    _ = x ^ 2 := by rw [h]

theorem diagSum_one_le (t : ℕ) : diagSum 1 t ≤ (t : ℝ) * Real.sqrt t := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 t, (s : ℝ) / Real.sqrt s ^ 1 ≤ Real.sqrt t := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hsq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) := Real.sq_sqrt hspos.le
    have hsp : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
    have h1 : (s : ℝ) / Real.sqrt s ^ 1 = Real.sqrt s := by
      rw [pow_one, div_eq_iff hsp.ne']
      nlinarith
    rw [h1]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hs.2.le)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  have : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by
    have : t - 1 ≤ t := by omega
    exact_mod_cast this
  exact this

theorem diagSum_two_le (t : ℕ) : diagSum 2 t ≤ (t : ℝ) := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 t, (s : ℝ) / Real.sqrt s ^ 2 ≤ 1 := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    rw [Real.sq_sqrt hspos.le, div_self hspos.ne']
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have : t - 1 ≤ t := by omega
  exact_mod_cast this

theorem diagSum_three_le (t : ℕ) : diagSum 3 t ≤ 2 * Real.sqrt t := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 t, (s : ℝ) / Real.sqrt s ^ 3
      = 1 / Real.sqrt ((s - 1 : ℕ) + 1 : ℝ) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hcast : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
      have : (s : ℕ) - 1 + 1 = s := by omega
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    rw [hcast, sqrt_pow_three _ hspos.le]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
  have hidx : ∀ i ∈ Finset.range (t - 1),
      1 / Real.sqrt (((1 + i - 1 : ℕ) : ℝ) + 1) = 1 / Real.sqrt ((i : ℝ) + 1) := by
    intro i _
    have : (1 + i - 1 : ℕ) = i := by omega
    rw [this]
  rw [Finset.sum_congr rfl hidx]
  refine (sum_inv_sqrt_le (t - 1)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  have : t - 1 ≤ t := by omega
  exact_mod_cast this

theorem diagSum_four_le (t : ℕ) : diagSum 4 t ≤ 1 + Real.log t := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 t, (s : ℝ) / Real.sqrt s ^ 4 = ((s : ℝ))⁻¹ := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    rw [sqrt_pow_four _ hspos.le]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  exact sum_inv_le_one_add_log t

theorem diagSum_le_three_of_five_le (hd : 5 ≤ d) (t : ℕ) : diagSum d t ≤ 3 := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 t, (s : ℝ) / Real.sqrt s ^ d ≤ (s : ℝ) ^ (-(3 : ℝ) / 2) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs.1
    have hspos : (0 : ℝ) < (s : ℝ) := by linarith
    have hsp1 : (1 : ℝ) ≤ Real.sqrt (s : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hs1
    have hsp : (0 : ℝ) < Real.sqrt (s : ℝ) := by linarith
    have hmono : Real.sqrt (s : ℝ) ^ 5 ≤ Real.sqrt (s : ℝ) ^ d :=
      pow_le_pow_right₀ hsp1 hd
    have hfive : Real.sqrt (s : ℝ) ^ 5 = (s : ℝ) ^ 2 * Real.sqrt (s : ℝ) := by
      have h4 := sqrt_pow_four (s : ℝ) hspos.le
      calc Real.sqrt (s : ℝ) ^ 5 = Real.sqrt (s : ℝ) ^ 4 * Real.sqrt (s : ℝ) := by ring
        _ = (s : ℝ) ^ 2 * Real.sqrt (s : ℝ) := by rw [h4]
    have hrp : (s : ℝ) ^ (-(3 : ℝ) / 2) = ((s : ℝ) * Real.sqrt (s : ℝ))⁻¹ := by
      rw [neg_div, Real.rpow_neg hspos.le]
      congr 1
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hspos,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hrp]
    have hpow5 : (0 : ℝ) < Real.sqrt (s : ℝ) ^ 5 := by positivity
    have hstep : (s : ℝ) / Real.sqrt s ^ d ≤ (s : ℝ) / Real.sqrt s ^ 5 :=
      div_le_div_of_nonneg_left hspos.le hpow5 hmono
    refine hstep.trans ?_
    rw [hfive, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt hspos.le, hsp.le, hs1]
  refine (Finset.sum_le_sum hterm).trans ?_
  exact sum_rpow_three_halves_le t

/-! ### Lower bounds for the one-dimensional sum -/

/-- The harmonic sum dominates the logarithm. -/
theorem log_le_sum_inv (m : ℕ) :
    Real.log (m : ℝ) ≤ ∑ n ∈ Finset.Ico 1 m, ((n : ℝ))⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        rw [Finset.sum_Ico_succ_top hm]
        have hstep : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ ((m : ℝ))⁻¹ := by
          have hdiv : Real.log (((m : ℝ) + 1) / (m : ℝ))
              = Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) :=
            Real.log_div (by linarith) hmpos.ne'
          have hle : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ ((m : ℝ) + 1) / (m : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = ((m : ℝ))⁻¹ := by
            field_simp
            ring
          rw [hdiv, heq] at hle
          exact hle
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith

theorem sum_Ico_cast (m : ℕ) :
    ∑ s ∈ Finset.Ico 1 m, (s : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · rw [Finset.sum_Ico_succ_top hm, ih]
        push_cast
        ring

theorem diagSum_one_ge {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) * Real.sqrt m / 4 ≤ diagSum 1 m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have hterm : ∀ s ∈ Finset.Ico 1 m, (s : ℝ) / Real.sqrt m ≤ (s : ℝ) / Real.sqrt s ^ 1 := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hss : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs.2.le
    have hsp : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
    rw [pow_one]
    exact div_le_div_of_nonneg_left hspos.le hsp (Real.sqrt_le_sqrt hss)
  have hsum : ∑ s ∈ Finset.Ico 1 m, (s : ℝ) / Real.sqrt m
      = ((m : ℝ) * ((m : ℝ) - 1) / 2) / Real.sqrt m := by
    rw [← Finset.sum_div, sum_Ico_cast]
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [hsum, div_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt (m : ℝ))]
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
  nlinarith [hsm.le, hsq, hm2]

theorem diagSum_two_ge {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) / 2 ≤ diagSum 2 m := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 m, (1 : ℝ) = (s : ℝ) / Real.sqrt s ^ 2 := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    rw [Real.sq_sqrt hspos.le, div_self hspos.ne']
  rw [← Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have h : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm1 : 1 ≤ m := by omega
    rw [Nat.cast_sub hm1, Nat.cast_one]
  rw [h]
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

theorem diagSum_three_ge {m : ℕ} (hm : 2 ≤ m) : Real.sqrt m / 2 ≤ diagSum 3 m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 m, (1 : ℝ) / Real.sqrt m ≤ (s : ℝ) / Real.sqrt s ^ 3 := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    have hss : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs.2.le
    have hsp : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
    rw [sqrt_pow_three _ hspos.le]
    have heq : (s : ℝ) / ((s : ℝ) * Real.sqrt s) = 1 / Real.sqrt s := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by norm_num) hsp (Real.sqrt_le_sqrt hss)
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm1 : 1 ≤ m := by omega
    rw [Nat.cast_sub hm1, Nat.cast_one]
  rw [h]
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_one_div, div_mul_eq_mul_div,
    le_div_iff₀ hsm]
  nlinarith [hsm.le, hsq, hm2]

theorem diagSum_four_ge (m : ℕ) : Real.log (m : ℝ) ≤ diagSum 4 m := by
  rw [diagSum]
  have hterm : ∀ s ∈ Finset.Ico 1 m, ((s : ℝ))⁻¹ = (s : ℝ) / Real.sqrt s ^ 4 := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.1
    rw [sqrt_pow_four _ hspos.le]
    field_simp
  rw [← Finset.sum_congr rfl hterm]
  exact log_le_sum_inv m

theorem one_le_diagSum {m : ℕ} (hm : 2 ≤ m) : 1 ≤ diagSum d m := by
  rw [diagSum]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hterm : ∀ s ∈ Finset.Ico 1 m, (0 : ℝ) ≤ (s : ℝ) / Real.sqrt s ^ d := by
    intro s _
    positivity
  refine le_trans ?_ (Finset.single_le_sum hterm h1)
  norm_num

/-! ### The tail term -/

theorem tail_eq_one {t : ℕ} (ht : 1 ≤ t) :
    (t : ℝ) ^ 2 / Real.sqrt t ^ 1 = (t : ℝ) * Real.sqrt t := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsp : (0 : ℝ) < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  rw [pow_one, div_eq_iff hsp.ne']
  nlinarith [Real.sq_sqrt htpos.le]

theorem tail_eq_two {t : ℕ} (ht : 1 ≤ t) : (t : ℝ) ^ 2 / Real.sqrt t ^ 2 = (t : ℝ) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [Real.sq_sqrt htpos.le]
  field_simp

theorem tail_eq_three {t : ℕ} (ht : 1 ≤ t) :
    (t : ℝ) ^ 2 / Real.sqrt t ^ 3 = Real.sqrt t := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsp : (0 : ℝ) < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  rw [sqrt_pow_three _ htpos.le, div_eq_iff (by positivity)]
  nlinarith [Real.sq_sqrt htpos.le]

theorem tail_eq_four {t : ℕ} (ht : 1 ≤ t) : (t : ℝ) ^ 2 / Real.sqrt t ^ 4 = 1 := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [sqrt_pow_four _ htpos.le, div_self (by positivity)]

theorem tail_le_one_of_four_le (hd : 4 ≤ d) {t : ℕ} (ht : 1 ≤ t) :
    (t : ℝ) ^ 2 / Real.sqrt t ^ d ≤ 1 := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hsp1 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht1
  have hmono : Real.sqrt (t : ℝ) ^ 4 ≤ Real.sqrt (t : ℝ) ^ d := pow_le_pow_right₀ hsp1 hd
  have h4 : Real.sqrt (t : ℝ) ^ 4 = (t : ℝ) ^ 2 := sqrt_pow_four _ htpos.le
  rw [div_le_one (by positivity)]
  rw [← h4]
  exact hmono

/-! ### The five branches of the table, upper half -/

/-- The `d`-dependent rate of `eq:Qt-table`: `t^{3/2}` in dimension one, `t` in
dimension two, `t^{1/2}` in dimension three, `log t` in dimension four, and `1`
in dimensions five and above. -/
def varianceRate (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then (t : ℝ) ^ ((3 : ℝ) / 2)
  else if d = 2 then (t : ℝ)
  else if d = 3 then (t : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 4 then Real.log (t : ℝ)
  else 1

/-- **The upper half of `eq:Qt-table`.**  In every dimension the variance scale
`∑_y g_t(0,y)^2` is at most a constant times the rate. -/
theorem exists_tsum_srwGreen_sq_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      ∑' y : Site d, srwGreen d t y ^ 2 ≤ C * varianceRate d t := by
  have hdpos : 0 < d := hd
  set K : ℝ := diagConst d with hK
  have hKpos : 0 < K := diagConst_pos d
  by_cases h1 : d = 1
  · subst h1
    refine ⟨1 + 3 * K, by positivity, fun t ht => ?_⟩
    have ht1 : 1 ≤ t := by omega
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
    have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hsp1 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hrate : varianceRate 1 t = (t : ℝ) * Real.sqrt t := by
      rw [varianceRate, if_pos rfl, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
        Real.rpow_add htpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hmaster := tsum_srwGreen_sq_le_master (d := 1) hdpos ht1
    have hA := diagSum_one_le t
    have hB : (t : ℝ) ^ 2 / Real.sqrt t ^ 1 = (t : ℝ) * Real.sqrt t := tail_eq_one ht1
    rw [hrate]
    have hX : (1 : ℝ) ≤ (t : ℝ) * Real.sqrt t := by nlinarith
    rw [hB] at hmaster
    nlinarith [hmaster, hA, hKpos]
  by_cases h2 : d = 2
  · subst h2
    refine ⟨1 + 3 * K, by positivity, fun t ht => ?_⟩
    have ht1 : 1 ≤ t := by omega
    have ht1R : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have hrate : varianceRate 2 t = (t : ℝ) := by
      rw [varianceRate, if_neg (by norm_num), if_pos rfl]
    have hmaster := tsum_srwGreen_sq_le_master (d := 2) hdpos ht1
    have hA := diagSum_two_le t
    have hB : (t : ℝ) ^ 2 / Real.sqrt t ^ 2 = (t : ℝ) := tail_eq_two ht1
    rw [hrate]
    rw [hB] at hmaster
    nlinarith [hmaster, hA, hKpos]
  by_cases h3 : d = 3
  · subst h3
    refine ⟨1 + 5 * K, by positivity, fun t ht => ?_⟩
    have ht1 : 1 ≤ t := by omega
    have ht1R : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have hsp1 : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt ht1R
    have hrate : varianceRate 3 t = Real.sqrt t := by
      rw [varianceRate, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl,
        ← Real.sqrt_eq_rpow]
    have hmaster := tsum_srwGreen_sq_le_master (d := 3) hdpos ht1
    have hA := diagSum_three_le t
    have hB : (t : ℝ) ^ 2 / Real.sqrt t ^ 3 = Real.sqrt t := tail_eq_three ht1
    rw [hrate]
    rw [hB] at hmaster
    nlinarith [hmaster, hA, hKpos]
  by_cases h4 : d = 4
  · subst h4
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨(1 + 3 * K) / Real.log 2 + 2 * K, by positivity, fun t ht => ?_⟩
    have ht1 : 1 ≤ t := by omega
    have hlogt : Real.log 2 ≤ Real.log (t : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast ht)
    have hrate : varianceRate 4 t = Real.log (t : ℝ) := by
      rw [varianceRate, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
        if_pos rfl]
    have hmaster := tsum_srwGreen_sq_le_master (d := 4) hdpos ht1
    have hA := diagSum_four_le t
    have hB : (t : ℝ) ^ 2 / Real.sqrt t ^ 4 = 1 := tail_eq_four ht1
    rw [hrate]
    rw [hB] at hmaster
    have hkey : (1 + 3 * K) ≤ ((1 + 3 * K) / Real.log 2) * Real.log (t : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    nlinarith [hmaster, hA, hKpos]
  · have h5 : 5 ≤ d := by omega
    refine ⟨1 + 7 * K, by positivity, fun t ht => ?_⟩
    have ht1 : 1 ≤ t := by omega
    have hrate : varianceRate d t = 1 := by
      rw [varianceRate, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    have hmaster := tsum_srwGreen_sq_le_master hdpos ht1
    have hA := diagSum_le_three_of_five_le h5 t
    have hB : (t : ℝ) ^ 2 / Real.sqrt t ^ d ≤ 1 := tail_le_one_of_four_le (by omega) ht1
    rw [hrate, mul_one]
    nlinarith [hmaster, hA, hKpos, hB]

/-! ### The lower half of the table -/

/-- **The even times carry the lower bound.**  Only times of the form `2n` have
a positive return probability, and those alone already give `2c · diagSum`. -/
theorem two_mul_diagSum_le {c : ℝ}
    (hlow : ∀ n : ℕ, 1 ≤ n → c / Real.sqrt n ^ d ≤ srwHeat d (2 * n) 0) (t : ℕ) :
    2 * c * diagSum d ((t + 1) / 2)
      ≤ ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * srwHeat d s 0 := by
  classical
  set m := (t + 1) / 2 with hm
  have hstep : 2 * c * diagSum d m
      = ∑ n ∈ Finset.Ico 1 m, 2 * c * ((n : ℝ) / Real.sqrt n ^ d) := by
    rw [diagSum, Finset.mul_sum]
  have hle1 : ∀ n ∈ Finset.Ico 1 m,
      2 * c * ((n : ℝ) / Real.sqrt n ^ d)
        ≤ (((2 * n : ℕ) : ℝ) + 1) * srwHeat d (2 * n) 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : 1 ≤ n := hn.1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hp : c / Real.sqrt n ^ d ≤ srwHeat d (2 * n) 0 := hlow n hn1
    have hpnn : (0 : ℝ) ≤ srwHeat d (2 * n) 0 := srwHeat_nonneg _ _
    have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [hcast]
    have h1 : 2 * c * ((n : ℝ) / Real.sqrt n ^ d) = (2 * (n : ℝ)) * (c / Real.sqrt n ^ d) := by
      ring
    rw [h1]
    nlinarith
  have hinj : ∀ a ∈ Finset.Ico 1 m, ∀ b ∈ Finset.Ico 1 m, 2 * a = 2 * b → a = b := by
    intro a _ b _ h
    omega
  have himg : ∑ s ∈ (Finset.Ico 1 m).image (fun n : ℕ => 2 * n), ((s : ℝ) + 1) * srwHeat d s 0
      = ∑ n ∈ Finset.Ico 1 m, (((2 * n : ℕ) : ℝ) + 1) * srwHeat d (2 * n) 0 := by
    rw [Finset.sum_image hinj]
  have hsub : (Finset.Ico 1 m).image (fun n : ℕ => 2 * n) ⊆ Finset.range t := by
    intro s hs
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.mem_Ico] at hn
    rw [Finset.mem_range]
    omega
  calc 2 * c * diagSum d m
      = ∑ n ∈ Finset.Ico 1 m, 2 * c * ((n : ℝ) / Real.sqrt n ^ d) := hstep
    _ ≤ ∑ n ∈ Finset.Ico 1 m, (((2 * n : ℕ) : ℝ) + 1) * srwHeat d (2 * n) 0 :=
        Finset.sum_le_sum hle1
    _ = ∑ s ∈ (Finset.Ico 1 m).image (fun n : ℕ => 2 * n), ((s : ℝ) + 1) * srwHeat d s 0 :=
        himg.symm
    _ ≤ ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * srwHeat d s 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun (s : ℕ) _ _ => mul_nonneg (by positivity) (srwHeat_nonneg (d := d) s 0))

/-- The variance scale is at least one, from the time `s = 0` alone. -/
theorem one_le_tsum_srwGreen_sq {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
  refine le_trans ?_ (le_tsum_srwGreen_sq t)
  have h0 : (0 : ℕ) ∈ Finset.range t := Finset.mem_range.mpr (by omega)
  have hterm : ∀ s ∈ Finset.range t, (0 : ℝ) ≤ ((s : ℝ) + 1) * srwHeat d s 0 := by
    intro s _
    exact mul_nonneg (by positivity) (srwHeat_nonneg s 0)
  refine le_trans ?_ (Finset.single_le_sum hterm h0)
  have : srwHeat d 0 (0 : Site d) = 1 := by simp
  rw [this]
  norm_num

theorem sqrt_two_le : Real.sqrt 2 ≤ 3 / 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem varianceRate_nonneg (d : ℕ) {t : ℕ} (ht : 2 ≤ t) : 0 ≤ varianceRate d t := by
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  rw [varianceRate]
  split_ifs
  · positivity
  · linarith
  · positivity
  · exact Real.log_nonneg (by linarith)
  · norm_num

theorem varianceRate_two_le (d : ℕ) : varianceRate d 2 ≤ 3 := by
  rw [varianceRate]
  split_ifs
  · have h2 : (0 : ℝ) < 2 := by norm_num
    have hc2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hc2, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add h2, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have := sqrt_two_le
    nlinarith
  · norm_num
  · have hc2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hc2, ← Real.sqrt_eq_rpow]
    have := sqrt_two_le
    nlinarith
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    push_cast
    linarith
  · norm_num

/-- **The lower half of `eq:Qt-table`.**  In every dimension the variance scale
`∑_y g_t(0,y)^2` is at least a constant times the rate. -/
theorem exists_le_tsum_srwGreen_sq (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 2 ≤ t →
      c * varianceRate d t ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
  have hdpos : 0 < d := hd
  obtain ⟨c₀, C₀, hc₀, hC₀, hbounds⟩ := exists_srwHeat_diag_bounds hdpos
  have hlow : ∀ n : ℕ, 1 ≤ n → c₀ / Real.sqrt n ^ d ≤ srwHeat d (2 * n) 0 :=
    fun n hn => (hbounds n hn).1
  have hbase : ∀ t : ℕ, 2 * c₀ * diagSum d ((t + 1) / 2)
      ≤ ∑' y : Site d, srwGreen d t y ^ 2 :=
    fun t => (two_mul_diagSum_le hlow t).trans (le_tsum_srwGreen_sq t)
  have hsmall : ∀ t : ℕ, 2 ≤ t → t < 3 →
      (1 / 3 : ℝ) * varianceRate d t ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
    intro t ht ht3
    have ht2 : t = 2 := by omega
    subst ht2
    have h1 : (1 : ℝ) ≤ ∑' y : Site d, srwGreen d 2 y ^ 2 :=
      one_le_tsum_srwGreen_sq (by omega)
    have h2 := varianceRate_two_le d
    linarith
  have hcast : ∀ t : ℕ, 3 ≤ t → (t : ℝ) ≤ 2 * (((t + 1) / 2 : ℕ) : ℝ) := by
    intro t ht
    have : t ≤ 2 * ((t + 1) / 2) := by omega
    exact_mod_cast this
  have hm2 : ∀ t : ℕ, 3 ≤ t → 2 ≤ (t + 1) / 2 := by intro t ht; omega
  by_cases h1 : d = 1
  · subst h1
    refine ⟨min (c₀ / 16) (1 / 3), by positivity, fun t ht => ?_⟩
    by_cases ht3 : 3 ≤ t
    · have hmm := hm2 t ht3
      have hct := hcast t ht3
      set m : ℕ := (t + 1) / 2 with hmdef
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hu : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
      have hv : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt htpos.le
      have hun : (0 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
      have hvn : (0 : ℝ) ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
      have hvu : Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by nlinarith
      have hrate : varianceRate 1 t = (t : ℝ) * Real.sqrt t := by
        rw [varianceRate, if_pos rfl, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add htpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have hA := diagSum_one_ge hmm
      have hb := hbase t
      have hcube : (t : ℝ) * Real.sqrt t ≤ 8 * ((m : ℝ) * Real.sqrt m) := by nlinarith
      have hstep : c₀ / 16 * varianceRate 1 t ≤ ∑' y : Site 1, srwGreen 1 t y ^ 2 := by
        rw [hrate]
        nlinarith
      refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (varianceRate_nonneg 1 ht)) hstep
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (varianceRate_nonneg 1 ht)) (hsmall t ht (by omega))
  by_cases h2 : d = 2
  · subst h2
    refine ⟨min (c₀ / 2) (1 / 3), by positivity, fun t ht => ?_⟩
    by_cases ht3 : 3 ≤ t
    · have hmm := hm2 t ht3
      have hct := hcast t ht3
      have hrate : varianceRate 2 t = (t : ℝ) := by
        rw [varianceRate, if_neg (by norm_num), if_pos rfl]
      have hA := diagSum_two_ge hmm
      have hb := hbase t
      have hstep : c₀ / 2 * varianceRate 2 t ≤ ∑' y : Site 2, srwGreen 2 t y ^ 2 := by
        rw [hrate]
        nlinarith
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (varianceRate_nonneg 2 ht)) hstep
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (varianceRate_nonneg 2 ht)) (hsmall t ht (by omega))
  by_cases h3 : d = 3
  · subst h3
    refine ⟨min (c₀ / 2) (1 / 3), by positivity, fun t ht => ?_⟩
    by_cases ht3 : 3 ≤ t
    · have hmm := hm2 t ht3
      have hct := hcast t ht3
      set m : ℕ := (t + 1) / 2 with hmdef
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hu : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
      have hv : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt htpos.le
      have hun : (0 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
      have hvn : (0 : ℝ) ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
      have hvu : Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by nlinarith
      have hrate : varianceRate 3 t = Real.sqrt t := by
        rw [varianceRate, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl,
          ← Real.sqrt_eq_rpow]
      have hA := diagSum_three_ge hmm
      have hb := hbase t
      have hstep : c₀ / 2 * varianceRate 3 t ≤ ∑' y : Site 3, srwGreen 3 t y ^ 2 := by
        rw [hrate]
        nlinarith
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (varianceRate_nonneg 3 ht)) hstep
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (varianceRate_nonneg 3 ht)) (hsmall t ht (by omega))
  by_cases h4 : d = 4
  · subst h4
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨min (2 * c₀ / (1 + Real.log 2)) (1 / 3), by positivity, fun t ht => ?_⟩
    by_cases ht3 : 3 ≤ t
    · have hmm := hm2 t ht3
      have hct := hcast t ht3
      set m : ℕ := (t + 1) / 2 with hmdef
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hrate : varianceRate 4 t = Real.log (t : ℝ) := by
        rw [varianceRate, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
          if_pos rfl]
      have hlogle : Real.log (t : ℝ) ≤ Real.log 2 + Real.log (m : ℝ) := by
        have h2m : Real.log (t : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
          Real.log_le_log htpos hct
        rwa [Real.log_mul (by norm_num) hmpos.ne'] at h2m
      have hA := diagSum_four_ge m
      have hA1 : (1 : ℝ) ≤ diagSum 4 m := one_le_diagSum hmm
      have hb := hbase t
      have hkey : Real.log (t : ℝ) ≤ (1 + Real.log 2) * diagSum 4 m := by nlinarith
      have hstep : 2 * c₀ / (1 + Real.log 2) * varianceRate 4 t
          ≤ ∑' y : Site 4, srwGreen 4 t y ^ 2 := by
        rw [hrate, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (varianceRate_nonneg 4 ht)) hstep
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (varianceRate_nonneg 4 ht)) (hsmall t ht (by omega))
  · refine ⟨min (2 * c₀) (1 / 3), by positivity, fun t ht => ?_⟩
    by_cases ht3 : 3 ≤ t
    · have hmm := hm2 t ht3
      have hrate : varianceRate d t = 1 := by
        rw [varianceRate, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      have hA : (1 : ℝ) ≤ diagSum d ((t + 1) / 2) := one_le_diagSum hmm
      have hb := hbase t
      have hstep : 2 * c₀ * varianceRate d t ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
        rw [hrate, mul_one]
        nlinarith
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (varianceRate_nonneg d ht)) hstep
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (varianceRate_nonneg d ht)) (hsmall t ht (by omega))

/-- **The variance scale `eq:Qt-table`, both directions.**  For `t ≥ 2` the
`ℓ²` mass of the truncated Green function is comparable with `t^{3/2}`, `t`,
`t^{1/2}`, `log t` and `1` in dimensions one, two, three, four, and five and
above. -/
theorem exists_tsum_srwGreen_sq_bounds (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      c * varianceRate d t ≤ ∑' y : Site d, srwGreen d t y ^ 2 ∧
        ∑' y : Site d, srwGreen d t y ^ 2 ≤ C * varianceRate d t := by
  obtain ⟨c, hc, hlow⟩ := exists_le_tsum_srwGreen_sq hd
  obtain ⟨C, hC, hup⟩ := exists_tsum_srwGreen_sq_le hd
  exact ⟨c, C, hc, hC, fun t ht => ⟨hlow t ht, hup t ht⟩⟩

end LatticeProb
