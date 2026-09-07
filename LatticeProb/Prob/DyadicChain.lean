/-
Dyadic chaining.

The deterministic half of the Kolmogorov-Chentsov theorem.  A function on
`ℝ≥0` whose increments over the dyadic grid of level `n` are at most `a n`, for
every level from some point on and over a range of the grid that grows with the
level, is the restriction to the dyadic points of a continuous function, namely
the limit of its values along the truncations `dtrunc n t = ⌊t 2^n⌋ / 2^n`.

No enumeration of pairs of dyadic points is built.  Everything comes from one
step estimate: `dtrunc n t` and `dtrunc (n+1) t` are level-`(n+1)` dyadic points
at distance `0` or `2^{-(n+1)}`, so the increment bound at level `n + 1` applies
to them.  Telescoping that gives `|f (dtrunc j t) - f (dtrunc m t)|` at most the
tail `∑_{n > m} a n`, and two points at distance at most `2^{-m}` have
truncations at level `m` which are again `0` or one step apart.
-/
import Mathlib

noncomputable section

open Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-! ### The dyadic grid -/

/-- The `k`-th dyadic point of level `n`. -/
def dyad (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

/-- `t` truncated down to the dyadic grid of level `n`. -/
def dtrunc (n : ℕ) (t : ℝ≥0) : ℝ≥0 := dyad n ⌊t * 2 ^ n⌋₊

theorem two_pow_ne_zero (n : ℕ) : (2 : ℝ≥0) ^ n ≠ 0 := by positivity

theorem dyad_mul_pow (n k : ℕ) : dyad n k * 2 ^ n = (k : ℝ≥0) := by
  rw [dyad, div_mul_cancel₀ _ (two_pow_ne_zero n)]

theorem dyad_two_mul (n k : ℕ) : dyad (n + 1) (2 * k) = dyad n k := by
  rw [dyad, dyad, pow_succ]
  push_cast
  rw [div_eq_div_iff (by positivity) (two_pow_ne_zero n)]
  ring

theorem dyad_le_dyad {n k l : ℕ} (h : k ≤ l) : dyad n k ≤ dyad n l := by
  unfold dyad
  gcongr

theorem floor_dyad (n k : ℕ) : ⌊dyad n k * 2 ^ n⌋₊ = k := by
  rw [dyad_mul_pow, Nat.floor_natCast]

theorem dtrunc_le (n : ℕ) (t : ℝ≥0) : dtrunc n t ≤ t := by
  rw [dtrunc, dyad, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by simp)

theorem lt_dyad_floor_succ (n : ℕ) (t : ℝ≥0) : t < dyad n (⌊t * 2 ^ n⌋₊ + 1) := by
  rw [dyad, lt_div_iff₀ (by positivity)]
  push_cast
  exact Nat.lt_floor_add_one _

theorem floor_le_of_le {t : ℝ≥0} {N : ℕ} (h : t ≤ (N : ℝ≥0)) (n : ℕ) :
    ⌊t * 2 ^ n⌋₊ ≤ N * 2 ^ n := by
  have : ⌊t * 2 ^ n⌋₊ ≤ ⌊(N : ℝ≥0) * 2 ^ n⌋₊ := Nat.floor_le_floor (by gcongr)
  refine this.trans_eq ?_
  rw [show ((N : ℝ≥0) * 2 ^ n) = ((N * 2 ^ n : ℕ) : ℝ≥0) by push_cast; ring, Nat.floor_natCast]

theorem floor_mono_mul {s t : ℝ≥0} (h : s ≤ t) (n : ℕ) :
    ⌊s * 2 ^ n⌋₊ ≤ ⌊t * 2 ^ n⌋₊ :=
  Nat.floor_le_floor (by gcongr)

/-- The level-`(n+1)` index of `t` is twice its level-`n` index, or one more. -/
theorem floor_succ_level (n : ℕ) (t : ℝ≥0) :
    ⌊t * 2 ^ (n + 1)⌋₊ = 2 * ⌊t * 2 ^ n⌋₊ ∨ ⌊t * 2 ^ (n + 1)⌋₊ = 2 * ⌊t * 2 ^ n⌋₊ + 1 := by
  set k := ⌊t * 2 ^ n⌋₊ with hk
  have hlow : ((k : ℝ≥0)) ≤ t * 2 ^ n := Nat.floor_le (by simp)
  have hhigh : t * 2 ^ n < (k : ℝ≥0) + 1 := Nat.lt_floor_add_one _
  have h1 : 2 * k ≤ ⌊t * 2 ^ (n + 1)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    rw [pow_succ]
    calc (2 : ℝ≥0) * k = k * 2 := by ring
      _ ≤ (t * 2 ^ n) * 2 := by gcongr
      _ = t * (2 ^ n * 2) := by ring
  have h2 : ⌊t * 2 ^ (n + 1)⌋₊ < 2 * k + 2 := by
    rw [Nat.floor_lt (by simp)]
    push_cast
    rw [pow_succ]
    calc t * (2 ^ n * 2) = (t * 2 ^ n) * 2 := by ring
      _ < ((k : ℝ≥0) + 1) * 2 := by gcongr
      _ = 2 * k + 2 := by ring
  omega

theorem dtrunc_eq_dyad_two_mul (n : ℕ) (t : ℝ≥0) :
    dtrunc n t = dyad (n + 1) (2 * ⌊t * 2 ^ n⌋₊) := by
  rw [dtrunc, dyad_two_mul]

/-! ### The chaining hypothesis -/

/-- The increments of `f` across the level-`n` dyadic grid, over the initial
segment of length `n · 2 ^ n`, are at most `a n`, for every level `n ≥ n₀`. -/
def DyadicIncBound (f : ℝ≥0 → ℝ) (a : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ k : ℕ, k + 1 ≤ n * 2 ^ n →
    |f (dyad n (k + 1)) - f (dyad n k)| ≤ a n

variable {f : ℝ≥0 → ℝ} {a : ℕ → ℝ} {n₀ : ℕ}

/-- One refinement step: the truncations of `t` at levels `n` and `n + 1` are
level-`(n+1)` dyadic points which are equal or adjacent. -/
theorem dtrunc_step (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n)
    {n : ℕ} (hn : n₀ ≤ n) {t : ℝ≥0} (ht : t ≤ (n : ℝ≥0)) :
    |f (dtrunc (n + 1) t) - f (dtrunc n t)| ≤ a (n + 1) := by
  set k := ⌊t * 2 ^ n⌋₊ with hk
  have hkle : k ≤ n * 2 ^ n := floor_le_of_le ht n
  have hpow : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have hrange : 2 * k + 1 ≤ (n + 1) * 2 ^ (n + 1) := by
    have : (n + 1) * 2 ^ (n + 1) = n * 2 ^ n * 2 + 2 ^ (n + 1) := by rw [pow_succ]; ring
    omega
  rcases floor_succ_level n t with hcase | hcase
  · rw [dtrunc_eq_dyad_two_mul n t, dtrunc, hcase, ← hk]
    simpa using ha (n + 1)
  · rw [dtrunc_eq_dyad_two_mul n t, dtrunc, hcase, ← hk]
    exact h (n + 1) (by omega) (2 * k) hrange

/-- The telescoped estimate along the levels. -/
theorem dtrunc_dist_le (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n)
    {m : ℕ} (hm : n₀ ≤ m) {t : ℝ≥0} (ht : t ≤ (m : ℝ≥0)) :
    ∀ j, m ≤ j → |f (dtrunc j t) - f (dtrunc m t)| ≤ ∑ n ∈ Finset.Ico (m + 1) (j + 1), a n := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      have hjm : t ≤ (j : ℝ≥0) := ht.trans (by exact_mod_cast Nat.cast_le.mpr hj)
      have hstep := dtrunc_step h ha (hm.trans hj) hjm
      have : |f (dtrunc (j + 1) t) - f (dtrunc m t)|
          ≤ |f (dtrunc (j + 1) t) - f (dtrunc j t)| + |f (dtrunc j t) - f (dtrunc m t)| := by
        simpa using abs_sub_le (f (dtrunc (j + 1) t)) (f (dtrunc j t)) (f (dtrunc m t))
      refine this.trans ?_
      rw [Finset.sum_Ico_succ_top (by omega)]
      have := add_le_add hstep ih
      linarith

/-! ### The tail of the increment bounds -/

/-- The tail `∑_{n > m} a n` of the increment bounds. -/
def dtail (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑' i : ℕ, a (i + (m + 1))

theorem summable_shift (hsum : Summable a) (m : ℕ) : Summable fun i : ℕ => a (i + m) :=
  (summable_nat_add_iff m).mpr hsum

theorem dtail_nonneg (ha : ∀ n, 0 ≤ a n) (m : ℕ) : 0 ≤ dtail a m :=
  tsum_nonneg fun _ => ha _

theorem sum_Ico_le_dtail (hsum : Summable a) (ha : ∀ n, 0 ≤ a n) (m j : ℕ) :
    ∑ n ∈ Finset.Ico (m + 1) (j + 1), a n ≤ dtail a m := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine le_trans (le_of_eq ?_) (Summable.sum_le_tsum (Finset.range (j + 1 - (m + 1)))
    (fun i _ => ha _) (summable_shift hsum (m + 1)))
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm (m + 1) i]

theorem tendsto_dtail (a : ℕ → ℝ) : Tendsto (dtail a) atTop (𝓝 0) :=
  (tendsto_sum_nat_add a).comp (Filter.tendsto_add_atTop_nat 1)

/-! ### The limit along the truncations -/

/-- The value of `f` read at `t` through its dyadic truncations. -/
def dlim (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := limsup (fun n => f (dtrunc n t)) atTop

theorem tendsto_dtrunc (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (t : ℝ≥0) : Tendsto (fun n => f (dtrunc n t)) atTop (𝓝 (dlim f t)) := by
  have hcauchy : CauchySeq fun n => f (dtrunc n t) := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨M, hM⟩ := (tendsto_dtail a).eventually (gt_mem_nhds
      (show (0 : ℝ) < ε from hε)) |>.exists_forall_of_atTop
    refine ⟨max (max n₀ ⌈t⌉₊) M, fun j hj => ?_⟩
    set m := max (max n₀ ⌈t⌉₊) M with hmdef
    have hmn₀ : n₀ ≤ m := le_max_of_le_left (le_max_left _ _)
    have htm : t ≤ (m : ℝ≥0) := (Nat.le_ceil t).trans
      (by exact_mod_cast Nat.cast_le.mpr (le_max_of_le_left (le_max_right _ _)))
    have hMm : M ≤ m := le_max_right _ _
    calc dist (f (dtrunc j t)) (f (dtrunc m t))
        = |f (dtrunc j t) - f (dtrunc m t)| := Real.dist_eq _ _
      _ ≤ ∑ n ∈ Finset.Ico (m + 1) (j + 1), a n := dtrunc_dist_le h ha hmn₀ htm j hj
      _ ≤ dtail a m := sum_Ico_le_dtail hsum ha m j
      _ < ε := by
          have := hM m hMm
          simpa [abs_of_nonneg (dtail_nonneg ha m)] using this
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  rwa [dlim, hc.limsup_eq]

/-- The limit is within the tail of any truncation from level `m` on. -/
theorem dlim_sub_dtrunc_le (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    {m : ℕ} (hm : n₀ ≤ m) {t : ℝ≥0} (ht : t ≤ (m : ℝ≥0)) :
    |dlim f t - f (dtrunc m t)| ≤ dtail a m := by
  refine le_of_tendsto ((tendsto_dtrunc h ha hsum t).sub_const _).abs ?_
  filter_upwards [eventually_ge_atTop m] with j hj
  exact (dtrunc_dist_le h ha hm ht j hj).trans (sum_Ico_le_dtail hsum ha m j)

/-- Two points at distance at most `2^{-m}` have level-`m` truncations that are
equal or adjacent. -/
theorem dtrunc_close (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n)
    {m : ℕ} (hm : n₀ ≤ m) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ (m : ℝ≥0))
    (hclose : t ≤ s + dyad m 1) :
    |f (dtrunc m t) - f (dtrunc m s)| ≤ a m := by
  set k := ⌊s * 2 ^ m⌋₊ with hk
  set l := ⌊t * 2 ^ m⌋₊ with hl
  have hkl : k ≤ l := floor_mono_mul hst m
  have hlk : l ≤ k + 1 := by
    have hlt : t * 2 ^ m < ((k + 2 : ℕ) : ℝ≥0) := by
      have h1 : t * 2 ^ m ≤ (s + dyad m 1) * 2 ^ m := by gcongr
      have h2 : (s + dyad m 1) * 2 ^ m = s * 2 ^ m + 1 := by
        rw [add_mul, dyad_mul_pow]; norm_num
      have h3 : s * 2 ^ m < (k : ℝ≥0) + 1 := Nat.lt_floor_add_one _
      push_cast
      calc t * 2 ^ m ≤ s * 2 ^ m + 1 := h1.trans_eq h2
        _ < ((k : ℝ≥0) + 1) + 1 := by gcongr
        _ = (k : ℝ≥0) + 2 := by ring
    have hfl := (Nat.floor_lt (by simp)).mpr hlt
    omega
  have hlrange : l ≤ m * 2 ^ m := floor_le_of_le ht m
  rcases (by omega : l = k ∨ l = k + 1) with hcase | hcase
  · rw [dtrunc, dtrunc, ← hk, ← hl, hcase]
    simpa using ha m
  · rw [dtrunc, dtrunc, ← hk, ← hl, hcase]
    exact h m hm k (by omega)

/-- The modulus of continuity of `dlim f`. -/
theorem dlim_sub_le (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    {m : ℕ} (hm : n₀ ≤ m) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ (m : ℝ≥0))
    (hclose : t ≤ s + dyad m 1) :
    |dlim f t - dlim f s| ≤ 2 * dtail a m + a m := by
  have hs : s ≤ (m : ℝ≥0) := hst.trans ht
  have h1 := dlim_sub_dtrunc_le h ha hsum hm ht
  have h2 := dlim_sub_dtrunc_le h ha hsum hm hs
  have h3 := dtrunc_close h ha hm hst ht hclose
  have : |dlim f t - dlim f s|
      ≤ |dlim f t - f (dtrunc m t)| + |f (dtrunc m t) - f (dtrunc m s)|
        + |f (dtrunc m s) - dlim f s| := by
    have e1 : dlim f t - dlim f s
        = (dlim f t - f (dtrunc m t)) + (f (dtrunc m t) - f (dtrunc m s))
          + (f (dtrunc m s) - dlim f s) := by ring
    rw [e1]
    exact abs_add_three _ _ _
  have h4 : |f (dtrunc m s) - dlim f s| ≤ dtail a m := by
    rw [abs_sub_comm]; exact h2
  linarith

/-- The modulus of continuity, without an ordering of the two points. -/
theorem dlim_dist_le' (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    {m : ℕ} (hm : n₀ ≤ m) {s t : ℝ≥0} (hsm : s ≤ (m : ℝ≥0)) (htm : t ≤ (m : ℝ≥0))
    (hclose : dist (s : ℝ) (t : ℝ) < (dyad m 1 : ℝ)) :
    |dlim f t - dlim f s| ≤ 2 * dtail a m + a m := by
  rcases le_total s t with hst | hts
  · refine dlim_sub_le h ha hsum hm hst htm ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_add]
    have := abs_sub_lt_iff.mp (by rwa [Real.dist_eq] at hclose)
    linarith [this.2]
  · rw [abs_sub_comm]
    refine dlim_sub_le h ha hsum hm hts hsm ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_add]
    have := abs_sub_lt_iff.mp (by rwa [Real.dist_eq] at hclose)
    linarith [this.1]

theorem dyad_one_pos (m : ℕ) : 0 < (dyad m 1 : ℝ) := by
  rw [NNReal.coe_pos, dyad]
  positivity

theorem dyad_one_le_one (m : ℕ) : (dyad m 1 : ℝ) ≤ 1 := by
  have : dyad m 1 ≤ 1 := by
    rw [dyad, div_le_one (by positivity)]
    push_cast
    exact one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2)
  exact_mod_cast this

/-- **The chained limit is continuous.** -/
theorem continuous_dlim (h : DyadicIncBound f a n₀) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) :
    Continuous (dlim f) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => Metric.continuousAt_iff.mpr fun ε hε => ?_
  have hzero : Tendsto (fun m => 2 * dtail a m + a m) atTop (𝓝 0) := by
    have := ((tendsto_dtail a).const_mul (2 : ℝ)).add hsum.tendsto_atTop_zero
    simpa using this
  obtain ⟨M, hM⟩ := (hzero.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  set m := max (max n₀ ⌈t₀ + 1⌉₊) M with hmdef
  have hm : n₀ ≤ m := le_max_of_le_left (le_max_left _ _)
  have hMm : M ≤ m := le_max_right _ _
  have ht₀m : t₀ + 1 ≤ (m : ℝ≥0) := (Nat.le_ceil _).trans
    (by exact_mod_cast Nat.cast_le.mpr (le_max_of_le_left (le_max_right _ _)))
  have hone := dyad_one_le_one m
  have hbound : ∀ u : ℝ≥0, dist (u : ℝ) (t₀ : ℝ) < (dyad m 1 : ℝ) → u ≤ (m : ℝ≥0) := by
    intro u hu
    rw [Real.dist_eq] at hu
    have hlt := abs_sub_lt_iff.mp hu
    have h2 : (u : ℝ) ≤ ((t₀ + 1 : ℝ≥0) : ℝ) := by push_cast; linarith [hlt.1]
    exact (NNReal.coe_le_coe.mp h2).trans ht₀m
  refine ⟨(dyad m 1 : ℝ), dyad_one_pos m, fun {t} hdist => ?_⟩
  have hdist' : dist (t : ℝ) (t₀ : ℝ) < (dyad m 1 : ℝ) := by
    rw [Real.dist_eq, ← NNReal.dist_eq]; exact hdist
  have htm : t ≤ (m : ℝ≥0) := hbound t hdist'
  have ht₀ : t₀ ≤ (m : ℝ≥0) := hbound t₀ (by simpa using dyad_one_pos m)
  calc dist (dlim f t) (dlim f t₀) = |dlim f t - dlim f t₀| := Real.dist_eq _ _
    _ ≤ 2 * dtail a m + a m := dlim_dist_le' h ha hsum hm ht₀ htm
        (by rw [dist_comm]; exact hdist')
    _ < ε := hM m hMm

end LatticeProb

end
