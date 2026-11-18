import LatticeProb.Prob.UniformLimitAfterPositiveTimes

/-!
# Shifting the limit after positive times

For `a k : ℝ≥0 → ℝ` (`k : ℕ`) write `F = limitAfterPositiveTimes a`, so that
`F t = lim_m lim_k (a k t - a k (δ m))` for `t > 0`, with `δ m = (m + 1)⁻¹`. Suppose that

* the increment limits `lim_k (a k t - a k (δ m))` exist whenever `δ m ≤ t` (`hconv`), and
* the limits `lim_m` defining `F t` exist at every positive time `t` (`hext`).

Then for all positive times `x, y` the increments `a k x - a k y` converge to `F x - F y`
(`tendsto_sub_limitAfterPositiveTimes`). Consequently, if `F` is right-continuous at `s`, the
limit after positive times of the sequence shifted to start at time `s`,
`shiftIncrements a s k t = a k (s + t) - a k s`, is `t ↦ F (s + t) - F s`
(`limitAfterPositiveTimes_shiftIncrements`), and the shifted sequence again satisfies both
convergence hypotheses (`exists_tendsto_shiftIncrements_sub_invSuccTime`,
`exists_tendsto_incrementLimitAfter_shiftIncrements`).

If `a k t → G t` for every `t ≥ 0` and `G` is right-continuous at `0`, then `F = G - G 0`
(`limitAfterPositiveTimes_eq_sub_of_tendsto`).

The hypothesis `hext` cannot be dropped: for `a k t = log (1 + k t)` the increment limits are
`log (x / y)`, while `lim_m log ((m + 1) t)` does not exist.
-/

open Filter Topology Set
open scoped NNReal

namespace LatticeProb

theorem tendsto_invSuccTime_atTop_nhds_zero : Tendsto invSuccTime atTop (𝓝 0) :=
  (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).congr fun n => by rw [one_div]; rfl

/-- The times `s + δ m` decrease to `s` from the right. -/
theorem tendsto_add_invSuccTime_nhdsGT (s : ℝ≥0) :
    Tendsto (fun m => s + invSuccTime m) atTop (𝓝[>] s) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m =>
    mem_Ioi.2 (lt_add_of_pos_right s (invSuccTime_pos m))⟩
  simpa using (tendsto_const_nhds (x := s)).add tendsto_invSuccTime_atTop_nhds_zero

/-- The sequence shifted to start at time `s`: `k, t ↦ a k (s + t) - a k s`. -/
def shiftIncrements (a : ℕ → ℝ≥0 → ℝ) (s : ℝ≥0) (k : ℕ) (t : ℝ≥0) : ℝ :=
  a k (s + t) - a k s

section Deterministic

variable {a : ℕ → ℝ≥0 → ℝ}

theorem shiftIncrements_monotone (hmono : ∀ k, Monotone (a k)) (s : ℝ≥0) (k : ℕ) :
    Monotone (shiftIncrements a s k) := fun _ _ htu =>
  sub_le_sub_right (hmono k (add_le_add le_rfl htu)) _

theorem shiftIncrements_nonneg (hmono : ∀ k, Monotone (a k)) (s : ℝ≥0) (k : ℕ) (t : ℝ≥0) :
    0 ≤ shiftIncrements a s k t :=
  sub_nonneg.2 (hmono k le_self_add)

/-- If `a k t → G t` at every time and `G` is right-continuous at `0`, the limit after positive
times is `G - G 0`. -/
theorem limitAfterPositiveTimes_eq_sub_of_tendsto {G : ℝ≥0 → ℝ}
    (hG : ∀ t, Tendsto (fun k => a k t) atTop (𝓝 (G t)))
    (h0 : ContinuousWithinAt G (Ioi 0) 0) (t : ℝ≥0) :
    limitAfterPositiveTimes a t = G t - G 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hm : ∀ m, incrementLimitAfter a m t = G t - G (invSuccTime m) := fun m =>
    ((hG t).sub (hG (invSuccTime m))).limUnder_eq
  have hδ : Tendsto invSuccTime atTop (𝓝[>] 0) := by
    simpa using tendsto_add_invSuccTime_nhdsGT 0
  rw [limitAfterPositiveTimes_of_ne_zero a ht]
  exact (((tendsto_const_nhds (x := G t)).sub (h0.tendsto.comp hδ)).congr
    fun m => (hm m).symm).limUnder_eq

theorem tendsto_incrementLimitAfter_limitAfterPositiveTimes
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 (limitAfterPositiveTimes a t)) := by
  obtain ⟨L, hL⟩ := hext t ht
  rwa [limitAfterPositiveTimes_of_ne_zero a ht.ne', hL.limUnder_eq]

/-- Increments between positive times converge to the increments of the limit after positive
times. -/
theorem tendsto_sub_limitAfterPositiveTimes
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun k => a k x - a k y) atTop
      (𝓝 (limitAfterPositiveTimes a x - limitAfterPositiveTimes a y)) := by
  obtain ⟨n, hn⟩ := exists_invSuccTime_le (lt_min hx hy)
  have hnx : invSuccTime n ≤ x := hn.trans (min_le_left x y)
  have hny : invSuccTime n ≤ y := hn.trans (min_le_right x y)
  have hD : ∀ m, n ≤ m → Tendsto (fun k => a k x - a k y) atTop
      (𝓝 (incrementLimitAfter a m x - incrementLimitAfter a m y)) := fun m hm =>
    ((tendsto_incrementLimitAfter hconv ((invSuccTime_antitone hm).trans hnx)).sub
      (tendsto_incrementLimitAfter hconv ((invSuccTime_antitone hm).trans hny))).congr
      fun k => by ring
  have hlim : Tendsto (fun m => incrementLimitAfter a m x - incrementLimitAfter a m y) atTop
      (𝓝 (limitAfterPositiveTimes a x - limitAfterPositiveTimes a y)) :=
    (tendsto_incrementLimitAfter_limitAfterPositiveTimes hext hx).sub
      (tendsto_incrementLimitAfter_limitAfterPositiveTimes hext hy)
  have hval : limitAfterPositiveTimes a x - limitAfterPositiveTimes a y =
      incrementLimitAfter a n x - incrementLimitAfter a n y := by
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact tendsto_nhds_unique (hD n le_rfl) (hD m hm)
  rw [hval]
  exact hD n le_rfl

/-- The increment limits of the shifted sequence. -/
theorem tendsto_shiftIncrements_sub
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    (s : ℝ≥0) {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun k => shiftIncrements a s k x - shiftIncrements a s k y) atTop
      (𝓝 (limitAfterPositiveTimes a (s + x) - limitAfterPositiveTimes a (s + y))) :=
  (tendsto_sub_limitAfterPositiveTimes hconv hext (hx.trans_le le_add_self)
    (hy.trans_le le_add_self)).congr fun k => by unfold shiftIncrements; ring

theorem exists_tendsto_shiftIncrements_sub_invSuccTime
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    (s : ℝ≥0) :
    ∀ m t, invSuccTime m ≤ t → ∃ L, Tendsto
      (fun k => shiftIncrements a s k t - shiftIncrements a s k (invSuccTime m)) atTop (𝓝 L) :=
  fun m _ ht => ⟨_, tendsto_shiftIncrements_sub hconv hext s
    ((invSuccTime_pos m).trans_le ht) (invSuccTime_pos m)⟩

/-- The limits defining the limit after positive times of the shifted sequence. -/
theorem tendsto_incrementLimitAfter_shiftIncrements
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    {s : ℝ≥0} (hcont : ContinuousWithinAt (limitAfterPositiveTimes a) (Ioi s) s)
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun m => incrementLimitAfter (shiftIncrements a s) m t) atTop
      (𝓝 (limitAfterPositiveTimes a (s + t) - limitAfterPositiveTimes a s)) := by
  have hm : ∀ m, incrementLimitAfter (shiftIncrements a s) m t =
      limitAfterPositiveTimes a (s + t) - limitAfterPositiveTimes a (s + invSuccTime m) :=
    fun m => (tendsto_shiftIncrements_sub hconv hext s ht (invSuccTime_pos m)).limUnder_eq
  exact ((tendsto_const_nhds (x := limitAfterPositiveTimes a (s + t))).sub
    (hcont.tendsto.comp (tendsto_add_invSuccTime_nhdsGT s))).congr fun m => (hm m).symm

theorem exists_tendsto_incrementLimitAfter_shiftIncrements
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    {s : ℝ≥0} (hcont : ContinuousWithinAt (limitAfterPositiveTimes a) (Ioi s) s) :
    ∀ t, 0 < t → ∃ L,
      Tendsto (fun m => incrementLimitAfter (shiftIncrements a s) m t) atTop (𝓝 L) :=
  fun _ ht => ⟨_, tendsto_incrementLimitAfter_shiftIncrements hconv hext hcont ht⟩

/-- **Shift identity.** If the increment limits and the limits after positive times exist and the
limit after positive times `F` is right-continuous at `s`, then the limit after positive times of
the sequence shifted to start at `s` is `t ↦ F (s + t) - F s`. -/
theorem limitAfterPositiveTimes_shiftIncrements
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    {s : ℝ≥0} (hcont : ContinuousWithinAt (limitAfterPositiveTimes a) (Ioi s) s) (t : ℝ≥0) :
    limitAfterPositiveTimes (shiftIncrements a s) t =
      limitAfterPositiveTimes a (s + t) - limitAfterPositiveTimes a s := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [limitAfterPositiveTimes_of_ne_zero _ ht,
    (tendsto_incrementLimitAfter_shiftIncrements hconv hext hcont
      (pos_iff_ne_zero.2 ht)).limUnder_eq]

/-- If the limit after positive times is continuous, so is the one of every shifted sequence. -/
theorem continuous_limitAfterPositiveTimes_shiftIncrements
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    (hext : ∀ t, 0 < t → ∃ L, Tendsto (fun m => incrementLimitAfter a m t) atTop (𝓝 L))
    (hcont : Continuous (limitAfterPositiveTimes a)) (s : ℝ≥0) :
    Continuous (limitAfterPositiveTimes (shiftIncrements a s)) := by
  have heq : limitAfterPositiveTimes (shiftIncrements a s) =
      fun t => limitAfterPositiveTimes a (s + t) - limitAfterPositiveTimes a s :=
    funext (limitAfterPositiveTimes_shiftIncrements hconv hext hcont.continuousWithinAt)
  rw [heq]
  exact (hcont.comp (continuous_const.add continuous_id)).sub continuous_const

end Deterministic

end LatticeProb
