import LatticeProb.Prob.BrownianDriftSmallBall

/-!
# Running-minimum hits of a continuous path

For a path `f : ℝ≥0 → ℝ` and `k : ℕ`, the unit interval `[k - 1, k]` *contains a running-minimum
time* when some `t` in it satisfies `f t ≤ f s` for every `s ≤ t`.  This file gives the
deterministic and measure-theoretic facts used to count such intervals for Brownian motion.

* For a continuous path, a running-minimum time in `[a, b]` relative to `[0, c]` is detected on
  dyadic times (`DyadicMinBefore`, `dyadicMinBefore_of_le`, `exists_isMinOn_of_dyadicMinBefore`,
  `isRunningMinHit_iff`).  The dyadic form is a countable combination of evaluations, hence
  measurable for every σ-algebra making the evaluations up to time `max b c` measurable
  (`measurableSet_dyadicMinBefore`).
* If `[j - 1, j]` contains a running-minimum time and `k + 2 ≤ j ≤ n`, then the path restarted at
  time `k` comes back, at some time of `[1, n]`, below its minimum over `[0, 1]`
  (`dyadicMinBefore_shift_of_isRunningMinHit`).  The set `returnSet n` of such paths is
  measurable and misses every path that stays above `w 0 + δ` on `[1, n]`
  (`notMem_returnSet_of_forall`).
-/

open MeasureTheory Filter

open scoped NNReal Topology

noncomputable section

namespace LatticeProb

/-- The unit interval `[k - 1, k]` contains a running-minimum time of `f`, that is, a time `t`
with `f t ≤ f s` for every `s ≤ t`. -/
def IsRunningMinHit (f : ℝ≥0 → ℝ) (k : ℕ) : Prop :=
  ∃ t : ℝ≥0, ((k - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ k ∧ ∀ s ≤ t, f t ≤ f s

/-- Dyadic form of a minimum: for every `r`, some dyadic time `u ∈ [a, b]` has
`f u ≤ f s + 1 / (r + 1)` for every dyadic time `s ≤ c`. -/
def DyadicMinBefore (f : ℝ≥0 → ℝ) (a b c : ℝ≥0) : Prop :=
  ∀ r : ℕ, ∃ N i : ℕ, a ≤ dyadicGrid N i ∧ dyadicGrid N i ≤ b ∧
    ∀ M j : ℕ, dyadicGrid M j ≤ c → f (dyadicGrid N i) ≤ f (dyadicGrid M j) + 1 / ((r : ℝ) + 1)

theorem natCast_le_dyadicGrid_floor {a : ℕ} {t : ℝ≥0} (hat : (a : ℝ≥0) ≤ t) (N : ℕ) :
    (a : ℝ≥0) ≤ dyadicGrid N ⌊(t : ℝ) * 2 ^ N⌋₊ := by
  rw [← NNReal.coe_le_coe, coe_dyadicGrid, NNReal.coe_natCast, le_div_iff₀ (by positivity)]
  have hat' : (a : ℝ) ≤ t := by exact_mod_cast hat
  have h : ((a * 2 ^ N : ℕ) : ℝ) ≤ (t : ℝ) * 2 ^ N := by
    push_cast
    gcongr
  calc (a : ℝ) * 2 ^ N = ((a * 2 ^ N : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (⌊(t : ℝ) * 2 ^ N⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor h

/-- A minimum time `t ∈ [a, b]` of `f` over `[0, c]` gives the dyadic form, for continuous `f`
and an integer left endpoint `a`. -/
theorem dyadicMinBefore_of_le {f : ℝ≥0 → ℝ} (hf : Continuous f) {a : ℕ} {b c t : ℝ≥0}
    (hat : (a : ℝ≥0) ≤ t) (htb : t ≤ b) (hmin : ∀ s ≤ c, f t ≤ f s) :
    DyadicMinBefore f a b c := by
  intro r
  have hr : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
  have hlim := (hf.tendsto t).comp (tendsto_dyadicGrid_floor t)
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds (lt_add_of_pos_right (f t) hr))).exists
  refine ⟨N, ⌊(t : ℝ) * 2 ^ N⌋₊, natCast_le_dyadicGrid_floor hat N,
    (dyadicGrid_floor_le t N).trans htb, fun M j hj => ?_⟩
  have h1 := hmin _ hj
  simp only [Function.comp_apply] at hN
  linarith

/-- Conversely, for continuous `f`, the dyadic form gives a minimum time `t` of `f` over `[a, b]`
that is also below every value of `f` on `[0, c]`. -/
theorem exists_isMinOn_of_dyadicMinBefore {f : ℝ≥0 → ℝ} (hf : Continuous f) {a b c : ℝ≥0}
    (hab : a ≤ b) (h : DyadicMinBefore f a b c) :
    ∃ t, a ≤ t ∧ t ≤ b ∧ IsMinOn f (Set.Icc a b) t ∧ ∀ s ≤ c, f t ≤ f s := by
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab) hf.continuousOn
  refine ⟨t, ht.1, ht.2, hmin, fun s hs => ?_⟩
  have key : ∀ r M : ℕ,
      f t ≤ f (dyadicGrid M ⌊(s : ℝ) * 2 ^ M⌋₊) + 1 / ((r : ℝ) + 1) := by
    intro r M
    obtain ⟨N, i, h1, h2, h3⟩ := h r
    exact (isMinOn_iff.mp hmin _ ⟨h1, h2⟩).trans (h3 M _ ((dyadicGrid_floor_le s M).trans hs))
  have key' : ∀ r : ℕ, f t ≤ f s + 1 / ((r : ℝ) + 1) := fun r =>
    ge_of_tendsto (((hf.tendsto s).comp (tendsto_dyadicGrid_floor s)).add_const _)
      (Eventually.of_forall fun M => key r M)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt hε
  linarith [key' r]

/-- For a continuous path, a running-minimum hit is detected on dyadic times. -/
theorem isRunningMinHit_iff {f : ℝ≥0 → ℝ} (hf : Continuous f) (k : ℕ) :
    IsRunningMinHit f k ↔ DyadicMinBefore f ((k - 1 : ℕ) : ℝ≥0) k ((k - 1 : ℕ) : ℝ≥0) := by
  constructor
  · rintro ⟨t, h1, h2, h3⟩
    exact dyadicMinBefore_of_le hf h1 h2 fun s hs => h3 s (hs.trans h1)
  · intro h
    have hab : ((k - 1 : ℕ) : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast Nat.sub_le k 1
    obtain ⟨t, h1, h2, hmin, h3⟩ := exists_isMinOn_of_dyadicMinBefore hf hab h
    refine ⟨t, h1, h2, fun s hs => ?_⟩
    by_cases hsk : s ≤ ((k - 1 : ℕ) : ℝ≥0)
    · exact h3 s hsk
    · exact isMinOn_iff.mp hmin s ⟨(not_le.1 hsk).le, hs.trans h2⟩

/-- The dyadic form is measurable for every σ-algebra making the evaluations up to a time
`T ≥ max b c` measurable. -/
theorem measurableSet_dyadicMinBefore {Ω : Type*} {m : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    {a b c T : ℝ≥0} (hbT : b ≤ T) (hcT : c ≤ T) (hm : ∀ s ≤ T, Measurable (B s)) :
    MeasurableSet {ω | DyadicMinBefore (fun t => B t ω) a b c} := by
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.forall fun r => Measurable.exists fun N => Measurable.exists fun i => ?_
  by_cases hb : dyadicGrid N i ≤ b
  · refine measurable_const.and (measurable_const.and
      (Measurable.forall fun M => Measurable.forall fun j => ?_))
    by_cases hc : dyadicGrid M j ≤ c
    · exact measurable_const.imp (measurableSet_setOfPred.1
        (measurableSet_le (hm _ (hb.trans hbT)) ((hm _ (hc.trans hcT)).add_const _)))
    · simp only [hc, false_imp_iff]
      exact measurable_const
  · simp only [hb, false_and, and_false]
    exact measurable_const

/-- The paths that come back, at some time of `[1, n]`, below their minimum over `[0, 1]`
(dyadic form). -/
def returnSet (n : ℕ) : Set (ℝ≥0 → ℝ) :=
  {w | DyadicMinBefore w 1 n 1}

theorem measurableSet_returnSet (n : ℕ) : MeasurableSet (returnSet n) :=
  measurableSet_dyadicMinBefore (B := fun s (w : ℝ≥0 → ℝ) => w s) (T := max (n : ℝ≥0) 1)
    (le_max_left _ _) (le_max_right _ _) fun s _ => measurable_pi_apply s

/-- A path that stays above `w 0 + δ` on `[1, n]` does not come back below its minimum over
`[0, 1]`. -/
theorem notMem_returnSet_of_forall {w : ℝ≥0 → ℝ} {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ u : ℝ≥0, 1 ≤ u → u ≤ n → w 0 + δ ≤ w u) : w ∉ returnSet n := by
  intro hw
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, i, h1, h2, h3⟩ := hw r
  have h0 : dyadicGrid 0 0 = 0 := by simp [dyadicGrid]
  have h4 := h3 0 0 (by rw [h0]; exact zero_le_one)
  rw [h0] at h4
  linarith [h _ h1 h2]

/-- A running-minimum hit in `[j - 1, j]` with `k + 2 ≤ j ≤ n` makes the path restarted at time
`k` come back, at some time of `[1, n]`, below its minimum over `[0, 1]`. -/
theorem shift_mem_returnSet_of_isRunningMinHit {f : ℝ≥0 → ℝ} (hf : Continuous f) {k j n : ℕ}
    (hkj : k + 2 ≤ j) (hjn : j ≤ n) (h : IsRunningMinHit f j) :
    (fun u => f (k + u) - f k) ∈ returnSet n := by
  obtain ⟨t, h1, h2, h3⟩ := h
  have hk1 : (k : ℝ≥0) + 1 ≤ t := by
    have h' : ((k + 1 : ℕ) : ℝ≥0) ≤ ((j - 1 : ℕ) : ℝ≥0) := Nat.cast_le.2 (by omega)
    have h'' := h'.trans h1
    rwa [Nat.cast_add, Nat.cast_one] at h''
  have hkt : (k : ℝ≥0) ≤ t := le_trans (le_add_of_nonneg_right zero_le_one) hk1
  have hcont : Continuous fun u : ℝ≥0 => f (k + u) - f k :=
    (hf.comp (continuous_const.add continuous_id)).sub continuous_const
  have hd := dyadicMinBefore_of_le hcont (a := 1) (b := n) (c := 1) (t := t - k)
    (by rw [Nat.cast_one]; exact le_tsub_of_add_le_left hk1)
    (tsub_le_self.trans (h2.trans (by exact_mod_cast hjn))) fun s hs => by
      rw [add_tsub_cancel_of_le hkt]
      have hks : (k : ℝ≥0) + s ≤ t := (add_le_add (le_refl _) hs).trans hk1
      linarith [h3 _ hks]
  rw [Nat.cast_one] at hd
  exact hd

end LatticeProb
