import Mathlib

/-!
# Uniform convergence in probability from convergence after each positive time

Let `A k ω : ℝ≥0 → ℝ` (`k : ℕ`, `ω` in a finite measure space `(Ω, Q)`) be nondecreasing,
continuous and nonnegative in time, and measurable in `ω` at each fixed time. Write
`δ n = (n + 1)⁻¹` (`invSuccTime`). Suppose that

* after each time `δ n`, almost surely the increments `t ↦ A k ω t - A k ω (δ n)` form a uniform
  Cauchy sequence on every interval `[δ n, T]`;
* the values at the times `δ n` are small in probability, uniformly in `k`:
  `sup_k Q (A k (δ n) ≥ η) → 0` as `n → ∞`, for every `η > 0`.

Then `A k` converges in `Q`-measure to `limitAfterPositiveTimes`, uniformly on every interval
`[0, T]` (`tendsto_measure_exists_le_abs_sub_limitAfterPositiveTimes`), and the limit vanishes at
time `0` (`limitAfterPositiveTimes_zero`).

The limit is explicit. `incrementLimitAfter a m t = lim_k (a k t - a k (δ m))` is the limit
increment after the time `δ m`, and `limitAfterPositiveTimes a t = lim_m incrementLimitAfter a m t`
for `t > 0`. For a single family of paths `a k` whose values at `δ n` are frequently below `c`,
`|a k t - F t| ≤ |a k t - a k (δ n) - G_n t| + a k (δ n) + c` for `t ≥ δ n`
(`abs_sub_limitAfterPositiveTimes_le_of_le`) and `|a k t - F t| ≤ a k (δ n) + c` for `t ≤ δ n`
(`abs_sub_limitAfterPositiveTimes_le_of_ge`). The probabilistic step uses the continuity from above
of `Q` along the decreasing events `{∃ i, j ≥ k, ∃ t ∈ [δ n, T], |Δ_i t - Δ_j t| > c}`, which are
measurable by the continuity in time (`measurableSet_exists_mem_lt_of_continuous`).

The smallness hypothesis cannot be dropped: the deterministic functions `A k t = min 1 (k t)` satisfy
all the other hypotheses, while no function vanishing at `0` is their uniform limit on `[0, 1]`.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- The positive times `δ n = (n + 1)⁻¹`, decreasing to `0`. -/
noncomputable def invSuccTime (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹

theorem invSuccTime_pos (n : ℕ) : 0 < invSuccTime n := by
  unfold invSuccTime
  positivity

theorem invSuccTime_antitone : Antitone invSuccTime := by
  intro m n hmn
  unfold invSuccTime
  gcongr

theorem exists_invSuccTime_le {t : ℝ≥0} (ht : 0 < t) : ∃ n, invSuccTime n ≤ t := by
  obtain ⟨n, hn⟩ := exists_nat_gt t⁻¹
  refine ⟨n, ?_⟩
  unfold invSuccTime
  rw [inv_le_comm₀ (by positivity) ht]
  exact hn.le.trans (le_add_of_nonneg_right zero_le_one)

/-- For a family of functions continuous in time and measurable at each fixed time, the event that
the function exceeds `c` at some time of a set `s` is measurable (reduction to a countable dense
subset of `s`). -/
theorem measurableSet_exists_mem_lt_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → ℝ≥0 → ℝ) (hg : ∀ ω, Continuous (g ω)) (hm : ∀ t, Measurable fun ω => g ω t)
    (s : Set ℝ≥0) (c : ℝ) : MeasurableSet {ω | ∃ t ∈ s, c < g ω t} := by
  obtain ⟨S, hSc, hSs, hsS⟩ := TopologicalSpace.exists_countable_dense_subset s
  have hEq : {ω | ∃ t ∈ s, c < g ω t} = ⋃ t ∈ S, {ω | c < g ω t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨t, hts, ht⟩
      obtain ⟨x, hxU, hxS⟩ :=
        mem_closure_iff.1 (hsS hts) _ (isOpen_lt continuous_const (hg ω)) ht
      exact ⟨x, hxS, hxU⟩
    · rintro ⟨t, htS, ht⟩
      exact ⟨t, hSs htS, ht⟩
  rw [hEq]
  exact MeasurableSet.biUnion hSc fun t _ => measurableSet_lt measurable_const (hm t)

section Deterministic

/-- The limit increment `lim_k (a k t - a k (δ m))` after the time `δ m = invSuccTime m`. -/
noncomputable def incrementLimitAfter (a : ℕ → ℝ≥0 → ℝ) (m : ℕ) (t : ℝ≥0) : ℝ :=
  limUnder atTop fun k => a k t - a k (invSuccTime m)

/-- The limit `lim_m lim_k (a k t - a k (δ m))` for `t > 0`, and `0` at `t = 0`. -/
noncomputable def limitAfterPositiveTimes (a : ℕ → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t = 0 then 0 else limUnder atTop fun m => incrementLimitAfter a m t

@[simp]
theorem limitAfterPositiveTimes_zero (a : ℕ → ℝ≥0 → ℝ) : limitAfterPositiveTimes a 0 = 0 := by
  simp [limitAfterPositiveTimes]

theorem limitAfterPositiveTimes_of_ne_zero (a : ℕ → ℝ≥0 → ℝ) {t : ℝ≥0} (ht : t ≠ 0) :
    limitAfterPositiveTimes a t = limUnder atTop fun m => incrementLimitAfter a m t := by
  simp [limitAfterPositiveTimes, ht]

variable {a : ℕ → ℝ≥0 → ℝ}

theorem tendsto_incrementLimitAfter
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {m : ℕ} {t : ℝ≥0} (ht : invSuccTime m ≤ t) :
    Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 (incrementLimitAfter a m t)) := by
  obtain ⟨L, hL⟩ := hconv m t ht
  rwa [incrementLimitAfter, hL.limUnder_eq]

theorem incrementLimitAfter_eq_add
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n m : ℕ} (hnm : n ≤ m) {t : ℝ≥0} (ht : invSuccTime n ≤ t) :
    incrementLimitAfter a m t =
      incrementLimitAfter a n t + incrementLimitAfter a m (invSuccTime n) := by
  have hδ := invSuccTime_antitone hnm
  refine tendsto_nhds_unique (tendsto_incrementLimitAfter hconv (hδ.trans ht)) ?_
  refine ((tendsto_incrementLimitAfter hconv ht).add
    (tendsto_incrementLimitAfter hconv hδ)).congr fun k => ?_
  ring

theorem incrementLimitAfter_mono (hmono : ∀ k, Monotone (a k))
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {m : ℕ} {t t' : ℝ≥0} (ht : invSuccTime m ≤ t) (htt' : t ≤ t') :
    incrementLimitAfter a m t ≤ incrementLimitAfter a m t' :=
  le_of_tendsto_of_tendsto' (tendsto_incrementLimitAfter hconv ht)
    (tendsto_incrementLimitAfter hconv (ht.trans htt')) fun k => sub_le_sub_right (hmono k htt') _

theorem incrementLimitAfter_nonneg (hmono : ∀ k, Monotone (a k))
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {m : ℕ} {t : ℝ≥0} (ht : invSuccTime m ≤ t) : 0 ≤ incrementLimitAfter a m t :=
  ge_of_tendsto' (tendsto_incrementLimitAfter hconv ht) fun k => sub_nonneg.2 (hmono k ht)

theorem incrementLimitAfter_le_of_frequently (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n m : ℕ} (hnm : n ≤ m) {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c) :
    incrementLimitAfter a m (invSuccTime n) ≤ c := by
  refine not_lt.1 fun hlt => ?_
  have hev :=
    (tendsto_incrementLimitAfter hconv (invSuccTime_antitone hnm)).eventually (lt_mem_nhds hlt)
  obtain ⟨k, hk1, hk2⟩ := (hfreq.and_eventually hev).exists
  have hk2' : c < a k (invSuccTime n) - a k (invSuccTime m) := hk2
  have := hnn k (invSuccTime m)
  linarith

theorem tendsto_limitAfterPositiveTimes_invSuccTime (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c) :
    Tendsto (fun m => incrementLimitAfter a m (invSuccTime n)) atTop
      (𝓝 (limitAfterPositiveTimes a (invSuccTime n))) := by
  have hgmono : Monotone fun j => incrementLimitAfter a (j + n) (invSuccTime n) := by
    intro i j hij
    show incrementLimitAfter a (i + n) (invSuccTime n) ≤
      incrementLimitAfter a (j + n) (invSuccTime n)
    rw [incrementLimitAfter_eq_add hconv (show i + n ≤ j + n by omega)
      (invSuccTime_antitone (show n ≤ i + n by omega))]
    have := incrementLimitAfter_nonneg hmono hconv (m := j + n)
      (invSuccTime_antitone (show i + n ≤ j + n by omega))
    linarith
  have hgbdd : BddAbove (range fun j => incrementLimitAfter a (j + n) (invSuccTime n)) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact incrementLimitAfter_le_of_frequently hnn hconv (by omega) hfreq
  have hlim : Tendsto (fun m => incrementLimitAfter a m (invSuccTime n)) atTop
      (𝓝 (⨆ j, incrementLimitAfter a (j + n) (invSuccTime n))) :=
    (tendsto_add_atTop_iff_nat n).1 (tendsto_atTop_ciSup hgmono hgbdd)
  rwa [limitAfterPositiveTimes_of_ne_zero a (invSuccTime_pos n).ne', hlim.limUnder_eq]

theorem limitAfterPositiveTimes_invSuccTime_nonneg (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c) :
    0 ≤ limitAfterPositiveTimes a (invSuccTime n) :=
  ge_of_tendsto (tendsto_limitAfterPositiveTimes_invSuccTime hmono hnn hconv hfreq)
    (eventually_atTop.2 ⟨n, fun _ hm => incrementLimitAfter_nonneg hmono hconv
      (invSuccTime_antitone hm)⟩)

theorem limitAfterPositiveTimes_invSuccTime_le (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c) :
    limitAfterPositiveTimes a (invSuccTime n) ≤ c :=
  le_of_tendsto (tendsto_limitAfterPositiveTimes_invSuccTime hmono hnn hconv hfreq)
    (eventually_atTop.2 ⟨n, fun _ hm => incrementLimitAfter_le_of_frequently hnn hconv hm hfreq⟩)

theorem limitAfterPositiveTimes_eq_add (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c)
    {t : ℝ≥0} (ht : invSuccTime n ≤ t) :
    limitAfterPositiveTimes a t =
      incrementLimitAfter a n t + limitAfterPositiveTimes a (invSuccTime n) := by
  have hlim : Tendsto (fun m => incrementLimitAfter a m t) atTop
      (𝓝 (incrementLimitAfter a n t + limitAfterPositiveTimes a (invSuccTime n))) := by
    refine (tendsto_const_nhds.add
      (tendsto_limitAfterPositiveTimes_invSuccTime hmono hnn hconv hfreq)).congr' ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (incrementLimitAfter_eq_add hconv hm ht).symm
  rw [limitAfterPositiveTimes_of_ne_zero a ((invSuccTime_pos n).trans_le ht).ne',
    hlim.limUnder_eq]

theorem limitAfterPositiveTimes_mem_Icc_of_le (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c)
    {t : ℝ≥0} (ht : t ≤ invSuccTime n) :
    0 ≤ limitAfterPositiveTimes a t ∧
      limitAfterPositiveTimes a t ≤ limitAfterPositiveTimes a (invSuccTime n) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simpa using limitAfterPositiveTimes_invSuccTime_nonneg hmono hnn hconv hfreq
  obtain ⟨n', hn'⟩ := exists_invSuccTime_le (pos_iff_ne_zero.2 ht0)
  have hδ : invSuccTime (max n n') ≤ t := (invSuccTime_antitone (le_max_right n n')).trans hn'
  have hδn : invSuccTime (max n n') ≤ invSuccTime n := invSuccTime_antitone (le_max_left n n')
  have hfreq' : ∃ᶠ k in atTop, a k (invSuccTime (max n n')) < c :=
    hfreq.mono fun k hk => (hmono k hδn).trans_lt hk
  rw [limitAfterPositiveTimes_eq_add hmono hnn hconv hfreq' hδ,
    limitAfterPositiveTimes_eq_add hmono hnn hconv hfreq' hδn]
  have h1 := incrementLimitAfter_nonneg hmono hconv hδ
  have h2 := incrementLimitAfter_mono hmono hconv hδ ht
  have h3 := limitAfterPositiveTimes_invSuccTime_nonneg hmono hnn hconv hfreq'
  constructor <;> linarith

/-- Deterministic bound after the time `δ n`, for paths whose values at `δ n` are frequently
below `c`. -/
theorem abs_sub_limitAfterPositiveTimes_le_of_le (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c) (k : ℕ)
    {t : ℝ≥0} (ht : invSuccTime n ≤ t) :
    |a k t - limitAfterPositiveTimes a t| ≤
      |a k t - a k (invSuccTime n) - incrementLimitAfter a n t| + a k (invSuccTime n) + c := by
  rw [limitAfterPositiveTimes_eq_add hmono hnn hconv hfreq ht]
  have h1 := le_abs_self (a k t - a k (invSuccTime n) - incrementLimitAfter a n t)
  have h2 := neg_abs_le (a k t - a k (invSuccTime n) - incrementLimitAfter a n t)
  have h3 := hnn k (invSuccTime n)
  have h4 := limitAfterPositiveTimes_invSuccTime_nonneg hmono hnn hconv hfreq
  have h5 := limitAfterPositiveTimes_invSuccTime_le hmono hnn hconv hfreq
  rw [abs_le]
  constructor <;> linarith

/-- Deterministic bound before the time `δ n`, for paths whose values at `δ n` are frequently
below `c`. -/
theorem abs_sub_limitAfterPositiveTimes_le_of_ge (hmono : ∀ k, Monotone (a k))
    (hnn : ∀ k t, 0 ≤ a k t)
    (hconv : ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (invSuccTime m)) atTop (𝓝 L))
    {n : ℕ} {c : ℝ} (hfreq : ∃ᶠ k in atTop, a k (invSuccTime n) < c) (k : ℕ)
    {t : ℝ≥0} (ht : t ≤ invSuccTime n) :
    |a k t - limitAfterPositiveTimes a t| ≤ a k (invSuccTime n) + c := by
  obtain ⟨h1, h2⟩ := limitAfterPositiveTimes_mem_Icc_of_le hmono hnn hconv hfreq ht
  have h3 := limitAfterPositiveTimes_invSuccTime_le hmono hnn hconv hfreq
  have h4 := hnn k t
  have h5 := hmono k ht
  rw [abs_le]
  constructor <;> linarith

end Deterministic

section Probabilistic

variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]

/-- **Uniform convergence in measure from convergence after each positive time.** If, after each
time `δ n = (n + 1)⁻¹`, the increments of nondecreasing continuous nonnegative random functions
`A k` form almost surely a uniform Cauchy sequence on every `[δ n, T]`, and their values at `δ n`
are small in measure uniformly in `k` as `n → ∞`, then `A k` converges in measure, uniformly on
`[0, T]`, to `limitAfterPositiveTimes (fun j => A j ω)`. -/
theorem tendsto_measure_exists_le_abs_sub_limitAfterPositiveTimes
    (A : ℕ → Ω → ℝ≥0 → ℝ) (hmono : ∀ k ω, Monotone (A k ω)) (hnn : ∀ k ω t, 0 ≤ A k ω t)
    (hcont : ∀ k ω, Continuous (A k ω)) (hmeas : ∀ k t, Measurable fun ω => A k ω t)
    (hpos : ∀ n (T : ℝ≥0), ∀ᵐ ω ∂Q, UniformCauchySeqOn
      (fun k t => A k ω t - A k ω (invSuccTime n)) atTop (Icc (invSuccTime n) T))
    (hsmall : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => ⨆ k, Q {ω | η ≤ A k ω (invSuccTime n)}) atTop (𝓝 0))
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k => Q {ω | ∃ t ≤ T,
      η ≤ |A k ω t - limitAfterPositiveTimes (fun j => A j ω) t|}) atTop (𝓝 0) := by
  -- the almost sure event of uniform Cauchy increments
  have hgood : ∀ᵐ ω ∂Q, ∀ n (m : ℕ), UniformCauchySeqOn
      (fun k t => A k ω t - A k ω (invSuccTime n)) atTop (Icc (invSuccTime n) (m : ℝ≥0)) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    exact hpos n m
  obtain ⟨N, hN⟩ : ∃ N : Set Ω, N = {ω | ¬ ∀ n (m : ℕ), UniformCauchySeqOn
      (fun k t => A k ω t - A k ω (invSuccTime n)) atTop (Icc (invSuccTime n) (m : ℝ≥0))} :=
    ⟨_, rfl⟩
  have hN0 : Q N = 0 := by
    rw [hN]
    exact ae_iff.1 hgood
  have hucs : ∀ ω ∉ N, ∀ n (T : ℝ≥0), UniformCauchySeqOn
      (fun k t => A k ω t - A k ω (invSuccTime n)) atTop (Icc (invSuccTime n) T) := by
    intro ω hω n T
    rw [hN, mem_ofPred_eq, not_not] at hω
    exact (hω n ⌈T⌉₊).mono (Icc_subset_Icc_right (Nat.le_ceil T))
  have hconv : ∀ ω ∉ N, ∀ m t, invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => A k ω t - A k ω (invSuccTime m)) atTop (𝓝 L) :=
    fun ω hω m t ht => cauchySeq_tendsto_of_complete ((hucs ω hω m t).cauchySeq ⟨ht, le_rfl⟩)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε4 : 0 < ε / 2 / 2 := ENNReal.half_pos (ENNReal.half_pos hε.ne').ne'
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 (hsmall (η / 3) (by positivity)) _ hε4).exists
  -- the three exceptional events
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Set Ω, S = fun k => {ω | η / 3 ≤ A k ω (invSuccTime n)} :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set Ω, B = {ω | ∀ᶠ k in atTop, η / 3 ≤ A k ω (invSuccTime n)} :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Set Ω, D = fun j => ⋃ i ∈ Ici j, ⋃ l ∈ Ici j,
      {ω | ∃ t ∈ Icc (invSuccTime n) T, η / 6 <
        |A i ω t - A i ω (invSuccTime n) - (A l ω t - A l ω (invSuccTime n))|} :=
    ⟨_, rfl⟩
  have hSle : ∀ k, Q (S k) ≤ ε / 2 / 2 := fun k => by
    rw [hS]
    exact (le_iSup (fun k => Q {ω | η / 3 ≤ A k ω (invSuccTime n)}) k).trans hn
  have hBle : Q B ≤ ε / 2 / 2 := by
    have hBeq : B = ⋃ K, ⋂ k ∈ Ici K, S k := by
      ext ω
      simp only [hB, hS, mem_ofPred_eq, eventually_atTop, mem_iUnion, mem_iInter, mem_Ici]
    rw [hBeq, Monotone.measure_iUnion]
    · exact iSup_le fun K => (measure_mono (biInter_subset_of_mem self_mem_Ici)).trans (hSle K)
    · exact fun K K' hKK' => biInter_subset_biInter_left (Ici_subset_Ici.2 hKK')
  have hDmeas : ∀ j, MeasurableSet (D j) := by
    intro j
    rw [hD]
    refine MeasurableSet.biUnion (to_countable _) fun i _ =>
      MeasurableSet.biUnion (to_countable _) fun l _ => ?_
    exact measurableSet_exists_mem_lt_of_continuous
      (fun ω t => |A i ω t - A i ω (invSuccTime n) - (A l ω t - A l ω (invSuccTime n))|)
      (fun ω => continuous_abs.comp (((hcont i ω).sub continuous_const).sub
        ((hcont l ω).sub continuous_const)))
      (fun t => continuous_abs.measurable.comp (((hmeas i t).sub (hmeas i _)).sub
        ((hmeas l t).sub (hmeas l _))))
      _ _
  have hDanti : Antitone D := by
    intro j j' hjj' ω hω
    rw [hD] at hω ⊢
    simp only [mem_iUnion, mem_Ici, exists_prop] at hω ⊢
    obtain ⟨i, hi, l, hl, h⟩ := hω
    exact ⟨i, hjj'.trans hi, l, hjj'.trans hl, h⟩
  have hDinter : Q (⋂ j, D j) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) hN0
    by_contra hωN
    obtain ⟨J, hJ⟩ := Metric.uniformCauchySeqOn_iff.1 (hucs ω hωN n T) (η / 6) (by positivity)
    have hωJ := mem_iInter.1 hω J
    rw [hD] at hωJ
    simp only [mem_iUnion, mem_Ici, exists_prop, mem_ofPred_eq] at hωJ
    obtain ⟨i, hi, l, hl, t, ht, hlt⟩ := hωJ
    have h' := hJ i hi l hl t ht
    simp only [Real.dist_eq] at h'
    linarith
  have hDlim : Tendsto (fun j => Q (D j)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := Q) (fun j => (hDmeas j).nullMeasurableSet) hDanti
      ⟨0, measure_ne_top _ _⟩
    rwa [hDinter] at this
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hDlim _ (ENNReal.half_pos hε.ne')] with k hk
  have hsub : {ω | ∃ t ≤ T, η ≤ |A k ω t - limitAfterPositiveTimes (fun j => A j ω) t|} ⊆
      N ∪ B ∪ S k ∪ D k := by
    rintro ω ⟨t, htT, ht⟩
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨hωN, hωB⟩, hωS⟩, hωD⟩ := hcon
    simp only [hB, mem_ofPred_eq] at hωB
    have hfreq : ∃ᶠ j in atTop, A j ω (invSuccTime n) < η / 3 :=
      (Filter.not_eventually.1 hωB).mono fun j hj => not_le.1 hj
    simp only [hS, mem_ofPred_eq, not_le] at hωS
    rcases le_total (invSuccTime n) t with hδt | htδ
    · have h1 : |A k ω t - limitAfterPositiveTimes (fun j => A j ω) t| ≤
          |A k ω t - A k ω (invSuccTime n) - incrementLimitAfter (fun j => A j ω) n t| +
            A k ω (invSuccTime n) + η / 3 :=
        abs_sub_limitAfterPositiveTimes_le_of_le (a := fun j => A j ω) (fun j => hmono j ω)
          (fun j => hnn j ω) (hconv ω hωN) hfreq k hδt
      have htend : Tendsto (fun j => A j ω t - A j ω (invSuccTime n)) atTop
          (𝓝 (incrementLimitAfter (fun j => A j ω) n t)) :=
        tendsto_incrementLimitAfter (a := fun j => A j ω) (hconv ω hωN) hδt
      obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 htend (η / 6) (by positivity)
      have hj := hJ (max k J) (le_max_right _ _)
      rw [Real.dist_eq] at hj
      have htri := abs_sub_le (A k ω t - A k ω (invSuccTime n))
        (A (max k J) ω t - A (max k J) ω (invSuccTime n))
        (incrementLimitAfter (fun j => A j ω) n t)
      apply hωD
      rw [hD]
      simp only [mem_iUnion, mem_Ici, exists_prop, mem_ofPred_eq]
      refine ⟨k, le_rfl, max k J, le_max_left _ _, t, ⟨hδt, htT⟩, ?_⟩
      linarith
    · have h2 : |A k ω t - limitAfterPositiveTimes (fun j => A j ω) t| ≤
          A k ω (invSuccTime n) + η / 3 :=
        abs_sub_limitAfterPositiveTimes_le_of_ge (a := fun j => A j ω) (fun j => hmono j ω)
          (fun j => hnn j ω) (hconv ω hωN) hfreq k htδ
      linarith
  calc Q {ω | ∃ t ≤ T, η ≤ |A k ω t - limitAfterPositiveTimes (fun j => A j ω) t|}
      ≤ Q (N ∪ B ∪ S k ∪ D k) := measure_mono hsub
    _ ≤ Q N + Q B + Q (S k) + Q (D k) := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ 0 + ε / 2 / 2 + ε / 2 / 2 + ε / 2 := by
        rw [hN0]
        exact add_le_add (add_le_add (add_le_add le_rfl hBle) (hSle k)) hk
    _ = ε := by rw [zero_add, ENNReal.add_halves, ENNReal.add_halves]

end Probabilistic

end LatticeProb
