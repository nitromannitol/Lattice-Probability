/-
Kingman's subadditive ergodic theorem.

A family `g n` is subadditive along `T` when `g (m + n) x ≤ g m x + g n (T^m x)`.
Kingman's theorem says that if `T` preserves a finite measure and the family is
bounded below then `g n / n` converges almost everywhere to a `T`-invariant
limit, and that the means `(∫ g n) / n` converge to their infimum.

Both halves are proved here.  The deterministic half is `tendsto_integral_div`:
the means form a subadditive sequence because `T` preserves the measure, so
Fekete's lemma applies.  The almost sure half is `ae_tendsto_gLow` for a
nonnegative family, and `ae_tendsto_div` for a family bounded below by `c * n`,
which is the form every application uses.  The limit is the lower limit `gLow`,
which is invariant almost everywhere by `ae_gLow_comp`.

The proof of the almost sure half is Steele's.  The upper bound comes from
iterating subadditivity, which dominates `g n` by the `n`-th Birkhoff sum of
`g 1`, so `ae_limsup_div_le` bounds the upper limit by the Birkhoff limit of
`g 1`, using the pointwise ergodic theorem of `LatticeProb/Prob/Birkhoff.lean`.
The lower bound is the block decomposition: for a horizon `N` and a tolerance
`ε`, split `[0, m)` greedily into blocks on which the family already beats
`gLow + ε` and single steps elsewhere; the cost of the single steps is
`costFn`, whose mean tends to zero as `N` grows; the set where its Birkhoff
averages stay large is then shrunk by the maximal ergodic theorem.
-/import Mathlib
import LatticeProb.Prob.Birkhoff

noncomputable section

namespace LatticeProb

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- A family subadditive along `T`. -/
def SubadditiveAlong (T : Ω → Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∀ (m n : ℕ) (x : Ω), g (m + n) x ≤ g m x + g n (T^[m] x)

theorem integrable_comp_iterate (hT : MeasurePreserving T μ μ) {h : Ω → ℝ}
    (hh : Integrable h μ) (m : ℕ) : Integrable (fun x => h (T^[m] x)) μ := by
  have hcopy := hh
  rw [← (hT.iterate m).map_eq] at hcopy
  exact (integrable_map_measure hcopy.aestronglyMeasurable
    (hT.measurable.iterate m).aemeasurable).mp hcopy

theorem integral_comp_iterate (hT : MeasurePreserving T μ μ) {h : Ω → ℝ}
    (hh : Integrable h μ) (m : ℕ) : ∫ x, h (T^[m] x) ∂μ = ∫ x, h x ∂μ := by
  conv_rhs => rw [← (hT.iterate m).map_eq]
  rw [integral_map (hT.measurable.iterate m).aemeasurable
    (by rw [(hT.iterate m).map_eq]; exact hh.aestronglyMeasurable)]

/-- The means of a family subadditive along a measure-preserving transformation
form a subadditive sequence. -/
theorem subadditive_integral (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : SubadditiveAlong T g) (hint : ∀ n, Integrable (g n) μ) :
    Subadditive fun n => ∫ x, g n x ∂μ := by
  intro m n
  have h1 : Integrable (fun x => g m x + g n (T^[m] x)) μ :=
    (hint m).add (integrable_comp_iterate hT (hint n) m)
  calc ∫ x, g (m + n) x ∂μ
      ≤ ∫ x, (g m x + g n (T^[m] x)) ∂μ :=
        integral_mono (hint (m + n)) h1 fun x => hsub m n x
    _ = (∫ x, g m x ∂μ) + ∫ x, g n (T^[m] x) ∂μ :=
        integral_add (hint m) (integrable_comp_iterate hT (hint n) m)
    _ = (∫ x, g m x ∂μ) + ∫ x, g n x ∂μ := by
        rw [integral_comp_iterate hT (hint n) m]

/-- **The mean half of Kingman's theorem.**  For a family subadditive along a
measure-preserving transformation whose means divided by `n` are bounded below,
`(∫ g n) / n` converges to its infimum. -/
theorem tendsto_integral_div (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : SubadditiveAlong T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g n x ∂μ) / n)) :
    Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop
      (nhds (subadditive_integral hT hsub hint).lim) :=
  (subadditive_integral hT hsub hint).tendsto_lim hbdd

/-- The limit of the means is at most every one of them. -/
theorem lim_integral_le (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : SubadditiveAlong T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g n x ∂μ) / n)) {n : ℕ} (hn : n ≠ 0) :
    (subadditive_integral hT hsub hint).lim ≤ (∫ x, g n x ∂μ) / n :=
  (subadditive_integral hT hsub hint).lim_le_div hbdd hn

omit [MeasurableSpace Ω] in
/-- The Birkhoff sums of an integrable function are subadditive along `T`, with
equality; so Kingman's theorem contains Birkhoff's. -/
theorem subadditiveAlong_birkhoffSum (T : Ω → Ω) (f : Ω → ℝ) :
    SubadditiveAlong T fun n => birkhoffSum T f n := by
  intro m n x
  show birkhoffSum T f (m + n) x ≤ birkhoffSum T f m x + birkhoffSum T f n (T^[m] x)
  rw [birkhoffSum_add]

/-! ### The subadditive family is dominated by the Birkhoff sums of its first term -/

omit [MeasurableSpace Ω] in
/-- Iterating subadditivity: `g n` is at most the `n`-th Birkhoff sum of `g 1`. -/
theorem le_birkhoffSum_of_subadditiveAlong {g : ℕ → Ω → ℝ} (hsub : SubadditiveAlong T g)
    (x : Ω) : ∀ n : ℕ, 1 ≤ n → g n x ≤ birkhoffSum T (g 1) n x := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [birkhoffSum]
      · have h1 : g (n + 1) x ≤ g n x + g 1 (T^[n] x) := hsub n 1 x
        have h2 : birkhoffSum T (g 1) (n + 1) x
            = birkhoffSum T (g 1) n x + g 1 (T^[n] x) := birkhoffSum_succ T (g 1) n x
        have h3 := ih hn
        linarith [h1, h2, h3]

omit [MeasurableSpace Ω] in
/-- Hence the averages of a subadditive family are dominated by the Birkhoff
averages of its first term. -/
theorem div_le_bAvg_of_subadditiveAlong {g : ℕ → Ω → ℝ} (hsub : SubadditiveAlong T g)
    (x : Ω) {n : ℕ} (hn : 1 ≤ n) : g n x / n ≤ bAvg T (g 1) n x := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [bAvg, div_le_div_iff_of_pos_right hn0]
  exact le_birkhoffSum_of_subadditiveAlong hsub x n hn

/-- For a subadditive family the upper limit of `g n / n` is at most the
Birkhoff limit of `g 1`, almost everywhere.  With a family bounded below this
is a genuine real bound and is the first half of Kingman's theorem. -/
theorem ae_limsup_div_le [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {g : ℕ → Ω → ℝ} (hsub : SubadditiveAlong T g) (hg1m : Measurable (g 1))
    (hg1 : Integrable (g 1) μ) {c : ℝ} (hlow : ∀ n x, 1 ≤ n → c ≤ g n x / n) :
    ∀ᵐ x ∂μ, limsup (fun n => g n x / n) atTop ≤ bLimsup T (g 1) x := by
  filter_upwards [ae_tendsto_bLimsup hT hg1m hg1] with x hx
  have hb : ∀ n : ℕ, min c 0 ≤ g n x / (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact le_trans (min_le_left _ _) (hlow n x hn)
  refine limsup_le_limsup ?_ (isBoundedUnder_ge_of hb).isCoboundedUnder_le
    hx.isBoundedUnder_le
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact div_le_bAvg_of_subadditiveAlong hsub x hn
/-! ### Steele's block decomposition

Fix a point `x`, a level `a`, and a horizon `N`.  A time `k` along the orbit is
*good* when the family already beats `a` within `N` steps from there.  Splitting
`[j, j + m)` greedily into the blocks the good times provide and single steps
elsewhere bounds `g m` at `T^j x` by `m a`, plus the cost of the single steps,
plus a boundary term over the last `N` times. -/

section Block

variable {g : ℕ → Ω → ℝ}

open scoped Classical in
omit [MeasurableSpace Ω] in
/-- The cost charged at a time that is not good. -/
def blockCost (T : Ω → Ω) (g : ℕ → Ω → ℝ) (a : ℝ) (N : ℕ) (x : Ω) (k : ℕ) : ℝ :=
  if ∃ n, 1 ≤ n ∧ n ≤ N ∧ g n (T^[k] x) < n * a then 0 else max (g 1 (T^[k] x) - a) 0

omit [MeasurableSpace Ω] in
/-- The boundary term, charged over the last `N` times. -/
def blockTail (T : Ω → Ω) (g : ℕ → Ω → ℝ) (a : ℝ) (x : Ω) (k : ℕ) : ℝ :=
  g 1 (T^[k] x) + a

omit [MeasurableSpace Ω] in
theorem blockCost_nonneg (T : Ω → Ω) (g : ℕ → Ω → ℝ) (a : ℝ) (N : ℕ) (x : Ω) (k : ℕ) :
    0 ≤ blockCost T g a N x k := by
  classical
  rw [blockCost]
  split
  · exact le_rfl
  · exact le_max_right _ _

omit [MeasurableSpace Ω] in
theorem blockTail_nonneg {a : ℝ} (ha : 0 ≤ a) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (T : Ω → Ω) (x : Ω) (k : ℕ) : 0 ≤ blockTail T g a x k := by
  rw [blockTail]
  have := hg 1 (T^[k] x) le_rfl
  linarith

omit [MeasurableSpace Ω] in
/-- **The block bound.** -/
theorem block_bound (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (x : Ω) {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 1 ≤ N) :
    ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ,
      g m (T^[j] x) ≤ m * a
        + ∑ k ∈ Finset.Ico j (j + m), blockCost T g a N x k
        + ∑ k ∈ Finset.Ico (j + m - N) (j + m), blockTail T g a x k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm j
    have hcostnn : ∀ k, 0 ≤ blockCost T g a N x k := blockCost_nonneg T g a N x
    have htailnn : ∀ k, 0 ≤ blockTail T g a x k := blockTail_nonneg ha hg T x
    have hcostsum : 0 ≤ ∑ k ∈ Finset.Ico j (j + m), blockCost T g a N x k :=
      Finset.sum_nonneg fun k _ => hcostnn k
    by_cases hmN : m ≤ N
    · -- short: single steps all the way
      have h1 : g m (T^[j] x) ≤ birkhoffSum T (g 1) m (T^[j] x) :=
        le_birkhoffSum_of_subadditiveAlong hsub _ m hm
      have h2 : birkhoffSum T (g 1) m (T^[j] x)
          = ∑ k ∈ Finset.Ico j (j + m), g 1 (T^[k] x) := by
        rw [Finset.sum_Ico_eq_sum_range, birkhoffSum]
        simp only [Nat.add_sub_cancel_left]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Function.iterate_add_apply T i j x, Nat.add_comm i j]
      have hsubset : Finset.Ico j (j + m) ⊆ Finset.Ico (j + m - N) (j + m) :=
        Finset.Ico_subset_Ico (by omega) le_rfl
      have h3 : ∑ k ∈ Finset.Ico j (j + m), g 1 (T^[k] x)
          ≤ ∑ k ∈ Finset.Ico (j + m - N) (j + m), blockTail T g a x k := by
        refine le_trans (Finset.sum_le_sum fun k _ => ?_)
          (Finset.sum_le_sum_of_subset_of_nonneg hsubset fun k _ _ => htailnn k)
        rw [blockTail]; linarith
      have h4 : (0 : ℝ) ≤ m * a := by positivity
      linarith [h1, h2 ▸ h1, h3]
    · push Not at hmN
      by_cases hgood : ∃ n, 1 ≤ n ∧ n ≤ N ∧ g n (T^[j] x) < n * a
      · obtain ⟨n, hn1, hnN, hnlt⟩ := hgood
        have hnm : n < m := by omega
        have hstep : g m (T^[j] x) ≤ g n (T^[j] x) + g (m - n) (T^[j + n] x) := by
          have := hsub n (m - n) (T^[j] x)
          rw [show n + (m - n) = m by omega] at this
          rw [show T^[n] (T^[j] x) = T^[j + n] x by
            rw [← Function.iterate_add_apply T n j x]; congr 1; omega] at this
          exact this
        have hIH := ih (m - n) (by omega) (by omega) (j + n)
        rw [show j + n + (m - n) = j + m by omega] at hIH
        have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
          push_cast [Nat.cast_sub (le_of_lt hnm)]; ring
        rw [hcast] at hIH
        have hshrink : ∑ k ∈ Finset.Ico (j + n) (j + m), blockCost T g a N x k
            ≤ ∑ k ∈ Finset.Ico j (j + m), blockCost T g a N x k :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Ico_subset_Ico (by omega) le_rfl) fun k _ _ => hcostnn k
        linarith [hstep, hIH, hshrink]
      · have hone : g 1 (T^[j] x) ≤ a + blockCost T g a N x j := by
          rw [blockCost, if_neg hgood]
          have := le_max_left (g 1 (T^[j] x) - a) 0
          linarith
        have hstep : g m (T^[j] x) ≤ g 1 (T^[j] x) + g (m - 1) (T^[j + 1] x) := by
          have := hsub 1 (m - 1) (T^[j] x)
          rw [show 1 + (m - 1) = m by omega] at this
          rw [show T^[1] (T^[j] x) = T^[j + 1] x by
            rw [← Function.iterate_add_apply T 1 j x]; congr 1; omega] at this
          exact this
        have hIH := ih (m - 1) (by omega) (by omega) (j + 1)
        rw [show j + 1 + (m - 1) = j + m by omega] at hIH
        have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          push_cast [Nat.cast_sub hm]; ring
        rw [hcast] at hIH
        have hsplit : ∑ k ∈ Finset.Ico j (j + m), blockCost T g a N x k
            = blockCost T g a N x j + ∑ k ∈ Finset.Ico (j + 1) (j + m),
              blockCost T g a N x k :=
          Finset.sum_eq_sum_Ico_succ_bot (by omega) _
        linarith [hstep, hIH, hone, hsplit]

end Block

/-! ### The lower Kingman limit -/

section Low

variable {g : ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem liminf_le_liminf_of_le_add {u v : ℕ → ℝ}
    (hu : IsBoundedUnder (· ≤ ·) atTop u) (hv : IsBoundedUnder (· ≥ ·) atTop v)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (h : ∀ᶠ n in atTop, v n ≤ u n + δ n) :
    liminf v atTop ≤ liminf u atTop := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs1, hs2⟩ := exists_between hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between hs2
  have hvE : ∀ᶠ n in atTop, t < v n := eventually_lt_of_lt_liminf ht2 hv
  have huF : ∃ᶠ n in atTop, u n < s :=
    frequently_lt_of_liminf_lt hu.isCoboundedUnder_ge hs1
  have hd : ∀ᶠ n in atTop, δ n < t - s := by
    have hpos : (0 : ℝ) < t - s := by linarith
    have := NormedAddGroup.tendsto_nhds_zero.mp hδ (t - s) hpos
    filter_upwards [this] with n hn
    exact lt_of_le_of_lt (le_abs_self _) hn
  obtain ⟨n, hn⟩ := (huF.and_eventually (hvE.and (hd.and h))).exists
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
  linarith

/-- The lower limit of `g n / n`. -/
def gLow (g : ℕ → Ω → ℝ) (x : Ω) : ℝ := liminf (fun n => g n x / n) atTop

theorem measurable_gLow (hgm : ∀ n, Measurable (g n)) : Measurable (gLow g) :=
  Measurable.liminf fun n => (hgm n).div measurable_const

omit [MeasurableSpace Ω] in
theorem div_nonneg_of (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y) (x : Ω) (n : ℕ) :
    0 ≤ g n x / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · exact div_nonneg (hg n x hn) (by positivity)

omit [MeasurableSpace Ω] in
theorem gLow_nonneg (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y) {x : Ω}
    (hb : IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ)) : 0 ≤ gLow g x :=
  le_liminf_of_le hb.isCoboundedUnder_ge
    (Filter.Eventually.of_forall fun n => div_nonneg_of hg x n)

omit [MeasurableSpace Ω] in
/-- On the set where the Birkhoff averages of `g 1` converge, the averages of a
nonnegative subadditive family are bounded. -/
theorem isBoundedUnder_div (hsub : SubadditiveAlong T g) {x : Ω} {L : ℝ}
    (hx : Tendsto (fun n => bAvg T (g 1) n x) atTop (𝓝 L)) :
    IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ) := by
  obtain ⟨C, hC⟩ := hx.isBoundedUnder_le
  refine ⟨C, ?_⟩
  rw [Filter.eventually_map] at hC ⊢
  filter_upwards [hC, eventually_ge_atTop 1] with n hn hn1
  exact le_trans (div_le_bAvg_of_subadditiveAlong hsub x hn1) hn

omit [MeasurableSpace Ω] in
/-- On the set where the Birkhoff averages of `g 1` converge at `x` and at
`T x`, the lower limit does not decrease along `T`. -/
theorem gLow_le_gLow_comp (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    {x : Ω} {L' : ℝ}
    (hTx : Tendsto (fun n => bAvg T (g 1) n (T x)) atTop (𝓝 L')) :
    gLow g x ≤ gLow g (T x) := by
  set u : ℕ → ℝ := fun n => g n (T x) / (n : ℝ) with hu
  set v : ℕ → ℝ := fun n => g (n + 1) x / ((n + 1 : ℕ) : ℝ) with hv
  have hub : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_div hsub hTx
  have hvb : IsBoundedUnder (· ≥ ·) atTop v :=
    isBoundedUnder_ge_of fun n => div_nonneg_of hg x (n + 1)
  have hδ : Tendsto (fun n : ℕ => g 1 x / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (g 1 x)
    exact h.comp (tendsto_add_atTop_nat 1)
  have hle : ∀ᶠ n in atTop, v n ≤ u n + g 1 x / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hstep : g (n + 1) x ≤ g 1 x + g n (T x) := by
      have h := hsub 1 n x
      rw [Nat.add_comm 1 n] at h
      simpa using h
    have hmid : g n (T x) / ((n + 1 : ℕ) : ℝ) ≤ u n := by
      rw [hu]
      refine div_le_div_of_nonneg_left (hg n (T x) hn) hn0 ?_
      push_cast
      linarith
    rw [hv]
    simp only
    rw [div_le_iff₀ hn1]
    have hexp : (u n + g 1 x / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ)
        = u n * ((n + 1 : ℕ) : ℝ) + g 1 x := by field_simp
    rw [hexp]
    have hmid' : g n (T x) ≤ u n * ((n + 1 : ℕ) : ℝ) := by
      rw [← div_le_iff₀ hn1] at *
      exact hmid
    linarith
  have h1 : liminf v atTop ≤ liminf u atTop :=
    liminf_le_liminf_of_le_add hub hvb hδ hle
  have h2 : liminf v atTop = gLow g x := by
    rw [hv, gLow]
    exact liminf_nat_add (fun n => g n x / (n : ℝ)) 1
  rwa [h2] at h1

/-- The lower limit is almost everywhere invariant. -/
theorem ae_gLow_comp [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (hgm : ∀ n, Measurable (g n)) (hg1 : Integrable (g 1) μ) :
    ∀ᵐ x ∂μ, gLow g (T x) = gLow g x := by
  have hbirk := ae_tendsto_bLimsup hT (hgm 1) hg1
  have hbirkT : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T (g 1) n (T x)) atTop
      (𝓝 (bLimsup T (g 1) (T x))) := hT.quasiMeasurePreserving.ae hbirk
  have hmono : ∀ᵐ x ∂μ, gLow g x ≤ gLow g (T x) := by
    filter_upwards [hbirkT] with x hx
    exact gLow_le_gLow_comp hsub hg hx
  set A : Ω → ℝ := fun x => Real.arctan (gLow g x) with hA
  have hAm : Measurable A := Real.continuous_arctan.measurable.comp (measurable_gLow hgm)
  have hAb : ∀ x, ‖A x‖ ≤ Real.pi / 2 := by
    intro x
    rw [hA, Real.norm_eq_abs, abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  have hAi : Integrable A μ :=
    Integrable.of_bound hAm.aestronglyMeasurable (Real.pi / 2)
      (Filter.Eventually.of_forall hAb)
  have hATi : Integrable (fun x => A (T x)) μ := by
    have hcopy := hAi
    rw [← hT.map_eq] at hcopy
    exact (integrable_map_measure hcopy.aestronglyMeasurable
      hT.measurable.aemeasurable).mp hcopy
  have hint : ∫ x, (A (T x) - A x) ∂μ = 0 := by
    have hTA : ∫ x, A (T x) ∂μ = ∫ x, A x ∂μ := by
      have h := integral_comp_iterate (m := 1) hT hAi
      simpa using h
    rw [integral_sub hATi hAi, hTA]
    ring
  have hnn : 0 ≤ᵐ[μ] fun x => A (T x) - A x := by
    filter_upwards [hmono] with x hx
    have := Real.arctan_le_arctan_iff.mpr hx
    simpa [hA] using this
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn (hATi.sub hAi)).mp hint
  filter_upwards [hzero] with x hx
  have : Real.arctan (gLow g (T x)) = Real.arctan (gLow g x) := by
    have h := hx
    simp only [Pi.zero_apply, hA, sub_eq_zero] at h
    exact h
  exact Real.arctan_injective this

/-! ### The cost as a function on the space -/

open scoped Classical in
/-- The cost charged at a point that is not good for the level `gLow + ε` within
`N` steps. -/
def costFn (g : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) (y : Ω) : ℝ :=
  if ∃ n, 1 ≤ n ∧ n ≤ N ∧ g n y < n * (gLow g y + ε) then 0
  else max (g 1 y - (gLow g y + ε)) 0

omit [MeasurableSpace Ω] in
theorem costFn_nonneg (g : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) (y : Ω) :
    0 ≤ costFn g ε N y := by
  classical
  rw [costFn]
  split
  · exact le_rfl
  · exact le_max_right _ _

omit [MeasurableSpace Ω] in
/-- The cost is dominated by the first term of the family. -/
theorem costFn_le (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    {x : Ω} (hb : IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ)) :
    costFn g ε N x ≤ g 1 x := by
  classical
  rw [costFn]
  split
  · exact hg 1 x le_rfl
  · refine max_le ?_ (hg 1 x le_rfl)
    have := gLow_nonneg hg hb
    linarith

theorem measurable_costFn (hgm : ∀ n, Measurable (g n)) (ε : ℝ) (N : ℕ) :
    Measurable (costFn g ε N) := by
  classical
  have hset : MeasurableSet
      {y : Ω | ∃ n, 1 ≤ n ∧ n ≤ N ∧ g n y < n * (gLow g y + ε)} := by
    have : {y : Ω | ∃ n, 1 ≤ n ∧ n ≤ N ∧ g n y < n * (gLow g y + ε)}
        = ⋃ n ∈ Finset.Icc 1 N, {y : Ω | g n y < n * (gLow g y + ε)} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
      constructor
      · rintro ⟨n, h1, h2, h3⟩; exact ⟨n, ⟨h1, h2⟩, h3⟩
      · rintro ⟨n, ⟨h1, h2⟩, h3⟩; exact ⟨n, h1, h2, h3⟩
    rw [this]
    refine MeasurableSet.biUnion (Finset.countable_toSet _) fun n _ => ?_
    exact measurableSet_lt (hgm n)
      (measurable_const.mul ((measurable_gLow hgm).add measurable_const))
  refine Measurable.ite hset measurable_const ?_
  exact ((hgm 1).sub ((measurable_gLow hgm).add measurable_const)).max measurable_const

omit [MeasurableSpace Ω] in
/-- Enlarging the horizon does not increase the cost. -/
theorem costFn_antitone (g : ℕ → Ω → ℝ) (ε : ℝ) {N N' : ℕ} (h : N ≤ N')
    (y : Ω) : costFn g ε N' y ≤ costFn g ε N y := by
  classical
  rw [costFn, costFn]
  by_cases hN : ∃ n, 1 ≤ n ∧ n ≤ N ∧ g n y < n * (gLow g y + ε)
  · obtain ⟨n, h1, h2, h3⟩ := hN
    rw [if_pos ⟨n, h1, le_trans h2 h, h3⟩, if_pos ⟨n, h1, h2, h3⟩]
  · rw [if_neg hN]
    split
    · exact le_max_right _ _
    · exact le_rfl

omit [MeasurableSpace Ω] in
/-- For a point whose averages are bounded, the cost vanishes once the horizon is
large enough. -/
theorem exists_costFn_eq_zero {ε : ℝ} (hε : 0 < ε)
    {x : Ω} (hb : IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ)) :
    ∃ N, 1 ≤ N ∧ costFn g ε N x = 0 := by
  classical
  have hfreq : ∃ᶠ n in atTop, g n x / (n : ℝ) < gLow g x + ε :=
    frequently_lt_of_liminf_lt hb.isCoboundedUnder_ge (by simp [gLow]; linarith)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine ⟨n, hn2, ?_⟩
  rw [div_lt_iff₀ hn0] at hn1
  rw [costFn, if_pos ⟨n, hn2, le_rfl, by linarith⟩]

/-! ### The upper limit is at most the lower limit plus the cost -/

omit [MeasurableSpace Ω] in
theorem sum_Ico_eq_birkhoffSum_sub (T : Ω → Ω) (h : Ω → ℝ) (x : Ω) {m N : ℕ}
    (hNm : N ≤ m) :
    ∑ k ∈ Finset.Ico (m - N) m, h (T^[k] x)
      = birkhoffSum T h m x - birkhoffSum T h (m - N) x := by
  have hsum : (∑ k ∈ Finset.Ico 0 (m - N), h (T^[k] x))
      + ∑ k ∈ Finset.Ico (m - N) m, h (T^[k] x)
      = ∑ k ∈ Finset.Ico 0 m, h (T^[k] x) :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  rw [birkhoffSum, birkhoffSum, Finset.range_eq_Ico, Finset.range_eq_Ico]
  linarith

omit [MeasurableSpace Ω] in
/-- The block bound divided by `m`, then passed to the limit. -/
theorem limsup_div_le_add_cost (hsub : SubadditiveAlong T g)
    (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N)
    {x : Ω} {L LC : ℝ}
    (hinv : ∀ k, gLow g (T^[k] x) = gLow g x)
    (hL : Tendsto (fun m => bAvg T (g 1) m x) atTop (𝓝 L))
    (hLC : Tendsto (fun m => bAvg T (costFn g ε N) m x) atTop (𝓝 LC)) :
    limsup (fun m => g m x / (m : ℝ)) atTop ≤ gLow g x + ε + LC := by
  classical
  set a : ℝ := gLow g x + ε with hadef
  have hb : IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ) :=
    isBoundedUnder_div hsub hL
  have ha : 0 ≤ a := by
    have := gLow_nonneg hg hb
    linarith
  have hcost : ∀ k, blockCost T g a N x k = costFn g ε N (T^[k] x) := by
    intro k
    rw [blockCost, costFn, hinv k]
  have htail : ∀ k, blockTail T g a x k = g 1 (T^[k] x) + a := fun k => rfl
  -- the bound for `m ≥ N`
  have hbound : ∀ m : ℕ, N ≤ m → g m x / (m : ℝ)
      ≤ a + bAvg T (costFn g ε N) m x
        + (bAvg T (g 1) m x - birkhoffSum T (g 1) (m - N) x / (m : ℝ))
        + (N : ℝ) * a / (m : ℝ) := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans hN hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hblk := block_bound hsub hg x ha hN m hm1 0
    simp only [Nat.zero_add] at hblk
    have e1 : ∑ k ∈ Finset.Ico 0 m, blockCost T g a N x k
        = birkhoffSum T (costFn g ε N) m x := by
      rw [birkhoffSum, Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun k _ => hcost k
    have e2 : ∑ k ∈ Finset.Ico (m - N) m, blockTail T g a x k
        = (birkhoffSum T (g 1) m x - birkhoffSum T (g 1) (m - N) x) + (N : ℝ) * a := by
      have hcard : (Finset.Ico (m - N) m).card = N := by
        rw [Nat.card_Ico]; omega
      rw [Finset.sum_congr rfl fun k _ => htail k, Finset.sum_add_distrib,
        sum_Ico_eq_birkhoffSum_sub T (g 1) x hm, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [e1, e2] at hblk
    rw [div_le_iff₀ hm0]
    have hexp : (a + bAvg T (costFn g ε N) m x
        + (bAvg T (g 1) m x - birkhoffSum T (g 1) (m - N) x / (m : ℝ))
        + (N : ℝ) * a / (m : ℝ)) * (m : ℝ)
        = (m : ℝ) * a + birkhoffSum T (costFn g ε N) m x
          + (birkhoffSum T (g 1) m x - birkhoffSum T (g 1) (m - N) x) + (N : ℝ) * a := by
      rw [bAvg, bAvg]
      field_simp
    rw [hexp]
    simp only [Function.iterate_zero, id_eq] at hblk
    linarith [hblk]
  -- the right-hand side converges
  set w : ℕ → ℝ := fun m => a + bAvg T (costFn g ε N) m x
      + (bAvg T (g 1) m x - birkhoffSum T (g 1) (m - N) x / (m : ℝ))
      + (N : ℝ) * a / (m : ℝ) with hw
  have hshift : Tendsto (fun m : ℕ => birkhoffSum T (g 1) (m - N) x / (m : ℝ)) atTop
      (𝓝 L) := by
    have hratio : Tendsto (fun m : ℕ => ((m - N : ℕ) : ℝ) / (m : ℝ)) atTop (𝓝 1) := by
      have heq : ∀ m : ℕ, N ≤ m → ((m - N : ℕ) : ℝ) / (m : ℝ) = 1 - (N : ℝ) / (m : ℝ) := by
        intro m hm
        have hm0 : (m : ℝ) ≠ 0 := by
          have : 0 < m := by omega
          exact_mod_cast (by omega : m ≠ 0)
        rw [Nat.cast_sub hm]
        field_simp
      have h1 : Tendsto (fun m : ℕ => 1 - (N : ℝ) / (m : ℝ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ))
      rw [show (1 : ℝ) = 1 - 0 by ring]
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop N] with m hm
      exact (heq m hm).symm
    have hsub' : Tendsto (fun m : ℕ => bAvg T (g 1) (m - N) x) atTop (𝓝 L) :=
      hL.comp (tendsto_sub_atTop_nat N)
    have hprod := hratio.mul hsub'
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    rcases Nat.eq_zero_or_pos (m - N) with h0 | h0
    · rw [h0]
      simp [bAvg, birkhoffSum]
    · have hmN : ((m - N : ℕ) : ℝ) ≠ 0 := by
        have : 0 < m - N := h0
        exact_mod_cast (by omega : m - N ≠ 0)
      rw [bAvg]
      field_simp
  have hwlim : Tendsto w atTop (𝓝 (a + LC + (L - L) + 0)) := by
    refine Tendsto.add (Tendsto.add (tendsto_const_nhds.add hLC) (hL.sub hshift)) ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat ((N : ℝ) * a))
  rw [show a + LC + (L - L) + 0 = a + LC by ring] at hwlim
  have hcob : IsCoboundedUnder (· ≤ ·) atTop fun m => g m x / (m : ℝ) :=
    (isBoundedUnder_ge_of fun n => div_nonneg_of hg x n).isCoboundedUnder_le
  have hle : limsup (fun m => g m x / (m : ℝ)) atTop ≤ limsup w atTop := by
    refine limsup_le_limsup ?_ hcob hwlim.isBoundedUnder_le
    filter_upwards [eventually_ge_atTop N] with m hm
    exact hbound m hm
  rwa [hwlim.limsup_eq] at hle

end Low

/-! ### The cost is eventually negligible -/

section Cost

variable {g : ℕ → Ω → ℝ}

theorem ae_gLow_iterate [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (hgm : ∀ n, Measurable (g n)) (hg1 : Integrable (g 1) μ) :
    ∀ᵐ x ∂μ, ∀ k : ℕ, gLow g (T^[k] x) = gLow g x := by
  have hstep : ∀ k : ℕ, ∀ᵐ x ∂μ, gLow g (T^[k + 1] x) = gLow g (T^[k] x) := by
    intro k
    have h := (hT.iterate k).quasiMeasurePreserving.ae
      (ae_gLow_comp hT hsub hg hgm hg1)
    filter_upwards [h] with x hx
    rw [show T^[k + 1] x = T (T^[k] x) by
      rw [Function.iterate_succ_apply']]
    exact hx
  rw [← ae_all_iff] at hstep
  filter_upwards [hstep] with x hx
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [hx k, ih]

theorem ae_isBoundedUnder_div [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hgm : ∀ n, Measurable (g n))
    (hg1 : Integrable (g 1) μ) :
    ∀ᵐ x ∂μ, IsBoundedUnder (· ≤ ·) atTop fun n => g n x / (n : ℝ) := by
  filter_upwards [ae_tendsto_bLimsup hT (hgm 1) hg1] with x hx
  exact isBoundedUnder_div hsub hx

theorem integrable_costFn [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (hgm : ∀ n, Measurable (g n)) (hg1 : Integrable (g 1) μ) {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) : Integrable (costFn g ε N) μ := by
  refine Integrable.mono' hg1 (measurable_costFn hgm ε N).aestronglyMeasurable ?_
  filter_upwards [ae_isBoundedUnder_div hT hsub hgm hg1] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (costFn_nonneg g ε N x)]
  exact costFn_le hg (le_of_lt hε) N hx

theorem tendsto_integral_costFn [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (hgm : ∀ n, Measurable (g n)) (hg1 : Integrable (g 1) μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => ∫ x, costFn g ε (N + 1) x ∂μ) atTop (𝓝 0) := by
  have hbnd := ae_isBoundedUnder_div hT hsub hgm hg1
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable (fun x => costFn g ε (N + 1) x) μ :=
    fun N => (measurable_costFn hgm ε (N + 1)).aestronglyMeasurable
  have hdom : ∀ N : ℕ, ∀ᵐ x ∂μ, ‖costFn g ε (N + 1) x‖ ≤ g 1 x := by
    intro N
    filter_upwards [hbnd] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (costFn_nonneg g ε (N + 1) x)]
    exact costFn_le hg (le_of_lt hε) (N + 1) hx
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun N : ℕ => costFn g ε (N + 1) x) atTop (𝓝 0) := by
    filter_upwards [hbnd] with x hx
    obtain ⟨N₀, hN₀, hzero⟩ := exists_costFn_eq_zero hε hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have h1 : costFn g ε (N + 1) x ≤ costFn g ε N₀ x :=
      costFn_antitone g ε (by omega) x
    have h2 : 0 ≤ costFn g ε (N + 1) x := costFn_nonneg g ε (N + 1) x
    rw [hzero] at h1
    linarith
  have := tendsto_integral_of_dominated_convergence (g 1) hmeas hg1 hdom hlim
  simpa using this

/-- Almost surely the Birkhoff limit of the cost can be made as small as
wanted by taking the horizon large. -/
theorem ae_exists_bLimsup_costFn_le [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (hgm : ∀ n, Measurable (g n)) (hg1 : Integrable (g 1) μ) {ε : ℝ} (hε : 0 < ε)
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ᵐ x ∂μ, ∃ N : ℕ, 1 ≤ N ∧ bLimsup T (costFn g ε N) x ≤ lam := by
  classical
  set S : ℕ → Set Ω := fun N => {x | lam < bLimsup T (costFn g ε (N + 1)) x} with hS
  have hsubset : ∀ N : ℕ, S N ⊆ maximalSet T (costFn g ε (N + 1)) lam := by
    intro N x hx
    have hnn : ∀ n : ℕ, (0 : ℝ) ≤ bAvg T (costFn g ε (N + 1)) n x := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [bAvg, birkhoffSum]
      · exact div_nonneg (Finset.sum_nonneg fun k _ => costFn_nonneg g ε (N + 1) _)
          (by positivity)
    have hcob : IsCoboundedUnder (· ≤ ·) atTop
        fun n => bAvg T (costFn g ε (N + 1)) n x :=
      (isBoundedUnder_ge_of (C := 0) hnn).isCoboundedUnder_le
    have hfreq : ∃ᶠ n in atTop, lam < bAvg T (costFn g ε (N + 1)) n x :=
      frequently_lt_of_lt_limsup hcob hx
    obtain ⟨n, hn⟩ := hfreq.exists
    have habs : lam < |bAvg T (costFn g ε (N + 1)) n x| :=
      lt_of_lt_of_le hn (le_abs_self _)
    have hmem : x ∈ maximalSet T (fun y => |costFn g ε (N + 1) y|) lam :=
      subset_maximalSet_abs T (costFn g ε (N + 1)) hlam ⟨n, habs⟩
    have hfun : (fun y => |costFn g ε (N + 1) y|) = costFn g ε (N + 1) := by
      funext y
      exact abs_of_nonneg (costFn_nonneg g ε (N + 1) y)
    rwa [hfun] at hmem
  have hbound : ∀ N : ℕ, lam * (μ (⋂ K : ℕ, S K)).toReal
      ≤ ∫ x, costFn g ε (N + 1) x ∂μ := by
    intro N
    have h1 : μ (⋂ K : ℕ, S K) ≤ μ (maximalSet T (costFn g ε (N + 1)) lam) :=
      le_trans (measure_mono (Set.iInter_subset _ N)) (measure_mono (hsubset N))
    have h2 := maximal_inequality hT (measurable_costFn hgm ε (N + 1))
      (integrable_costFn hT hsub hg hgm hg1 hε (N + 1)) hlam
    have h3 : ∫ x, |costFn g ε (N + 1) x| ∂μ = ∫ x, costFn g ε (N + 1) x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x =>
        abs_of_nonneg (costFn_nonneg g ε (N + 1) x))
    have h4 : (μ (⋂ K : ℕ, S K)).toReal
        ≤ (μ (maximalSet T (costFn g ε (N + 1)) lam)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [h3] at h2
    nlinarith [h2, h4, hlam]
  have hzero : μ (⋂ K : ℕ, S K) = 0 := by
    have hlim := tendsto_integral_costFn hT hsub hg hgm hg1 hε
    have hle0 : lam * (μ (⋂ K : ℕ, S K)).toReal ≤ 0 := ge_of_tendsto' hlim hbound
    have hnn : (0 : ℝ) ≤ (μ (⋂ K : ℕ, S K)).toReal := ENNReal.toReal_nonneg
    have hle : (μ (⋂ K : ℕ, S K)).toReal ≤ 0 := by nlinarith
    have heq := le_antisymm hle hnn
    rcases (ENNReal.toReal_eq_zero_iff _).mp heq with h | h
    · exact h
    · exact absurd h (measure_ne_top μ _)
  rw [ae_iff]
  refine measure_mono_null ?_ hzero
  intro x hx
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hx
  exact Set.mem_iInter.mpr fun K => hx (K + 1) (by omega)

/-! ### Kingman's subadditive ergodic theorem -/

/-- **Kingman's subadditive ergodic theorem**, for a nonnegative subadditive
family: `g n / n` converges almost everywhere to the lower limit `gLow g`, which
is measurable and almost everywhere invariant. -/
theorem ae_tendsto_gLow [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hg : ∀ n y, 1 ≤ n → 0 ≤ g n y)
    (hgm : ∀ n, Measurable (g n)) (hg1 : Integrable (g 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => g n x / (n : ℝ)) atTop (𝓝 (gLow g x)) := by
  have hLC : ∀ᵐ x ∂μ, ∀ p : ℕ × ℕ,
      Tendsto (fun m => bAvg T (costFn g (1 / ((p.1 : ℝ) + 1)) (p.2 + 1)) m x) atTop
        (𝓝 (bLimsup T (costFn g (1 / ((p.1 : ℝ) + 1)) (p.2 + 1)) x)) := by
    rw [ae_all_iff]
    intro p
    exact ae_tendsto_bLimsup hT (measurable_costFn hgm _ _)
      (integrable_costFn hT hsub hg hgm hg1 (by positivity) _)
  have hsmall : ∀ᵐ x ∂μ, ∀ p : ℕ × ℕ, ∃ N : ℕ, 1 ≤ N ∧
      bLimsup T (costFn g (1 / ((p.1 : ℝ) + 1)) N) x ≤ 1 / ((p.2 : ℝ) + 1) := by
    rw [ae_all_iff]
    intro p
    exact ae_exists_bLimsup_costFn_le hT hsub hg hgm hg1 (by positivity) (by positivity)
  filter_upwards [ae_isBoundedUnder_div hT hsub hgm hg1,
    ae_gLow_iterate hT hsub hg hgm hg1, ae_tendsto_bLimsup hT (hgm 1) hg1, hLC, hsmall]
    with x hbnd hinv hL hLCx hsmallx
  have hupper : limsup (fun n => g n x / (n : ℝ)) atTop ≤ gLow g x := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0:ℝ) < δ / 2 by linarith)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < δ / 2 by linarith)
    obtain ⟨N, hN1, hNle⟩ := hsmallx (j, k)
    simp only at hNle
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hLCjm := hLCx (j, M)
    simp only at hLCjm
    have hbound := limsup_div_le_add_cost hsub hg
      (show (0:ℝ) < 1 / ((j : ℝ) + 1) by positivity) hN1 hinv hL hLCjm
    linarith [hbound, hNle, hj, hk]
  have hlower : gLow g x ≤ limsup (fun n => g n x / (n : ℝ)) atTop :=
    liminf_le_limsup hbnd (isBoundedUnder_ge_of (C := 0) fun n => div_nonneg_of hg x n)
  have heq : limsup (fun n => g n x / (n : ℝ)) atTop = gLow g x :=
    le_antisymm hupper hlower
  refine tendsto_of_liminf_eq_limsup rfl heq hbnd ?_
  exact isBoundedUnder_ge_of (C := 0) fun n => div_nonneg_of hg x n

/-- **Kingman's subadditive ergodic theorem** for a subadditive family bounded
below linearly: `g n / n` converges almost everywhere.  This is the class every
application uses; the nonnegative case is `c = 0`. -/
theorem ae_tendsto_div [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hsub : SubadditiveAlong T g) (hgm : ∀ n, Measurable (g n))
    (hg1 : Integrable (g 1) μ) {c : ℝ} (hlow : ∀ n y, 1 ≤ n → c * n ≤ g n y) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => g n x / (n : ℝ)) atTop (𝓝 L) := by
  set g' : ℕ → Ω → ℝ := fun n y => g n y - c * n with hg'
  have hsub' : SubadditiveAlong T g' := by
    intro m n x
    have := hsub m n x
    simp only [hg']
    push_cast
    linarith
  have hnn : ∀ n y, 1 ≤ n → 0 ≤ g' n y := by
    intro n y hn
    have := hlow n y hn
    simp only [hg']
    linarith
  have hgm' : ∀ n, Measurable (g' n) := fun n => (hgm n).sub measurable_const
  have hg1' : Integrable (g' 1) μ := by
    simp only [hg']
    exact hg1.sub (integrable_const _)
  filter_upwards [ae_tendsto_gLow hT hsub' hnn hgm' hg1'] with x hx
  refine ⟨gLow g' x + c, ?_⟩
  have heq : ∀ n : ℕ, 1 ≤ n → g n x / (n : ℝ) = g' n x / (n : ℝ) + c := by
    intro n hn
    have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [hg']
    field_simp
    ring
  refine (hx.add tendsto_const_nhds).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (heq n hn).symm

end Cost

end LatticeProb

end
