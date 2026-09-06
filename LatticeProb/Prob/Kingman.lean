/-
Kingman's subadditive ergodic theorem: the part that is reachable, and what is
missing.

A family `g n` is subadditive along `T` when `g (m + n) x ≤ g m x + g n (T^m x)`.
Kingman's theorem says that if `T` preserves a probability measure and the means
are bounded below then `g n / n` converges almost everywhere and in `L¹` to a
`T`-invariant limit whose mean is `inf_n (∫ g n) / n`.

What is proved here is the statement about the means: they form a subadditive
sequence, because `T` preserves the measure, so Fekete's lemma applies and
`(∫ g n) / n` converges to its infimum.  That is the deterministic half, and it
is what identifies the limit once the almost sure convergence is known.

The almost sure half is not proved here, and the obstruction is named: Mathlib
4.32 has no pointwise (Birkhoff) ergodic theorem.  The first step of the chain
that leads to one is `LatticeProb.maximal_ergodic`, proved in
`LatticeProb/Prob/MaximalErgodic.lean`; from it Birkhoff follows by the standard
argument on the invariant sets where the lower limit is below `α` and the upper
limit above `β`, and Kingman follows from Birkhoff by Steele's argument.  Until
those land, the full statement is `LatticeProb.External.KingmanSubadditive`.
-/
import Mathlib
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

end Low

end LatticeProb

end
