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

open MeasureTheory Filter

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
end LatticeProb

end
