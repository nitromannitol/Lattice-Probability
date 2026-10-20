/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/Quantile.lean.
-/
import Mathlib.Probability.CDF

/-!
# Generalized quantiles of probability measures on `ℝ`

For a measure `μ` on `ℝ` and a level `p ∈ ℝ≥0∞`, `q` is a *`p`-quantile* of `μ` if
`p ≤ μ (Iic q)` and `1 - p ≤ μ (Ici q)` (`IsQuantile`). The defining conditions are inequalities,
not the equation `μ (Iic q) = p`, so the set of `p`-quantiles is in general a nondegenerate
closed interval. The median is the case `p = 1/2`.

Main results (for a probability measure `μ` and `0 < p < 1`):
* `lowerQuantile μ p = sInf {x | p ≤ μ (Iic x)}` and `upperQuantile μ p = sSup {x | 1 - p ≤
  μ (Ici x)}` are quantiles, and `lowerQuantile μ p ≤ upperQuantile μ p`;
* `isQuantile_iff_mem_Icc`: the set of `p`-quantiles is `Icc (lowerQuantile μ p)
  (upperQuantile μ p)`.

The proofs use the right-continuity of the distribution function.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb

/-- `q` is a (generalized) `p`-quantile of `μ`: `p ≤ μ (-∞,q]` and `1 - p ≤ μ [q,∞)`. -/
def IsQuantile (μ : Measure ℝ) (p : ℝ≥0∞) (q : ℝ) : Prop :=
  p ≤ μ (Iic q) ∧ 1 - p ≤ μ (Ici q)

/-- The lower `p`-quantile `inf {x | μ (-∞,x] ≥ p}`. -/
def lowerQuantile (μ : Measure ℝ) (p : ℝ≥0∞) : ℝ := sInf {x | p ≤ μ (Iic x)}

/-- The upper `p`-quantile `sup {x | μ [x,∞) ≥ 1 - p}`. -/
def upperQuantile (μ : Measure ℝ) (p : ℝ≥0∞) : ℝ := sSup {x | 1 - p ≤ μ (Ici x)}

variable {μ : Measure ℝ} {p c : ℝ≥0∞}

/-! ### One-sided continuity of `μ (-∞,x]` and `μ [x,∞)` -/

/-- `0 < 1 / (n + 1)` for a natural number `n`. -/
lemma one_div_natCast_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- Right-continuity of `x ↦ μ (Iic x)`, lower bound form: if `c ≤ μ (Iio y)` for every `y > x`,
then `c ≤ μ (Iic x)`. -/
lemma le_measure_Iic_of_forall_lt_Iio [IsFiniteMeasure μ] {x : ℝ}
    (h : ∀ y, x < y → c ≤ μ (Iio y)) : c ≤ μ (Iic x) := by
  have hI : (⋂ n : ℕ, Iio (x + 1 / ((n : ℝ) + 1))) = Iic x := by
    ext z
    simp only [mem_iInter, mem_Iio, mem_Iic]
    constructor
    · intro hz
      by_contra hzx
      push Not at hzx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hzx)
      have := hz n
      linarith
    · intro hz n
      have := one_div_natCast_succ_pos n
      linarith
  have hanti : Antitone (fun n : ℕ => Iio (x + 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    refine Iio_subset_Iio ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun _ => measurableSet_Iio.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hI] at ht
  exact ge_of_tendsto' ht fun n => h _ (by have := one_div_natCast_succ_pos n; linarith)

/-- Left-continuity of `x ↦ μ (Ici x)`, lower bound form: if `c ≤ μ (Ioi y)` for every `y < x`,
then `c ≤ μ (Ici x)`. -/
lemma le_measure_Ici_of_forall_gt_Ioi [IsFiniteMeasure μ] {x : ℝ}
    (h : ∀ y, y < x → c ≤ μ (Ioi y)) : c ≤ μ (Ici x) := by
  have hI : (⋂ n : ℕ, Ioi (x - 1 / ((n : ℝ) + 1))) = Ici x := by
    ext z
    simp only [mem_iInter, mem_Ioi, mem_Ici]
    constructor
    · intro hz
      by_contra hzx
      push Not at hzx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hzx)
      have := hz n
      linarith
    · intro hz n
      have := one_div_natCast_succ_pos n
      linarith
  have hanti : Antitone (fun n : ℕ => Ioi (x - 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    refine Ioi_subset_Ioi ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun _ => measurableSet_Ioi.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hI] at ht
  exact ge_of_tendsto' ht fun n => h _ (by have := one_div_natCast_succ_pos n; linarith)

/-- Right-continuity of `x ↦ μ (Iic x)` in the form using `Iic` on the right-hand side of the
hypothesis: if `c ≤ μ (Iic y)` for every `y > x`, then `c ≤ μ (Iic x)`. -/
lemma le_measure_Iic_of_forall_lt [IsFiniteMeasure μ] {x : ℝ}
    (h : ∀ y, x < y → c ≤ μ (Iic y)) : c ≤ μ (Iic x) := by
  refine le_measure_Iic_of_forall_lt_Iio fun y hy => ?_
  refine (h ((x + y) / 2) (by linarith)).trans (measure_mono fun z hz => ?_)
  simp only [mem_Iic, mem_Iio] at hz ⊢
  linarith

/-- Left-continuity of `x ↦ μ (Ici x)` in the form using `Ici` on the right-hand side of the
hypothesis: if `c ≤ μ (Ici y)` for every `y < x`, then `c ≤ μ (Ici x)`. -/
lemma le_measure_Ici_of_forall_gt [IsFiniteMeasure μ] {x : ℝ}
    (h : ∀ y, y < x → c ≤ μ (Ici y)) : c ≤ μ (Ici x) := by
  refine le_measure_Ici_of_forall_gt_Ioi fun y hy => ?_
  refine (h ((x + y) / 2) (by linarith)).trans (measure_mono fun z hz => ?_)
  simp only [mem_Ici, mem_Ioi] at hz ⊢
  linarith

/-- `0 < 1 - p` whenever `p < 1`. -/
lemma one_sub_pos_of_lt_one (hp1 : p < 1) : 0 < 1 - p := tsub_pos_of_lt hp1

/-- `1 - p < 1` whenever `0 < p`. -/
lemma one_sub_lt_one_of_pos (hp0 : 0 < p) : 1 - p < 1 :=
  ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne'

/-! ### Tails -/

section prob
variable [IsProbabilityMeasure μ]

/-- For a probability measure, `μ (Iic x) → 1` as `x → ∞`. -/
lemma tendsto_measure_Iic_atTop_one : Tendsto (fun x => μ (Iic x)) atTop (𝓝 1) := by
  simpa using tendsto_measure_Iic_atTop μ

/-- For a probability measure, `μ (Iic x) → 0` as `x → -∞`. -/
lemma tendsto_measure_Iic_atBot_zero : Tendsto (fun x => μ (Iic x)) atBot (𝓝 0) := by
  have h := (ENNReal.tendsto_ofReal (ProbabilityTheory.tendsto_cdf_atBot (μ := μ)))
  simpa [ProbabilityTheory.ofReal_cdf] using h

/-- For a probability measure, `μ (Ici x) → 1` as `x → -∞`. -/
lemma tendsto_measure_Ici_atBot_one : Tendsto (fun x => μ (Ici x)) atBot (𝓝 1) := by
  simpa using tendsto_measure_Ici_atBot μ

/-- The mass of the open right half-line is the complement of the closed left half-line. -/
lemma measure_Ioi_eq_one_sub (x : ℝ) : μ (Ioi x) = 1 - μ (Iic x) := by
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]

/-- The mass of the open left half-line is the complement of the closed right half-line. -/
lemma measure_Iio_eq_one_sub (x : ℝ) : μ (Iio x) = 1 - μ (Ici x) := by
  rw [← compl_Ici, prob_compl_eq_one_sub measurableSet_Ici]

/-- For a probability measure, `μ (Ioi x) → 0` as `x → ∞`. -/
lemma tendsto_measure_Ioi_atTop_zero : Tendsto (fun x => μ (Ioi x)) atTop (𝓝 0) := by
  simp_rw [measure_Ioi_eq_one_sub]
  simpa using ENNReal.Tendsto.sub tendsto_const_nhds tendsto_measure_Iic_atTop_one
    (Or.inl ENNReal.one_ne_top)

/-! ### The two defining sets -/

/-- The set of `x` with `p ≤ μ (Iic x)` is bounded below when `0 < p`. -/
lemma bddBelow_setOf_le_measure_Iic (hp0 : 0 < p) (_hp1 : p < 1) :
    BddBelow {x : ℝ | p ≤ μ (Iic x)} := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Iic_atBot_zero (μ := μ)).eventually
    (eventually_lt_nhds hp0)).exists
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  exact absurd hx (not_le.2 ((measure_mono (Iic_subset_Iic.2 hlt.le)).trans_lt hx0))

/-- The set of `x` with `p ≤ μ (Iic x)` is nonempty when `p < 1`. -/
lemma nonempty_setOf_le_measure_Iic (_hp0 : 0 < p) (hp1 : p < 1) :
    {x : ℝ | p ≤ μ (Iic x)}.Nonempty := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Iic_atTop_one (μ := μ)).eventually
    (eventually_gt_nhds hp1)).exists
  exact ⟨x0, hx0.le⟩

/-- The set of `x` with `1 - p ≤ μ (Ici x)` is bounded above when `p < 1`. -/
lemma bddAbove_setOf_le_measure_Ici (_hp0 : 0 < p) (hp1 : p < 1) :
    BddAbove {x : ℝ | 1 - p ≤ μ (Ici x)} := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Ioi_atTop_zero (μ := μ)).eventually
    (eventually_lt_nhds (one_sub_pos_of_lt_one hp1))).exists
  refine ⟨x0 + 1, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  refine absurd hx (not_le.2 (lt_of_le_of_lt (measure_mono fun z hz => ?_) hx0))
  simp only [mem_Ici, mem_Ioi] at hz ⊢
  linarith

/-- The set of `x` with `1 - p ≤ μ (Ici x)` is nonempty when `0 < p`. -/
lemma nonempty_setOf_le_measure_Ici (hp0 : 0 < p) (_hp1 : p < 1) :
    {x : ℝ | 1 - p ≤ μ (Ici x)}.Nonempty := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Ici_atBot_one (μ := μ)).eventually
    (eventually_gt_nhds (one_sub_lt_one_of_pos hp0))).exists
  exact ⟨x0, hx0.le⟩

/-- `p ≤ μ (Iic x)` iff `lowerQuantile μ p ≤ x`, for `0 < p < 1`. -/
lemma le_measure_Iic_iff_lowerQuantile_le (hp0 : 0 < p) (hp1 : p < 1) {x : ℝ} :
    p ≤ μ (Iic x) ↔ lowerQuantile μ p ≤ x := by
  constructor
  · exact fun hx => csInf_le (bddBelow_setOf_le_measure_Iic hp0 hp1) hx
  · intro hx
    have hmem : p ≤ μ (Iic (lowerQuantile μ p)) := by
      refine le_measure_Iic_of_forall_lt fun y hy => ?_
      obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt (nonempty_setOf_le_measure_Iic hp0 hp1) hy
      exact hs.trans (measure_mono (Iic_subset_Iic.2 hsy.le))
    exact hmem.trans (measure_mono (Iic_subset_Iic.2 hx))

/-- `1 - p ≤ μ (Ici x)` iff `x ≤ upperQuantile μ p`, for `0 < p < 1`. -/
lemma le_measure_Ici_iff_le_upperQuantile (hp0 : 0 < p) (hp1 : p < 1) {x : ℝ} :
    1 - p ≤ μ (Ici x) ↔ x ≤ upperQuantile μ p := by
  constructor
  · exact fun hx => le_csSup (bddAbove_setOf_le_measure_Ici hp0 hp1) hx
  · intro hx
    have hmem : 1 - p ≤ μ (Ici (upperQuantile μ p)) := by
      refine le_measure_Ici_of_forall_gt fun y hy => ?_
      obtain ⟨s, hs, hsy⟩ := exists_lt_of_lt_csSup (nonempty_setOf_le_measure_Ici hp0 hp1) hy
      exact hs.trans (measure_mono (Ici_subset_Ici.2 hsy.le))
    exact hmem.trans (measure_mono (Ici_subset_Ici.2 hx))

/-- Mass strictly to the left of `x < lowerQuantile μ p` is less than `p`. -/
lemma measure_Iic_lt_of_lt_lowerQuantile (hp0 : 0 < p) (hp1 : p < 1) {x : ℝ}
    (hx : x < lowerQuantile μ p) : μ (Iic x) < p :=
  not_le.1 fun h => absurd ((le_measure_Iic_iff_lowerQuantile_le hp0 hp1).1 h) (not_le.2 hx)

/-- Mass strictly to the right of `x > upperQuantile μ p` is less than `1 - p`. -/
lemma measure_Ici_lt_of_upperQuantile_lt (hp0 : 0 < p) (hp1 : p < 1) {x : ℝ}
    (hx : upperQuantile μ p < x) : μ (Ici x) < 1 - p :=
  not_le.1 fun h => absurd ((le_measure_Ici_iff_le_upperQuantile hp0 hp1).1 h) (not_le.2 hx)

/-- The lower quantile satisfies the upper tail bound. -/
lemma le_measure_Ici_lowerQuantile (hp0 : 0 < p) (hp1 : p < 1) :
    1 - p ≤ μ (Ici (lowerQuantile μ p)) := by
  refine le_measure_Ici_of_forall_gt_Ioi fun y hy => ?_
  rw [measure_Ioi_eq_one_sub]
  exact tsub_le_tsub_left (measure_Iic_lt_of_lt_lowerQuantile hp0 hp1 hy).le 1

/-- The lower quantile is at most the upper quantile, for `0 < p < 1`. -/
lemma lowerQuantile_le_upperQuantile (hp0 : 0 < p) (hp1 : p < 1) :
    lowerQuantile μ p ≤ upperQuantile μ p :=
  (le_measure_Ici_iff_le_upperQuantile hp0 hp1).1 (le_measure_Ici_lowerQuantile hp0 hp1)

/-- For `0 < p < 1`, `q` is a `p`-quantile iff it lies in `[lowerQuantile μ p, upperQuantile μ p]`. -/
lemma isQuantile_iff_mem_Icc (hp0 : 0 < p) (hp1 : p < 1) {q : ℝ} :
    IsQuantile μ p q ↔ q ∈ Icc (lowerQuantile μ p) (upperQuantile μ p) := by
  rw [IsQuantile, le_measure_Iic_iff_lowerQuantile_le hp0 hp1,
    le_measure_Ici_iff_le_upperQuantile hp0 hp1]
  rfl

/-- The lower quantile is a `p`-quantile, for `0 < p < 1`. -/
lemma isQuantile_lowerQuantile (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuantile μ p (lowerQuantile μ p) :=
  (isQuantile_iff_mem_Icc hp0 hp1).2 ⟨le_rfl, lowerQuantile_le_upperQuantile hp0 hp1⟩

/-- The upper quantile is a `p`-quantile, for `0 < p < 1`. -/
lemma isQuantile_upperQuantile (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuantile μ p (upperQuantile μ p) :=
  (isQuantile_iff_mem_Icc hp0 hp1).2 ⟨lowerQuantile_le_upperQuantile hp0 hp1, le_rfl⟩

end prob

/-! ### Nonvacuity -/

namespace QuantileExample

/-- The hypotheses of the quantile results are satisfied by a real probability measure: the Dirac
mass at `0` has a `1/2`-quantile, namely its lower quantile. -/
example : ∃ q : ℝ, IsQuantile (Measure.dirac (0 : ℝ)) (2⁻¹ : ℝ≥0∞) q :=
  ⟨_, isQuantile_lowerQuantile (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
    (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)⟩

end QuantileExample

end LatticeProb

end
