/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.Quantile at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Generalized quantiles of probability measures on `ℝ`

For a measure `μ` on `ℝ` and a level `p ∈ (0,1)` (in `ℝ≥0∞`), `q` is a *`p`-quantile* of `μ`
if `p ≤ μ (Iic q)` and `1 - p ≤ μ (Ici q)` (`IsQuantile`). The median is the case `p = 1/2`
(`LQGMetric.Prob.Median`). This is the "generalized quantile" convention of the project
(blueprint DDDF.D2.len, proposed deviation D-DDDF-4): DDDF define quantiles by `P(L ≤ ℓ) = p`.

Main results (for a probability measure `μ` and `0 < p < 1`):
* `lowerQuantile μ p = sInf {x | p ≤ μ (Iic x)}` and `upperQuantile μ p = sSup {x | 1 - p ≤
  μ (Ici x)}` are quantiles, `lowerQuantile ≤ upperQuantile`;
* `setOf_isQuantile_eq_Icc`: the set of `p`-quantiles is `Icc (lowerQuantile μ p)
  (upperQuantile μ p)`, a nonempty compact interval.

Source: elementary (right-continuity of the distribution function); own elementary proof.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- `q` is a (generalized) `p`-quantile of `μ`: `μ(-∞,q] ≥ p` and `μ[q,∞) ≥ 1 - p`. -/
def IsQuantile (μ : Measure ℝ) (p : ℝ≥0∞) (q : ℝ) : Prop :=
  p ≤ μ (Iic q) ∧ 1 - p ≤ μ (Ici q)

/-- The lower `p`-quantile `inf {x | μ(-∞,x] ≥ p}`. -/
def lowerQuantile (μ : Measure ℝ) (p : ℝ≥0∞) : ℝ := sInf {x | p ≤ μ (Iic x)}

/-- The upper `p`-quantile `sup {x | μ[x,∞) ≥ 1 - p}`. -/
def upperQuantile (μ : Measure ℝ) (p : ℝ≥0∞) : ℝ := sSup {x | 1 - p ≤ μ (Ici x)}

variable {μ : Measure ℝ} {p c : ℝ≥0∞}

/-! ### One-sided continuity of `μ(-∞,x]` and `μ[x,∞)` -/

lemma one_div_succ_pos' (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- Right-continuity of `x ↦ μ(-∞,x]` (lower bound form). -/
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
      have := one_div_succ_pos' n
      linarith
  have hanti : Antitone (fun n : ℕ => Iio (x + 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    refine Iio_subset_Iio ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun _ => measurableSet_Iio.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hI] at ht
  exact ge_of_tendsto' ht fun n => h _ (by have := one_div_succ_pos' n; linarith)

/-- Left-continuity of `x ↦ μ[x,∞)` (lower bound form). -/
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
      have := one_div_succ_pos' n
      linarith
  have hanti : Antitone (fun n : ℕ => Ioi (x - 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    refine Ioi_subset_Ioi ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun _ => measurableSet_Ioi.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hI] at ht
  exact ge_of_tendsto' ht fun n => h _ (by have := one_div_succ_pos' n; linarith)

lemma le_measure_Iic_of_forall_lt [IsFiniteMeasure μ] {x : ℝ}
    (h : ∀ y, x < y → c ≤ μ (Iic y)) : c ≤ μ (Iic x) := by
  refine le_measure_Iic_of_forall_lt_Iio fun y hy => ?_
  refine (h ((x + y) / 2) (by linarith)).trans (measure_mono fun z hz => ?_)
  simp only [mem_Iic, mem_Iio] at hz ⊢
  linarith

lemma le_measure_Ici_of_forall_gt [IsFiniteMeasure μ] {x : ℝ}
    (h : ∀ y, y < x → c ≤ μ (Ici y)) : c ≤ μ (Ici x) := by
  refine le_measure_Ici_of_forall_gt_Ioi fun y hy => ?_
  refine (h ((x + y) / 2) (by linarith)).trans (measure_mono fun z hz => ?_)
  simp only [mem_Ici, mem_Ioi] at hz ⊢
  linarith

/-! ### Tails -/

section prob
variable [IsProbabilityMeasure μ]

lemma tendsto_measure_Iic_atTop_one : Tendsto (fun x => μ (Iic x)) atTop (𝓝 1) := by
  simpa using tendsto_measure_Iic_atTop μ

lemma tendsto_measure_Iic_atBot_zero : Tendsto (fun x => μ (Iic x)) atBot (𝓝 0) := by
  have h := (ENNReal.tendsto_ofReal (ProbabilityTheory.tendsto_cdf_atBot (μ := μ)))
  simpa [ProbabilityTheory.ofReal_cdf] using h

lemma tendsto_measure_Ici_atBot_one : Tendsto (fun x => μ (Ici x)) atBot (𝓝 1) := by
  simpa using tendsto_measure_Ici_atBot μ

lemma measure_Ioi_eq_one_sub (x : ℝ) : μ (Ioi x) = 1 - μ (Iic x) := by
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]

lemma measure_Iio_eq_one_sub (x : ℝ) : μ (Iio x) = 1 - μ (Ici x) := by
  rw [← compl_Ici, prob_compl_eq_one_sub measurableSet_Ici]

lemma tendsto_measure_Ioi_atTop_zero : Tendsto (fun x => μ (Ioi x)) atTop (𝓝 0) := by
  simp_rw [measure_Ioi_eq_one_sub]
  simpa using ENNReal.Tendsto.sub tendsto_const_nhds tendsto_measure_Iic_atTop_one
    (Or.inl ENNReal.one_ne_top)

omit [IsProbabilityMeasure μ] in
lemma one_sub_pos_of_lt_one (hp1 : p < 1) : 0 < 1 - p := tsub_pos_of_lt hp1

omit [IsProbabilityMeasure μ] in
lemma one_sub_lt_one_of_pos (hp0 : 0 < p) : 1 - p < 1 :=
  ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne'

/-! ### The two defining sets -/

variable (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

set_option linter.unusedSectionVars false in
lemma bddBelow_setOf_le_measure_Iic : BddBelow {x : ℝ | p ≤ μ (Iic x)} := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Iic_atBot_zero (μ := μ)).eventually (eventually_lt_nhds hp0)).exists
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  exact absurd hx (not_le.2 ((measure_mono (Iic_subset_Iic.2 hlt.le)).trans_lt hx0))

set_option linter.unusedSectionVars false in
lemma nonempty_setOf_le_measure_Iic : {x : ℝ | p ≤ μ (Iic x)}.Nonempty := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Iic_atTop_one (μ := μ)).eventually (eventually_gt_nhds hp1)).exists
  exact ⟨x0, hx0.le⟩

set_option linter.unusedSectionVars false in
lemma bddAbove_setOf_le_measure_Ici : BddAbove {x : ℝ | 1 - p ≤ μ (Ici x)} := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Ioi_atTop_zero (μ := μ)).eventually
    (eventually_lt_nhds (one_sub_pos_of_lt_one hp1))).exists
  refine ⟨x0 + 1, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  refine absurd hx (not_le.2 (lt_of_le_of_lt (measure_mono fun z hz => ?_) hx0))
  simp only [mem_Ici, mem_Ioi] at hz ⊢
  linarith

set_option linter.unusedSectionVars false in
lemma nonempty_setOf_le_measure_Ici : {x : ℝ | 1 - p ≤ μ (Ici x)}.Nonempty := by
  obtain ⟨x0, hx0⟩ := ((tendsto_measure_Ici_atBot_one (μ := μ)).eventually
    (eventually_gt_nhds (one_sub_lt_one_of_pos hp0))).exists
  exact ⟨x0, hx0.le⟩

/-- `μ(-∞,x] ≥ p` iff `x ≥ lowerQuantile μ p`. -/
lemma le_measure_Iic_iff_lowerQuantile_le {x : ℝ} : p ≤ μ (Iic x) ↔ lowerQuantile μ p ≤ x := by
  constructor
  · exact fun hx => csInf_le (bddBelow_setOf_le_measure_Iic hp0 hp1) hx
  · intro hx
    have hmem : p ≤ μ (Iic (lowerQuantile μ p)) := by
      refine le_measure_Iic_of_forall_lt fun y hy => ?_
      obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt (nonempty_setOf_le_measure_Iic hp0 hp1) hy
      exact hs.trans (measure_mono (Iic_subset_Iic.2 hsy.le))
    exact hmem.trans (measure_mono (Iic_subset_Iic.2 hx))

/-- `μ[x,∞) ≥ 1 - p` iff `x ≤ upperQuantile μ p`. -/
lemma le_measure_Ici_iff_le_upperQuantile {x : ℝ} :
    1 - p ≤ μ (Ici x) ↔ x ≤ upperQuantile μ p := by
  constructor
  · exact fun hx => le_csSup (bddAbove_setOf_le_measure_Ici hp0 hp1) hx
  · intro hx
    have hmem : 1 - p ≤ μ (Ici (upperQuantile μ p)) := by
      refine le_measure_Ici_of_forall_gt fun y hy => ?_
      obtain ⟨s, hs, hsy⟩ := exists_lt_of_lt_csSup (nonempty_setOf_le_measure_Ici hp0 hp1) hy
      exact hs.trans (measure_mono (Ici_subset_Ici.2 hsy.le))
    exact hmem.trans (measure_mono (Ici_subset_Ici.2 hx))

lemma measure_Iic_lt_of_lt_lowerQuantile {x : ℝ} (hx : x < lowerQuantile μ p) :
    μ (Iic x) < p :=
  not_le.1 fun h => absurd ((le_measure_Iic_iff_lowerQuantile_le hp0 hp1).1 h) (not_le.2 hx)

lemma measure_Ici_lt_of_upperQuantile_lt {x : ℝ} (hx : upperQuantile μ p < x) :
    μ (Ici x) < 1 - p :=
  not_le.1 fun h => absurd ((le_measure_Ici_iff_le_upperQuantile hp0 hp1).1 h) (not_le.2 hx)

/-- The lower quantile satisfies the upper tail bound. -/
lemma le_measure_Ici_lowerQuantile : 1 - p ≤ μ (Ici (lowerQuantile μ p)) := by
  refine le_measure_Ici_of_forall_gt_Ioi fun y hy => ?_
  rw [measure_Ioi_eq_one_sub]
  exact tsub_le_tsub_left (measure_Iic_lt_of_lt_lowerQuantile hp0 hp1 hy).le 1

lemma lowerQuantile_le_upperQuantile : lowerQuantile μ p ≤ upperQuantile μ p :=
  (le_measure_Ici_iff_le_upperQuantile hp0 hp1).1 (le_measure_Ici_lowerQuantile hp0 hp1)

lemma isQuantile_iff_mem_Icc {q : ℝ} :
    IsQuantile μ p q ↔ q ∈ Icc (lowerQuantile μ p) (upperQuantile μ p) := by
  rw [IsQuantile, le_measure_Iic_iff_lowerQuantile_le hp0 hp1,
    le_measure_Ici_iff_le_upperQuantile hp0 hp1]
  rfl

lemma isQuantile_lowerQuantile : IsQuantile μ p (lowerQuantile μ p) :=
  (isQuantile_iff_mem_Icc hp0 hp1).2 ⟨le_rfl, lowerQuantile_le_upperQuantile hp0 hp1⟩

lemma isQuantile_upperQuantile : IsQuantile μ p (upperQuantile μ p) :=
  (isQuantile_iff_mem_Icc hp0 hp1).2 ⟨lowerQuantile_le_upperQuantile hp0 hp1, le_rfl⟩

end prob

end LQGMetric
