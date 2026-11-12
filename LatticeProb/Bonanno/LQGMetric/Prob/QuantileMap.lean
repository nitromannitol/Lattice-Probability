/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.QuantileMap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.Quantile

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Quantiles: equivariance and uniqueness

* `IsQuantile.map_monotone`: a monotone measurable map sends `p`-quantiles of `μ` to
  `p`-quantiles of the pushforward.
* `isQuantile_map_affine_iff`, `lowerQuantile_map_affine`, `upperQuantile_map_affine`
  (and the scaling versions `…_map_mul`): quantiles of `a • X + b` for `a > 0`.
* `measure_Ioo_eq_zero_of_isQuantile`: between two `p`-quantiles the measure has no mass.
  Uniqueness criteria: `lowerQuantile_eq_upperQuantile_of_measure_Ioo_pos` and the
  "no gap" form `lowerQuantile_eq_upperQuantile_of_noGap` (the form of GM.S1.18).
* `eq_one_of_isQuantile_map_mul`: if `μ` has a unique `p`-quantile `1` and `1` is also a
  `p`-quantile of `μ ∘ (c ·)⁻¹`, `c > 0`, then `c = 1` (GM §1.4 "median 1 ⇒ constant 1").

Source: elementary; own elementary proof.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

variable {μ : Measure ℝ} {p : ℝ≥0∞}

/-! ### Pushforward under monotone and affine maps -/

lemma IsQuantile.map_monotone {g : ℝ → ℝ} (hg : Monotone g) (hgm : Measurable g) {q : ℝ}
    (hq : IsQuantile μ p q) : IsQuantile (μ.map g) p (g q) := by
  refine ⟨?_, ?_⟩
  · rw [Measure.map_apply hgm measurableSet_Iic]
    exact hq.1.trans (measure_mono fun z hz => hg hz)
  · rw [Measure.map_apply hgm measurableSet_Ici]
    exact hq.2.trans (measure_mono fun z hz => hg hz)

lemma measurable_affine (a b : ℝ) : Measurable (fun x : ℝ => a * x + b) := by fun_prop

/-- `q` is a `p`-quantile of the law of `aX + b` (`a > 0`) iff `(q - b)/a` is one of `X`. -/
lemma isQuantile_map_affine_iff {a : ℝ} (ha : 0 < a) (b : ℝ) {q : ℝ} :
    IsQuantile (μ.map (fun x => a * x + b)) p q ↔ IsQuantile μ p ((q - b) / a) := by
  have h1 : (fun x : ℝ => a * x + b) ⁻¹' Iic q = Iic ((q - b) / a) := by
    ext z
    simp only [mem_preimage, mem_Iic, le_div_iff₀ ha]
    constructor <;> intro h <;> linarith
  have h2 : (fun x : ℝ => a * x + b) ⁻¹' Ici q = Ici ((q - b) / a) := by
    ext z
    simp only [mem_preimage, mem_Ici, div_le_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [IsQuantile, IsQuantile, Measure.map_apply (measurable_affine a b) measurableSet_Iic,
    Measure.map_apply (measurable_affine a b) measurableSet_Ici, h1, h2]

lemma map_mul_eq_map_affine (a : ℝ) :
    μ.map (fun x => a * x) = μ.map (fun x => a * x + 0) := by
  simp only [add_zero]

section prob
variable [IsProbabilityMeasure μ]

variable (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

end prob

lemma isQuantile_map_mul_iff {a : ℝ} (ha : 0 < a) {q : ℝ} :
    IsQuantile (μ.map (fun x => a * x)) p q ↔ IsQuantile μ p (q / a) := by
  rw [map_mul_eq_map_affine, isQuantile_map_affine_iff ha, sub_zero]

/-! ### Uniqueness -/

section prob
variable [IsProbabilityMeasure μ]

/-- `μ(-∞,a] + μ(a,b) + μ[b,∞) = 1` for `a < b`. -/
lemma measure_Iic_add_Ioo_add_Ici {a b : ℝ} (hab : a < b) :
    μ (Iic a) + μ (Ioo a b) + μ (Ici b) = 1 := by
  have hd : Disjoint (Iic a) (Ioo a b) :=
    Set.disjoint_left.2 fun z h1 h2 => (not_lt.2 h1) h2.1
  rw [← measure_union hd measurableSet_Ioo, Iic_union_Ioo_eq_Iio hab, measure_Iio_eq_one_sub,
    tsub_add_cancel_of_le prob_le_one]

/-- Between two `p`-quantiles there is no mass. -/
lemma measure_Ioo_eq_zero_of_isQuantile (hp1 : p ≤ 1) {a b : ℝ} (hab : a < b)
    (ha : IsQuantile μ p a) (hb : IsQuantile μ p b) : μ (Ioo a b) = 0 := by
  have h := measure_Iic_add_Ioo_add_Ici (μ := μ) hab
  have h' : p + μ (Ioo a b) + (1 - p) ≤ 1 :=
    (add_le_add (add_le_add ha.1 le_rfl) hb.2).trans h.le
  rw [add_right_comm, add_tsub_cancel_of_le hp1] at h'
  have : 1 + μ (Ioo a b) ≤ 1 + 0 := by simpa using h'
  exact le_antisymm ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 this) bot_le

variable (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

/-- Uniqueness criterion: `μ` charges every interval `(a,b)` to the right of a quantile `a`. -/
lemma lowerQuantile_eq_upperQuantile_of_measure_Ioo_pos
    (h : ∀ a b, a < b → IsQuantile μ p a → 0 < μ (Ioo a b)) :
    lowerQuantile μ p = upperQuantile μ p := by
  refine le_antisymm (lowerQuantile_le_upperQuantile hp0 hp1) (not_lt.1 fun hlt => ?_)
  have h0 := measure_Ioo_eq_zero_of_isQuantile hp1.le hlt (isQuantile_lowerQuantile hp0 hp1)
    (isQuantile_upperQuantile hp0 hp1)
  exact (h _ _ hlt (isQuantile_lowerQuantile hp0 hp1)).ne' h0

/-- Uniqueness criterion ("no gap", the form of GM.S1.18): if `μ(-∞,a] > 0` and `a < b`
imply `μ(a,b) > 0`, the `p`-quantile is unique. -/
lemma lowerQuantile_eq_upperQuantile_of_noGap
    (h : ∀ a b, a < b → 0 < μ (Iic a) → 0 < μ (Ioo a b)) :
    lowerQuantile μ p = upperQuantile μ p :=
  lowerQuantile_eq_upperQuantile_of_measure_Ioo_pos hp0 hp1 fun a b hab ha =>
    h a b hab (hp0.trans_le ha.1)

lemma isQuantile_iff_eq_lowerQuantile (hU : lowerQuantile μ p = upperQuantile μ p) {q : ℝ} :
    IsQuantile μ p q ↔ q = lowerQuantile μ p := by
  rw [isQuantile_iff_mem_Icc hp0 hp1, ← hU, Icc_self, mem_singleton_iff]

/-- If `p`-quantiles of `μ` are unique, any two `p`-quantiles agree. -/
lemma IsQuantile.eq_of_unique (hU : lowerQuantile μ p = upperQuantile μ p) {q q' : ℝ}
    (hq : IsQuantile μ p q) (hq' : IsQuantile μ p q') : q = q' :=
  ((isQuantile_iff_eq_lowerQuantile hp0 hp1 hU).1 hq).trans
    ((isQuantile_iff_eq_lowerQuantile hp0 hp1 hU).1 hq').symm

/-- GM §1.4: if `1` is the unique `p`-quantile of `X` and also a `p`-quantile of `cX`
(`c > 0`), then `c = 1`. -/
lemma eq_one_of_isQuantile_map_mul (hU : lowerQuantile μ p = upperQuantile μ p)
    (h1 : IsQuantile μ p 1) {c : ℝ} (hc : 0 < c) (hc1 : IsQuantile (μ.map (fun x => c * x)) p 1) :
    c = 1 := by
  have := (isQuantile_map_mul_iff hc).1 hc1
  have he := this.eq_of_unique hp0 hp1 hU h1
  field_simp at he
  linarith

end prob

end LQGMetric
