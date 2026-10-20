/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/QuantileMap.lean.
-/
import LatticeProb.Prob.Quantile

/-!
# Quantiles: equivariance and uniqueness

* `IsQuantile.map_monotone`: a monotone measurable map sends `p`-quantiles of `μ` to
  `p`-quantiles of the pushforward.
* `isQuantile_map_affine_iff` and `isQuantile_map_mul_iff`: the `p`-quantiles of the law of
  `a * X + b` (resp. `a * X`) for `a > 0` are the images of the `p`-quantiles of `X`.
* `measure_Ioo_eq_zero_of_isQuantile`: between two `p`-quantiles the measure has no mass.
  Uniqueness criteria: `lowerQuantile_eq_upperQuantile_of_measure_Ioo_pos` and the
  "no gap" form `lowerQuantile_eq_upperQuantile_of_noGap`.
* `eq_one_of_isQuantile_map_mul`: if `μ` has a unique `p`-quantile `1` and `1` is also a
  `p`-quantile of the pushforward of `μ` under `x ↦ c * x`, `c > 0`, then `c = 1`.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb

variable {μ : Measure ℝ} {p : ℝ≥0∞}

/-! ### Pushforward under monotone and affine maps -/

/-- A monotone measurable map sends a `p`-quantile `q` of `μ` to a `p`-quantile `g q` of the
pushforward `μ.map g`. -/
lemma IsQuantile.map_monotone {g : ℝ → ℝ} (hg : Monotone g) (hgm : Measurable g) {q : ℝ}
    (hq : IsQuantile μ p q) : IsQuantile (μ.map g) p (g q) := by
  refine ⟨?_, ?_⟩
  · rw [Measure.map_apply hgm measurableSet_Iic]
    exact hq.1.trans (measure_mono fun z hz => hg hz)
  · rw [Measure.map_apply hgm measurableSet_Ici]
    exact hq.2.trans (measure_mono fun z hz => hg hz)

/-- The affine map `x ↦ a * x + b` is measurable. -/
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

/-- Scaling by `a` is the affine map `x ↦ a * x + 0`. -/
lemma map_mul_eq_map_affine (a : ℝ) :
    μ.map (fun x => a * x) = μ.map (fun x => a * x + 0) := by
  simp only [add_zero]

/-- `q` is a `p`-quantile of the law of `aX` (`a > 0`) iff `q / a` is a `p`-quantile of `X`. -/
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

/-- Uniqueness criterion ("no gap"): if `μ(-∞,a] > 0` and `a < b` imply `μ(a,b) > 0`,
the `p`-quantile is unique. -/
lemma lowerQuantile_eq_upperQuantile_of_noGap
    (h : ∀ a b, a < b → 0 < μ (Iic a) → 0 < μ (Ioo a b)) :
    lowerQuantile μ p = upperQuantile μ p :=
  lowerQuantile_eq_upperQuantile_of_measure_Ioo_pos hp0 hp1 fun a b hab ha =>
    h a b hab (hp0.trans_le ha.1)

/-- If `p`-quantiles of `μ` are unique, then `q` is a `p`-quantile iff `q` is the common value
`lowerQuantile μ p`. -/
lemma isQuantile_iff_eq_lowerQuantile (hU : lowerQuantile μ p = upperQuantile μ p) {q : ℝ} :
    IsQuantile μ p q ↔ q = lowerQuantile μ p := by
  rw [isQuantile_iff_mem_Icc hp0 hp1, ← hU, Icc_self, mem_singleton_iff]

/-- If `p`-quantiles of `μ` are unique, any two `p`-quantiles agree. -/
lemma IsQuantile.eq_of_unique (hU : lowerQuantile μ p = upperQuantile μ p) {q q' : ℝ}
    (hq : IsQuantile μ p q) (hq' : IsQuantile μ p q') : q = q' :=
  ((isQuantile_iff_eq_lowerQuantile hp0 hp1 hU).1 hq).trans
    ((isQuantile_iff_eq_lowerQuantile hp0 hp1 hU).1 hq').symm

/-- If `1` is the unique `p`-quantile of `μ` and also a `p`-quantile of the pushforward of `μ`
under `x ↦ c * x` (`c > 0`), then `c = 1`. -/
lemma eq_one_of_isQuantile_map_mul (hU : lowerQuantile μ p = upperQuantile μ p)
    (h1 : IsQuantile μ p 1) {c : ℝ} (hc : 0 < c) (hc1 : IsQuantile (μ.map (fun x => c * x)) p 1) :
    c = 1 := by
  have := (isQuantile_map_mul_iff hc).1 hc1
  have he := this.eq_of_unique hp0 hp1 hU h1
  field_simp at he
  linarith

end prob

/-! ### Nonvacuity -/

namespace QuantileMapExample

/-- The point mass at `1` satisfies the hypotheses of `eq_one_of_isQuantile_map_mul` with
`p = 2⁻¹` and `c = 1`: its only `2⁻¹`-quantile is `1`, and its pushforward under `x ↦ 1 * x` is
itself. -/
example : lowerQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ = upperQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ ∧
    IsQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ 1 ∧
    IsQuantile ((Measure.dirac (1 : ℝ)).map (fun x => (1 : ℝ) * x)) 2⁻¹ 1 := by
  have hp0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hp1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have hq : ∀ q : ℝ, IsQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ q → q = 1 := by
    intro q hq'
    rcases lt_trichotomy q 1 with h | h | h
    · have h0 : Measure.dirac (1 : ℝ) (Iic q) = 0 := by
        rw [Measure.dirac_apply' _ measurableSet_Iic]
        exact Set.indicator_of_notMem (by simpa using h) _
      have h2 : 2⁻¹ ≤ Measure.dirac (1 : ℝ) (Iic q) := hq'.1
      rw [h0] at h2
      exact absurd h2 (not_le.2 (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top))
    · exact h
    · have h0 : Measure.dirac (1 : ℝ) (Ici q) = 0 := by
        rw [Measure.dirac_apply' _ measurableSet_Ici]
        exact Set.indicator_of_notMem (by simpa using h) _
      have h2 : 1 - 2⁻¹ ≤ Measure.dirac (1 : ℝ) (Ici q) := hq'.2
      rw [h0] at h2
      exact absurd (tsub_eq_zero_iff_le.1 (le_antisymm h2 zero_le)) (not_le.2 hp1)
  have hU : lowerQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ =
      upperQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ := by
    rw [hq _ (isQuantile_lowerQuantile hp0 hp1), hq _ (isQuantile_upperQuantile hp0 hp1)]
  have h1 : IsQuantile (Measure.dirac (1 : ℝ)) 2⁻¹ 1 := by
    refine ⟨?_, ?_⟩
    · rw [Measure.dirac_apply_of_mem (mem_Iic.2 (le_refl (1 : ℝ)))]
      exact ENNReal.inv_le_one.2 one_le_two
    · rw [Measure.dirac_apply_of_mem (mem_Ici.2 (le_refl (1 : ℝ)))]
      exact tsub_le_self
  have hmap : (Measure.dirac (1 : ℝ)).map (fun x => (1 : ℝ) * x) = Measure.dirac 1 := by
    rw [Measure.map_dirac' (by fun_prop)]
    simp
  exact ⟨hU, h1, by rw [hmap]; exact h1⟩

end QuantileMapExample

end LatticeProb
