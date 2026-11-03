/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.RNMoment at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Moments of Radon–Nikodym derivatives under push-forward (task P2-MQ)

Measure-theoretic tools for MQ Lemma 4.1 (Miller–Qian, arXiv:1812.03913,
`lqg_geodesics.tex` l. 549–589): MQ bound the moments of the Radon–Nikodym derivative of the
*restricted* field by those of the Cameron–Martin density of the whole field "by Jensen's
inequality" (l. 585–589). Here:

* `lintegral_rnDeriv_map_rpow_le` : for `p ≥ 1`,
  `∫ (d(μ∘g⁻¹)/d(ν∘g⁻¹))^p d(ν∘g⁻¹) ≤ ∫ (dμ/dν)^p dν` — the conditional Jensen inequality
  (data processing for the convex `x ↦ x^p`), from mathlib's `ConvexOn.comp_rnDeriv_map_le`
  (Degenne–Luccioli, `InformationTheory/KullbackLeibler/DataProcessing.lean`);
* `lintegral_rnDeriv_rpow_swap` : for mutually absolutely continuous `μ, ν`,
  `∫ (dμ/dν)^p dν = ∫ (dν/dμ)^{1-p} dμ` (change of measure);
* `lintegral_rnDeriv_rpow_le_two` : for `0 ≤ p ≤ 1` and probability measures,
  `∫ (dμ/dν)^p dν ≤ 2` (`a^p ≤ 1 + a`; own elementary step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.MQ

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma rpow_eq_ofReal_toReal_rpow {a : ℝ≥0∞} (ha : a ≠ ⊤) {p : ℝ} (hp : 0 ≤ p) :
    a ^ p = ENNReal.ofReal (a.toReal ^ p) := by
  rw [ENNReal.toReal_rpow, ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hp ha)]

/-- **Conditional Jensen for RN derivatives**: for `p ≥ 1`, push-forward does not increase the
`p`-th moment of the Radon–Nikodym derivative. -/
theorem lintegral_rnDeriv_map_rpow_le {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : α → β} (hg : Measurable g) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ y, ((μ.map g).rnDeriv (ν.map g) y) ^ p ∂(ν.map g) ≤ ∫⁻ x, (μ.rnDeriv ν x) ^ p ∂ν := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  set f : ℝ → ℝ := fun x => x ^ p with hfdef
  have hfc : Continuous f := Real.continuous_rpow_const hp0
  have hfs : StronglyMeasurable f := hfc.stronglyMeasurable
  have hcvx : ConvexOn ℝ (Ici 0) f := convexOn_rpow hp
  have hca : ContinuousWithinAt f (Ici 0) 0 := hfc.continuousWithinAt
  -- rewrite both sides through `toReal`
  have hR : ∫⁻ x, (μ.rnDeriv ν x) ^ p ∂ν = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
    exact rpow_eq_ofReal_toReal_rpow hx.ne hp0
  have hL : ∫⁻ y, ((μ.map g).rnDeriv (ν.map g) y) ^ p ∂(ν.map g) =
      ∫⁻ y, ENNReal.ofReal (f ((μ.map g).rnDeriv (ν.map g) y).toReal) ∂(ν.map g) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top (μ.map g) (ν.map g)] with x hx
    exact rpow_eq_ofReal_toReal_rpow hx.ne hp0
  rw [hL, hR]
  by_cases hint : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν
  swap
  · have : ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν = ⊤ := by
      by_contra hne
      refine hint ?_
      have h1 := integrable_toReal_of_lintegral_ne_top (μ := ν)
        (by fun_prop : AEMeasurable (fun x => ENNReal.ofReal (f (μ.rnDeriv ν x).toReal)) ν) hne
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      exact ENNReal.toReal_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    rw [this]; exact le_top
  have hint' := hcvx.integrable_comp_rnDeriv_map hμν hg hfs hca hint
  have hnn : ∀ y : ℝ≥0∞, 0 ≤ f y.toReal := fun y => Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun y => hnn _),
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => hnn _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_map (f := fun y => f ((μ.map g).rnDeriv (ν.map g) y).toReal) hg.aemeasurable
    (hfc.measurable.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable]
  calc ∫ x, f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν
      ≤ ∫ x, (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | (inferInstance : MeasurableSpace β).comap g])
          x ∂ν :=
        integral_mono_ae (hint'.comp_measurable hg) integrable_condExp
          (hcvx.comp_rnDeriv_map_le hμν hg hfs hca hint)
    _ = ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := integral_condExp hg.comap_le

/-- **Change of measure**: `∫ (dμ/dν)^p dν = ∫ (dν/dμ)^{1-p} dμ` for mutually absolutely
continuous σ-finite `μ, ν`. -/
theorem lintegral_rnDeriv_rpow_swap {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (h1 : μ ≪ ν) (h2 : ν ≪ μ) (p : ℝ) :
    ∫⁻ x, (μ.rnDeriv ν x) ^ p ∂ν = ∫⁻ x, (ν.rnDeriv μ x) ^ (1 - p) ∂μ := by
  rw [← lintegral_rnDeriv_mul h2 (by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h1, Measure.rnDeriv_pos h1,
    h1.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hinv hpos htop
  rw [← hinv]
  simp only [Pi.inv_apply]
  set a := μ.rnDeriv ν x
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg_one a, ← ENNReal.rpow_add _ _ hpos.ne' htop.ne,
    ← ENNReal.rpow_neg, neg_sub]
  congr 1; ring

/-- For `0 ≤ p ≤ 1`: `∫ (dμ/dν)^p dν ≤ ν(univ) + μ(univ)` (from `a^p ≤ 1 + a`). -/
theorem lintegral_rnDeriv_rpow_le_add {μ ν : Measure α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫⁻ x, (μ.rnDeriv ν x) ^ p ∂ν ≤ ν univ + μ univ := by
  calc ∫⁻ x, (μ.rnDeriv ν x) ^ p ∂ν ≤ ∫⁻ x, (1 + μ.rnDeriv ν x) ∂ν := by
        refine lintegral_mono fun x => ?_
        set a := μ.rnDeriv ν x
        rcases le_total a 1 with ha | ha
        · exact (ENNReal.rpow_le_one ha hp0).trans le_self_add
        · calc a ^ p ≤ a ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le ha hp1
            _ = a := ENNReal.rpow_one a
            _ ≤ 1 + a := le_add_self
    _ = ν univ + ∫⁻ x, μ.rnDeriv ν x ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
    _ ≤ ν univ + μ univ := by gcongr; exact Measure.lintegral_rnDeriv_le

/-- **Moment bounds for the restricted RN derivatives** (MQ l. 585–589, "by Jensen"): if
`Q ≪ P ≪ Q` are probability measures whose RN derivative has `∫ (dQ/dP)^q dP ≤ C` for
`q ∈ {p, 1 − p}`, then both RN derivatives of the push-forwards under any measurable `R` have
`p`-th moments `≤ max 2 C`. -/
theorem rnDeriv_map_moments_le {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h1 : Q ≪ P) (h2 : P ≪ Q) {R : α → β} (hR : Measurable R) {C : ℝ≥0∞} (p : ℝ)
    (hC : ∀ q : ℝ, (q = p ∨ q = 1 - p) → ∫⁻ x, (Q.rnDeriv P x) ^ q ∂P ≤ C) :
    ∫⁻ y, ((Q.map R).rnDeriv (P.map R) y) ^ p ∂(P.map R) ≤ max 2 C ∧
      ∫⁻ y, ((P.map R).rnDeriv (Q.map R) y) ^ p ∂(Q.map R) ≤ max 2 C := by
  have : IsProbabilityMeasure (P.map R) :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (Q.map R) :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 inferInstance
  have m1 : Q.map R ≪ P.map R := h1.map hR
  have m2 : P.map R ≪ Q.map R := h2.map hR
  have hsw : ∀ q : ℝ, ∫⁻ x, (P.rnDeriv Q x) ^ q ∂Q = ∫⁻ x, (Q.rnDeriv P x) ^ (1 - q) ∂P :=
    fun q => lintegral_rnDeriv_rpow_swap h2 h1 q
  have h2le : ∀ {μ ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : ℝ},
      0 ≤ q → q ≤ 1 → ∫⁻ y, (μ.rnDeriv ν y) ^ q ∂ν ≤ max 2 C := by
    intro μ ν _ _ q hq0 hq1
    refine (lintegral_rnDeriv_rpow_le_add hq0 hq1).trans ?_
    rw [measure_univ, measure_univ]
    exact (le_of_eq (by norm_num)).trans (le_max_left _ _)
  constructor
  · rcases le_or_gt 1 p with hp | hp
    · exact (lintegral_rnDeriv_map_rpow_le h1 hR hp).trans
        ((hC p (Or.inl rfl)).trans (le_max_right _ _))
    rcases le_or_gt 0 p with hp0 | hp0
    · exact h2le hp0 hp.le
    rw [lintegral_rnDeriv_rpow_swap m1 m2]
    refine (lintegral_rnDeriv_map_rpow_le h2 hR (by linarith)).trans ?_
    rw [hsw, sub_sub_cancel]
    exact (hC p (Or.inl rfl)).trans (le_max_right _ _)
  · rcases le_or_gt 1 p with hp | hp
    · refine (lintegral_rnDeriv_map_rpow_le h2 hR hp).trans ?_
      rw [hsw]
      exact (hC _ (Or.inr rfl)).trans (le_max_right _ _)
    rcases le_or_gt 0 p with hp0 | hp0
    · exact h2le hp0 hp.le
    rw [lintegral_rnDeriv_rpow_swap m2 m1]
    exact (lintegral_rnDeriv_map_rpow_le h1 hR (by linarith)).trans
      ((hC _ (Or.inr rfl)).trans (le_max_right _ _))

end LQGMetric.MQ
