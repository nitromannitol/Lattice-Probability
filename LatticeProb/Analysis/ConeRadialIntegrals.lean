import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.NullMeasurable
import LatticeProb.Analysis.AngularIntegralMeasurable

/-!
# Radial integrals and good samples for circle-average processes

General measure-theoretic and integrability facts for a random field `c : Ω → ℝ → ℂ → ℝ` whose circle averages are
measurable in the sample and continuous in the radius off a null set. The radial process is `t ↦ c (e^{-t}) 0`.

* `exists_measurable_good_set`: a measurable set of full measure on which `c` is continuous on `(0,∞) × ℂ`.
* `measurable_uncurry_radial`: joint measurability of `(t, ω) ↦ 1_T(ω) c_{e^{-t}}(0)(ω)`, by Carathéodory's lemma.
* `lintegral_Ioc_eq_radial`: the change of variables `y = e^{-t}` from `(0,1]` onto `[0,∞)`.
* `integrableOn_Ioc_mul_abs`: integrability of `y ↦ y |g y|` on `(0,R0]` from its integrability on `(0,1]`.
* `integrable_radial_indicator`: the function `x ↦ 1_{|x| ≤ R0} |g(|x|)|` is integrable on `ℂ` (polar coordinates).
* `ae_circleMap_ne_zero`: the circle `θ ↦ circleMap z r θ` avoids `0` for Lebesgue-almost every angle in `(0, 2π]`,
  by the null set of exceptional angles `LatticeProb.AngularIntegralMeasurable.circleZeroAngles`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.ConeRadialIntegrals

/-- **A measurable full-measure set of good samples.** Off a `P`-null set the field `c` is continuous on
`(0,∞) × ℂ`. There is a measurable set `T` with null complement such that `c ω` is continuous on `(0,∞) × ℂ`
for every `ω ∈ T`. -/
lemma exists_measurable_good_set {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    ∃ T : Set Ω, MeasurableSet T ∧ P Tᶜ = 0 ∧
      ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  obtain ⟨t, hBt, hmt, hPt⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  refine ⟨tᶜ, hmt.compl, by rw [compl_compl]; exact hPt, fun ω hω => ?_⟩
  by_contra h
  exact hω (hBt h)

/-- **Joint measurability of the modified radial process.** For a measurable set `T` on whose points `c` is
continuous on `(0,∞) × ℂ`, the map `(t, ω) ↦ 1_T(ω) c ω (e^{-t}) 0` is measurable on `ℝ × Ω`: it is continuous
in `t` for every `ω` and measurable in `ω` for every `t` (Carathéodory's lemma). -/
lemma measurable_uncurry_radial {Ω : Type*} [MeasurableSpace Ω] {c : Ω → ℝ → ℂ → ℝ} {T : Set Ω}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) (hT : MeasurableSet T)
    (hgood : ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) :
    Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => T.indicator (fun ω => c ω (Real.exp (-t)) 0) ω) := by
  refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun t => ?_)
  · by_cases hω : ω ∈ T
    · simp only [Set.indicator_of_mem hω]
      have hc := hgood ω hω
      exact hc.comp_continuous (f := fun t : ℝ => ((Real.exp (-t)), (0 : ℂ)))
        (by fun_prop) (fun t => ⟨Real.exp_pos _, Set.mem_univ _⟩)
    · simp only [Set.indicator_of_notMem hω]
      exact continuous_const
  · exact (hcm (Real.exp (-t)) 0 (Real.exp_pos _)).indicator hT

/-- **Change of variables `y = e^{-t}` on `(0,1]`.** The image of `[0,∞)` under `t ↦ e^{-t}` is `(0,1]`, with
Jacobian `e^{-t}`, so `∫_{(0,1]} y |g y| dy = ∫_{[0,∞)} e^{-2t} |g(e^{-t})| dt`. -/
lemma lintegral_Ioc_eq_radial (g : ℝ → ℝ) :
    ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |g y|) =
      ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * t)) * ENNReal.ofReal |g (Real.exp (-t))| := by
  have himg : (fun t : ℝ => Real.exp (-t)) '' Set.Ici 0 = Set.Ioc 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (by simp only [Set.mem_Ici] at ht; linarith)⟩
    · rintro ⟨hy0, hy1⟩
      refine ⟨-Real.log y, ?_, ?_⟩
      · simp only [Set.mem_Ici, neg_nonneg]
        exact Real.log_nonpos hy0.le hy1
      · simp only [neg_neg]
        exact Real.exp_log hy0
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) (Set.Ici 0) x := by
    intro x _
    have := ((hasDerivAt_id x).neg.exp).hasDerivWithinAt (s := Set.Ici 0)
    simpa using this
  have hinj : Set.InjOn (fun t : ℝ => Real.exp (-t)) (Set.Ici 0) := by
    intro a _ b _ hab
    have := Real.exp_injective hab
    linarith
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ici hderiv hinj
    (fun y => ENNReal.ofReal (y * |g y|))
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ici fun t _ => ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    abs_neg, abs_of_pos (Real.exp_pos _)]
  congr 1
  rw [show -2 * t = -t + -t by ring, Real.exp_add]
  ring

/-- **Integrability of the radial majorant on `(0,R0]`.** A function `g` continuous on `(0,∞)` with
`∫_{(0,1]} y |g y| dy < ∞` has `y ↦ y |g y|` integrable on `(0,R0]` for every `R0 ≥ 1`. -/
lemma integrableOn_Ioc_mul_abs {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0)) {R0 : ℝ} (hR0 : 1 ≤ R0)
    (hfin : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |g y|) < ⊤) :
    IntegrableOn (fun y => y * |g y|) (Set.Ioc 0 R0) := by
  have hc : ContinuousOn (fun y => y * |g y|) (Set.Ioi 0) := continuousOn_id.mul hg.abs
  rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hR0]
  refine IntegrableOn.union ?_ ?_
  · refine ⟨(hc.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc, ?_⟩
    have h1 : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ‖y * |g y|‖ₑ = ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (y * |g y|) :=
      setLIntegral_congr_fun measurableSet_Ioc fun y hy => by
        rw [Real.enorm_eq_ofReal (mul_nonneg hy.1.le (abs_nonneg _))]
    exact h1.trans_lt hfin
  · have hcI : ContinuousOn (fun y => y * |g y|) (Set.Icc 1 R0) :=
      hc.mono fun y hy => Set.mem_Ioi.2 (lt_of_lt_of_le one_pos hy.1)
    exact (hcI.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- **Integrability of a radial indicator on `ℂ`.** If `y ↦ y |g y|` is integrable on `(0,R0]`, then
`x ↦ 1_{|x| ≤ R0} |g(|x|)|` is integrable on `ℂ`: polar coordinates (`MeasureTheory.integrable_fun_norm_addHaar`)
in the two-dimensional real space `ℂ`. -/
lemma integrable_radial_indicator {g : ℝ → ℝ} {R0 : ℝ}
    (hg : IntegrableOn (fun y => y * |g y|) (Set.Ioc 0 R0)) :
    Integrable (fun x : ℂ => (Set.Iic R0).indicator (fun y => |g y|) ‖x‖) := by
  have hdim : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  refine (integrable_fun_norm_addHaar (μ := volume) (f := (Set.Iic R0).indicator (fun y => |g y|))).2 ?_
  have h1 : IntegrableOn (fun y => (Set.Ioc 0 R0).indicator (fun y => y * |g y|) y) (Set.Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).2 hg).integrableOn
  refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := hy
  by_cases h : y ≤ R0
  · simp [Set.indicator, h, hy0]
  · simp [Set.indicator, h]

/-- **The circle meets the origin in a null set of angles.** For `r > 0` the set of angles `θ` with
`circleMap z r θ = 0` is Lebesgue-null (`LatticeProb.AngularIntegralMeasurable.volume_circleZeroAngles`), so the
circle avoids `0` for Lebesgue-almost every angle in `(0, 2π]`. -/
lemma ae_circleMap_ne_zero {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂(volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))), circleMap z r θ ≠ 0 := by
  refine ae_restrict_of_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (LatticeProb.AngularIntegralMeasurable.volume_circleZeroAngles hr)] with θ hθ h0
  apply hθ
  show ‖z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = 0
  rw [circleMap, mul_comm (θ : ℂ) Complex.I] at h0
  rw [h0, norm_zero]

end LatticeProb.ConeRadialIntegrals
