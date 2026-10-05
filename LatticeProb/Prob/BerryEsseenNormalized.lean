/- # Normalised Berry-Esseen for non-identically distributed summands

This file is route A4 of the multivariate Berry-Esseen chain (`scratch/pk/mvbe-route.md`).  For a
finite family of centred probability laws `ν i` on `ℝ` with finite third absolute moments and
total variance `∑ σ_i² = 1`, write `ρ = ∑ ∫ |z|³ dν_i`.  The law of the sum of independent
variables with laws `ν i` is `sumLaw ν`, the image of the product measure under the coordinate
sum.  Granting Esseen's smoothing inequality for the standard Gaussian (taken as the explicit
hypothesis `EsseenGaussianInequality`), the Kolmogorov distance of `sumLaw ν` from the standard
Gaussian is at most `100 ρ`.

* `LatticeProb.EsseenGaussianInequality` — Esseen's smoothing inequality for the standard
  Gaussian, as a `Prop`.
* `LatticeProb.sumLaw` — the law of the sum of independent variables with laws `ν i`.
* `LatticeProb.isProbabilityMeasure_sumLaw` — `sumLaw ν` is a probability measure.
* `LatticeProb.charFun_sumLaw` — its characteristic function is `∏ i, charFun (ν i)`.
* `LatticeProb.integrable_abs_sumLaw` — `sumLaw ν` has a finite first absolute moment.
* `LatticeProb.berryEsseen_normalized_of_esseen` — the normalised Berry-Esseen inequality.

The proof takes the smoothing parameter `T = 1/(8ρ)`: on `[-T, T]` the product of characteristic
functions is within `4 ρ |t|³ exp (-t²/3)` of the Gaussian one, the resulting Fourier integral is
at most `20 ρ`, and the second term of Esseen's inequality is at most `66 ρ`.
-/
import Mathlib
import LatticeProb.Prob.BerryEsseenSumCharFun
import LatticeProb.Prob.GaussianBerryEsseenFacts

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- Esseen's smoothing inequality for the standard Gaussian, as a hypothesis-shaped Prop. -/
def EsseenGaussianInequality : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun x : ℝ => |x|) μ →
    ∀ {T : ℝ}, 0 < T → ∀ x : ℝ,
      |(μ (Set.Iic x)).toReal - (gaussianReal 0 1 (Set.Iic x)).toReal|
        ≤ (1 / Real.pi) * (∫ t in (-T)..T,
            ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|)
          + 64 * (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ / (Real.pi * T)

/-- The law of the sum of independent variables with laws `ν i`. -/
noncomputable def sumLaw {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ) : Measure ℝ :=
  Measure.map (fun y : ι → ℝ => ∑ i, y i) (Measure.pi ν)

/-- The coordinate sum `y ↦ ∑ i, y i` on `ι → ℝ` is measurable. -/
private theorem measurable_sum_coord {ι : Type*} [Fintype ι] :
    Measurable (fun y : ι → ℝ => ∑ i, y i) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- The law of a sum of independent variables with probability laws is a probability measure. -/
instance isProbabilityMeasure_sumLaw {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] : IsProbabilityMeasure (sumLaw ν) :=
  Measure.isProbabilityMeasure_map measurable_sum_coord.aemeasurable

/-- The characteristic function of the law of a sum of independent variables is the product of
the characteristic functions of the summands. -/
theorem charFun_sumLaw {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (t : ℝ) :
    charFun (sumLaw ν) t = ∏ i, charFun (ν i) t := by
  have hcont : Continuous fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  rw [charFun_apply_real, sumLaw,
    integral_map measurable_sum_coord.aemeasurable hcont.aestronglyMeasurable]
  have hexp : ∀ y : ι → ℝ, Complex.exp ((t : ℂ) * ((∑ i, y i : ℝ) : ℂ) * Complex.I) =
      ∏ i, Complex.exp ((t : ℂ) * (y i : ℂ) * Complex.I) := by
    intro y
    rw [← Complex.exp_sum]
    congr 1
    rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  simp_rw [hexp]
  rw [integral_fintype_prod_eq_prod
    (fun (_ : ι) (x : ℝ) => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))]
  simp_rw [charFun_apply_real]

/-- The law of a sum of independent variables whose summands have finite third absolute moments
has a finite first absolute moment. -/
theorem integrable_abs_sumLaw {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (h3 : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i)) :
    Integrable (fun x : ℝ => |x|) (sumLaw ν) := by
  have hi : ∀ i, Integrable (fun z : ℝ => |z|) (ν i) := by
    intro i
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (h3 i))
      continuous_abs.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have ha : 0 ≤ |z| := abs_nonneg z
    rw [Real.norm_eq_abs, abs_of_nonneg ha]
    simp only [Pi.add_apply]
    nlinarith [mul_nonneg ha (sq_nonneg (|z| - 1)), sq_nonneg (|z| - 1)]
  have hsum : Integrable (fun y : ι → ℝ => ∑ i, |y i|) (Measure.pi ν) :=
    integrable_finsetSum _ fun i _ => integrable_comp_eval (hi i)
  unfold sumLaw
  rw [integrable_map_measure continuous_abs.aestronglyMeasurable
    measurable_sum_coord.aemeasurable]
  refine hsum.mono' (continuous_abs.comp_aestronglyMeasurable
    measurable_sum_coord.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_abs]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Normalised Berry-Esseen**, given Esseen's smoothing inequality for the standard Gaussian.
For centred independent summands with laws `ν i`, finite third absolute moments and total
variance `1`, the distribution function of the sum differs from the standard Gaussian one by at
most `100 ∑ ∫ |z|³ dν_i`. -/
theorem berryEsseen_normalized_of_esseen (hEss : EsseenGaussianInequality)
    {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hmean : ∀ i, ∫ z, z ∂(ν i) = 0) (h3 : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i))
    (hvar : ∑ i, variance id (ν i) = 1) (x : ℝ) :
    |(sumLaw ν (Set.Iic x)).toReal - (gaussianReal 0 1 (Set.Iic x)).toReal|
      ≤ 100 * ∑ i, ∫ z, |z| ^ 3 ∂(ν i) := by
  set ρ : ℝ := ∑ i, ∫ z, |z| ^ 3 ∂(ν i) with hρ
  have hρi : ∀ i, 0 ≤ ∫ z, |z| ^ 3 ∂(ν i) := fun i => integral_nonneg fun z => by positivity
  have hρpos : 0 < ρ := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < variance id (ν i) := by
      by_contra hcon
      have : ∑ i, variance id (ν i) ≤ 0 :=
        Finset.sum_nonpos fun i _ => not_lt.1 fun h => hcon ⟨i, h⟩
      linarith
    have h1 := variance_rpow_three_halves_le (hmean i) (h3 i)
    have h2 : 0 < variance id (ν i) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hi _
    have h4 : ∫ z, |z| ^ 3 ∂(ν i) ≤ ρ :=
      Finset.single_le_sum (fun j _ => hρi j) (Finset.mem_univ i)
    linarith
  set T : ℝ := 1 / (8 * ρ) with hT
  have hTpos : 0 < T := by positivity
  have hTρ : T * ρ = 1 / 8 := by
    rw [hT]
    field_simp
  have hint := integrable_abs_sumLaw ν h3
  have hE := hEss (sumLaw ν) hint hTpos x
  -- the Fourier integrand
  have hgauss : ∀ t : ℝ, charFun (gaussianReal 0 1) t = Complex.exp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    intro t
    rw [charFun_gaussianReal_zero one_pos]
    simp
  have hpt : ∀ t ∈ Set.Icc (-T) T,
      ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t| ≤
        4 * ρ * (t ^ 2 * Real.exp (-(t ^ 2) / 3)) := by
    intro t ht
    by_cases h0 : t = 0
    · subst h0
      simp
    · have htabs : |t| ≤ T := abs_le.2 ⟨ht.1, ht.2⟩
      have hsmall : |t| * ρ ≤ 1 / 8 := by
        rw [← hTρ]
        exact mul_le_mul_of_nonneg_right htabs hρpos.le
      have hb := norm_prod_charFun_sub_gaussian_le ν hmean h3 hvar hsmall
      rw [← charFun_sumLaw, ← hgauss] at hb
      rw [div_le_iff₀ (abs_pos.2 h0)]
      have e1 : (-(t ^ 2) / 3) = -(t ^ 2 / 3) := by ring
      have e2 : |t| ^ 3 = t ^ 2 * |t| := by
        rw [← sq_abs t]
        ring
      calc ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖
          ≤ 4 * ρ * |t| ^ 3 * Real.exp (-(t ^ 2 / 3)) := hb
        _ = 4 * ρ * (t ^ 2 * Real.exp (-(t ^ 2) / 3)) * |t| := by
          rw [e1, e2]
          ring
  have hcontL : Continuous fun t : ℝ => ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ := by
    have h1 : Continuous (charFun (sumLaw ν)) := continuous_charFun
    have h2 : Continuous (charFun (gaussianReal 0 1)) := continuous_charFun
    exact (h1.sub h2).norm
  have hmeasL : Measurable fun t : ℝ =>
      ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t| :=
    hcontL.measurable.div continuous_abs.measurable
  have hR : IntervalIntegrable (fun t : ℝ => 4 * ρ * (t ^ 2 * Real.exp (-(t ^ 2) / 3)))
      MeasureTheory.volume (-T) T :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hL : IntervalIntegrable (fun t : ℝ =>
      ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t|)
      MeasureTheory.volume (-T) T := by
    refine hR.mono_fun' hmeasL.aestronglyMeasurable ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have htT : t ∈ Set.Icc (-T) T := by
      rw [Set.uIoc_of_le (by linarith)] at ht
      exact ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt t htT
  have hFour : ∫ t in (-T)..T, ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t|
      ≤ 20 * ρ := by
    calc ∫ t in (-T)..T, ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t|
        ≤ ∫ t in (-T)..T, 4 * ρ * (t ^ 2 * Real.exp (-(t ^ 2) / 3)) :=
          intervalIntegral.integral_mono_on (by linarith) hL hR hpt
      _ = 4 * ρ * ∫ t in (-T)..T, t ^ 2 * Real.exp (-(t ^ 2) / 3) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ 4 * ρ * 5 :=
          mul_le_mul_of_nonneg_left (integral_sq_mul_exp_neg_third_le T) (by positivity)
      _ = 20 * ρ := by ring
  -- numerical bounds
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpid : 3.14 < Real.pi := Real.pi_gt_d2
  have hs : (5 / 2 : ℝ) ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simp only [NNReal.coe_one, mul_one]
    nlinarith
  have hspos : 0 < Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by linarith
  set s : ℝ := Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) with hsdef
  have hps : (7.85 : ℝ) ≤ Real.pi * s := by nlinarith
  have hsecond : 64 * s⁻¹ / (Real.pi * T) ≤ 66 * ρ := by
    have hform : 64 * s⁻¹ / (Real.pi * T) = 512 * ρ / (Real.pi * s) := by
      rw [hT]
      field_simp
      norm_num
    rw [hform, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hps hρpos.le]
  have hfirst : (1 / Real.pi) * (∫ t in (-T)..T,
      ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t|) ≤ 7 * ρ := by
    have h1 : 1 / Real.pi ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hpi3.le
    calc (1 / Real.pi) * (∫ t in (-T)..T,
          ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t|)
        ≤ (1 / Real.pi) * (20 * ρ) :=
          mul_le_mul_of_nonneg_left hFour (by positivity)
      _ ≤ (1 / 3) * (20 * ρ) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 7 * ρ := by linarith
  calc |(sumLaw ν (Set.Iic x)).toReal - (gaussianReal 0 1 (Set.Iic x)).toReal|
      ≤ (1 / Real.pi) * (∫ t in (-T)..T,
            ‖charFun (sumLaw ν) t - charFun (gaussianReal 0 1) t‖ / |t|)
          + 64 * s⁻¹ / (Real.pi * T) := hE
    _ ≤ 7 * ρ + 66 * ρ := add_le_add hfirst hsecond
    _ ≤ 100 * ρ := by linarith

end LatticeProb
