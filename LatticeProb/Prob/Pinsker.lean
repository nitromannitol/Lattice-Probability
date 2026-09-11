/-
Pinsker's inequality from Gibbs' inequality for an exponential tilt and Hoeffding's lemma.
-/
import Mathlib
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
/-- A relative entropy bound controls an expectation minus the log partition function. -/
theorem LatticeProb.integral_sub_log_integral_exp_le_of_klDiv_le
    {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun x => Real.exp (f x)) ν)
    {δ : ℝ} (hδ : 0 ≤ δ) (hkl : klDiv μ ν ≤ ENNReal.ofReal δ) :
    (∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ δ := by
  have hne : klDiv μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hne
  haveI := isProbabilityMeasure_tilted he
  have hnonneg := integral_llr_add_sub_measure_univ_nonneg
    (hac.trans (absolutelyContinuous_tilted he)) (integrable_llr_tilted_right hac hf hint he)
  simp only [probReal_univ, add_sub_cancel_right] at hnonneg
  rw [integral_llr_tilted_right hac hf he hint] at hnonneg
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
  rw [toReal_klDiv hac hint, ENNReal.toReal_ofReal hδ] at hle
  simp only [probReal_univ, add_sub_cancel_right] at hle
  linarith


/-- A centred event indicator is sub-Gaussian with variance proxy one quarter. -/
theorem LatticeProb.indicator_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {A : Set Ω} (hA : MeasurableSet A) :
    HasSubgaussianMGF (fun x => A.indicator (fun _ => (1 : ℝ)) x - ν.real A) (1 / 4) ν := by
  have hb : ∀ᵐ x ∂ν, A.indicator (fun _ => (1 : ℝ)) x ∈ Set.Icc 0 1 := by
    filter_upwards with x
    by_cases hx : x ∈ A <;> simp [hx]
  have h := hasSubgaussianMGF_of_mem_Icc
    ((measurable_const.indicator hA).aemeasurable) hb
  norm_num [integral_indicator_const _ hA] at h
  exact h


/-- Pinsker's inequality for a measurable event and an upper bound on relative entropy. -/
theorem LatticeProb.pinsker (T : Type*) [MeasurableSpace T]
    (μ ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set T) (hA : MeasurableSet A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hkl : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal δ) :
    |μ.real A - ν.real A| ≤ Real.sqrt (δ / 2) := by
  let m := μ.real A - ν.real A
  have hsg := LatticeProb.indicator_hasSubgaussianMGF (ν := ν) hA
  have hZ : Integrable (fun x => A.indicator (fun _ => (1 : ℝ)) x - ν.real A) μ :=
    ((integrable_const (1 : ℝ)).indicator hA).sub (integrable_const _)
  have he := hsg.integrable_exp_mul (4 * m)
  have hvar := LatticeProb.integral_sub_log_integral_exp_le_of_klDiv_le
    (hZ.const_mul (4 * m)) he hδ hkl
  have hmean : (∫ x, (4 * m) * (A.indicator (fun _ => (1 : ℝ)) x - ν.real A) ∂μ) =
      (4 * m) * m := by
    rw [integral_const_mul, integral_sub ((integrable_const (1 : ℝ)).indicator hA)
      (integrable_const _)]
    rw [integral_indicator_const (1 : ℝ) hA]
    simp [m]
  rw [hmean] at hvar
  have hcgf := hsg.cgf_le (4 * m)
  norm_num [ProbabilityTheory.cgf, ProbabilityTheory.mgf] at hcgf
  have hsq : 2 * m ^ 2 ≤ δ := by nlinarith
  change |m| ≤ Real.sqrt (δ / 2)
  nlinarith [sq_abs m, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / 2),
    Real.sqrt_nonneg (δ / 2)]
