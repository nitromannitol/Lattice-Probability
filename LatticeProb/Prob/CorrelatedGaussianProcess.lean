import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- A pointwise linear correlation transform of two coordinates. -/
noncomputable def correlationTransform {J Ω : Type*} (ρ : ℝ) (F : J × Fin 2 → Ω → ℝ) :
    J × Fin 2 → Ω → ℝ := fun p ω =>
  if p.2 = 0 then F (p.1, 0) ω
  else ρ * F (p.1, 0) ω + Real.sqrt (1 - ρ ^ 2) * F (p.1, 1) ω

theorem correlationTransform_isGaussianProcess {J Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : J × Fin 2 → Ω → ℝ} (hF : IsGaussianProcess F P) (ρ : ℝ) :
    IsGaussianProcess (correlationTransform ρ F) P := by
  classical
  apply hF.of_isGaussianProcess
  intro p
  refine ⟨{(p.1, 0), (p.1, 1)}, ?_, ?_⟩
  let a : ({(p.1, 0), (p.1, 1)} : Finset (J × Fin 2)) := ⟨(p.1, 0), by simp⟩
  let b : ({(p.1, 0), (p.1, 1)} : Finset (J × Fin 2)) := ⟨(p.1, 1), by simp⟩
  exact if p.2 = 0 then ContinuousLinearMap.proj a else
    ρ • ContinuousLinearMap.proj a + Real.sqrt (1 - ρ ^ 2) • ContinuousLinearMap.proj b
  intro ω
  by_cases hi : p.2 = 0 <;> simp [correlationTransform, Finset.restrict_def, hi]

theorem correlationTransform_measurable {J Ω : Type*} [MeasurableSpace Ω]
    (ρ : ℝ) (F : J × Fin 2 → Ω → ℝ) (hF : ∀ p, Measurable (F p)) (p : J × Fin 2) :
    Measurable (correlationTransform ρ F p) := by
  unfold correlationTransform
  split
  · exact hF _
  · exact ((measurable_const.mul (hF _)).add (measurable_const.mul (hF _)))

theorem correlationTransform_continuous {Ω : Type*} (ρ : ℝ) (F : ℝ × Fin 2 → Ω → ℝ)
    (hF : ∀ i ω, Continuous (fun t => F (t, i) ω)) (i : Fin 2) (ω : Ω) :
    Continuous (fun t => correlationTransform ρ F (t, i) ω) := by
  by_cases hi : i = 0
  · simpa [correlationTransform, hi] using hF 0 ω
  · simpa [correlationTransform, hi, Pi.add_def, Pi.mul_def] using
      (continuous_const.mul (hF 0 ω)).add (continuous_const.mul (hF 1 ω))

theorem correlationTransform_covariance {J Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : J × Fin 2 → Ω → ℝ} (hF : IsGaussianProcess F P)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (K : J → J → ℝ)
    (hcov : ∀ s t i j, cov[F (s, i), F (t, j); P] = if i = j then K s t else 0)
    (s t : J) (i j : Fin 2) :
    cov[correlationTransform ρ F (s, i), correlationTransform ρ F (t, j); P] =
      K s t * (if i = j then 1 else ρ) := by
  letI : IsProbabilityMeasure P := hF.isProbabilityMeasure
  have hm (u : J) (k : Fin 2) : MemLp (F (u, k)) 2 P :=
    (hF.hasGaussianLaw_eval (u, k)).memLp_two
  have hnonneg : 0 ≤ 1 - ρ ^ 2 := by
    have h := abs_le.mp hρ
    nlinarith [sq_nonneg (ρ + 1), sq_nonneg (ρ - 1)]
  have hsqrt : (Real.sqrt (1 - ρ ^ 2)) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hnonneg
  fin_cases i <;> fin_cases j <;>
    norm_num
  · change cov[F (s, 0), F (t, 0); P] = K s t
    simpa using hcov s t 0 0
  · change cov[F (s, 0), (fun ω => ρ * F (t, 0) ω) +
        (fun ω => Real.sqrt (1 - ρ ^ 2) * F (t, 1) ω); P] = K s t * ρ
    rw [covariance_add_right (hm s 0) ((hm t 0).const_mul ρ)
      ((hm t 1).const_mul _), covariance_const_mul_right, covariance_const_mul_right,
      hcov, hcov]
    simp
    ring
  · change cov[(fun ω => ρ * F (s, 0) ω) +
        (fun ω => Real.sqrt (1 - ρ ^ 2) * F (s, 1) ω), F (t, 0); P] = K s t * ρ
    rw [covariance_add_left ((hm s 0).const_mul ρ) ((hm s 1).const_mul _)
      (hm t 0), covariance_const_mul_left, covariance_const_mul_left, hcov, hcov]
    simp
    ring
  · change cov[(fun ω => ρ * F (s, 0) ω) +
        (fun ω => Real.sqrt (1 - ρ ^ 2) * F (s, 1) ω),
        (fun ω => ρ * F (t, 0) ω) +
        (fun ω => Real.sqrt (1 - ρ ^ 2) * F (t, 1) ω); P] = K s t
    rw [covariance_add_left ((hm s 0).const_mul ρ) ((hm s 1).const_mul _)
      (((hm t 0).const_mul ρ).add ((hm t 1).const_mul _)),
      covariance_add_right ((hm s 0).const_mul ρ) ((hm t 0).const_mul ρ)
        ((hm t 1).const_mul _),
      covariance_add_right ((hm s 1).const_mul _) ((hm t 0).const_mul ρ)
        ((hm t 1).const_mul _)]
    simp [covariance_const_mul_left, covariance_const_mul_right, hcov]
    calc
      ρ * (ρ * K s t) + Real.sqrt (1 - ρ ^ 2) *
          (Real.sqrt (1 - ρ ^ 2) * K s t) =
          (ρ ^ 2 + Real.sqrt (1 - ρ ^ 2) ^ 2) * K s t := by ring
      _ = K s t := by rw [hsqrt]; ring

theorem correlationTransform_mean {J Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : J × Fin 2 → Ω → ℝ} (hF : IsGaussianProcess F P)
    (ρ : ℝ) (hmean : ∀ p, ∫ ω, F p ω ∂P = 0) (t : J) (i : Fin 2) :
    ∫ ω, correlationTransform ρ F (t, i) ω ∂P = 0 := by
  by_cases hi : i = 0
  · simpa [correlationTransform, hi] using hmean (t, 0)
  · simp only [correlationTransform, hi, if_false]
    rw [integral_add]
    · simp [integral_const_mul, hmean]
    · exact ((hF.hasGaussianLaw_eval (t, 0)).integrable).const_mul _
    · exact ((hF.hasGaussianLaw_eval (t, 1)).integrable).const_mul _

theorem correlationTransform_variance_pos {J Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : J × Fin 2 → Ω → ℝ} (hF : IsGaussianProcess F P)
    (ρ : ℝ) (hρ : |ρ| ≤ 1) (K : J → J → ℝ)
    (hcov : ∀ s t i j, cov[F (s, i), F (t, j); P] = if i = j then K s t else 0)
    (t : J) (i : Fin 2) (hK : 0 < K t t) :
    0 < Var[correlationTransform ρ F (t, i); P] := by
  have hc := correlationTransform_covariance hF ρ hρ K hcov t t i i
  have hg := correlationTransform_isGaussianProcess hF ρ
  rw [covariance_self (hg.aemeasurable (t, i))] at hc
  have heq : Var[correlationTransform ρ F (t, i); P] = K t t := by simpa using hc
  rw [heq]
  exact hK

/-- Two independent standard Gaussian coordinates on the product probability space. -/
noncomputable def standardGaussianPair : Unit × Fin 2 → ℝ × ℝ → ℝ :=
  fun p ω => if p.2 = 0 then ω.1 else ω.2

noncomputable def standardGaussianPairMeasure : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

theorem standardGaussianPair_isGaussianProcess :
    IsGaussianProcess standardGaussianPair standardGaussianPairMeasure := by
  classical
  constructor
  intro I
  let L : (ℝ × ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi fun i =>
    if i.1.2 = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else ContinuousLinearMap.snd ℝ ℝ ℝ
  letI : IsGaussian standardGaussianPairMeasure := by
    unfold standardGaussianPairMeasure
    infer_instance
  have h : HasGaussianLaw id standardGaussianPairMeasure := IsGaussian.hasGaussianLaw_id
  have heq : (fun ω => I.restrict (standardGaussianPair · ω)) = (fun ω => L ω) := by
    funext ω i
    simp only [L, ContinuousLinearMap.pi_apply, standardGaussianPair, Finset.restrict_def]
    split_ifs <;> rfl
  rw [heq]
  exact h.map_fun L

theorem standardGaussianPair_transform_isGaussian (ρ : ℝ) :
    IsGaussianProcess (correlationTransform ρ standardGaussianPair)
      standardGaussianPairMeasure :=
  correlationTransform_isGaussianProcess standardGaussianPair_isGaussianProcess ρ

theorem standardGaussianPair_independent :
    IndepFun Prod.fst Prod.snd standardGaussianPairMeasure := by
  simpa [standardGaussianPairMeasure] using
    (indepFun_prod (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (X := id) (Y := id) measurable_id measurable_id)

theorem standardGaussianPair_first_variance :
    Var[Prod.fst; standardGaussianPairMeasure] = 1 := by
  rw [← variance_id_map measurable_fst.aemeasurable]
  simp [standardGaussianPairMeasure, variance_id_gaussianReal]

theorem abs_neg_cos_parameter_le_one (γ : ℝ) :
    |-Real.cos (Real.pi * γ ^ 2 / 4)| ≤ 1 := by
  simpa using Real.abs_cos_le_one (Real.pi * γ ^ 2 / 4)

theorem standardGaussianPair_second_variance :
    Var[Prod.snd; standardGaussianPairMeasure] = 1 := by
  rw [← variance_id_map measurable_snd.aemeasurable]
  simp [standardGaussianPairMeasure, variance_id_gaussianReal]

theorem standardGaussianPair_covariance (s t : Unit) (i j : Fin 2) :
    cov[standardGaussianPair (s, i), standardGaussianPair (t, j);
      standardGaussianPairMeasure] = if i = j then 1 else 0 := by
  have hf : MemLp Prod.fst 2 standardGaussianPairMeasure :=
    (standardGaussianPair_isGaussianProcess.hasGaussianLaw_eval ((), 0)).memLp_two
  have hs : MemLp Prod.snd 2 standardGaussianPairMeasure :=
    (standardGaussianPair_isGaussianProcess.hasGaussianLaw_eval ((), 1)).memLp_two
  have hcross := standardGaussianPair_independent.covariance_eq_zero hf hs
  have hff : cov[Prod.fst, Prod.fst; standardGaussianPairMeasure] = 1 := by
    rw [covariance_self measurable_fst.aemeasurable, standardGaussianPair_first_variance]
  have hss : cov[Prod.snd, Prod.snd; standardGaussianPairMeasure] = 1 := by
    rw [covariance_self measurable_snd.aemeasurable, standardGaussianPair_second_variance]
  fin_cases i <;> fin_cases j <;> norm_num
  · exact hff
  · exact hcross
  · rw [covariance_comm]; exact hcross
  · exact hss

theorem standardGaussianPair_transform_covariance (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (i j : Fin 2) :
    cov[correlationTransform ρ standardGaussianPair ((), i),
      correlationTransform ρ standardGaussianPair ((), j); standardGaussianPairMeasure] =
      if i = j then 1 else ρ := by
  simpa using correlationTransform_covariance standardGaussianPair_isGaussianProcess ρ hρ
    (fun _ _ => 1) standardGaussianPair_covariance () () i j

theorem standardGaussianPair_cos_covariance (γ : ℝ) (i j : Fin 2) :
    cov[correlationTransform (-Real.cos (Real.pi * γ ^ 2 / 4)) standardGaussianPair ((), i),
      correlationTransform (-Real.cos (Real.pi * γ ^ 2 / 4)) standardGaussianPair ((), j);
      standardGaussianPairMeasure] =
      if i = j then 1 else -Real.cos (Real.pi * γ ^ 2 / 4) :=
  standardGaussianPair_transform_covariance _ (abs_neg_cos_parameter_le_one γ) i j

end LatticeProb
