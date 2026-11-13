/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.TranslatedMoment at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaFunctional
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPArea
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.BallMoment
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# Small-ball moments of translated whole-plane GMC

The normalized whole-plane GFF recentered at `z` has its original law.
The measurable area functional transfers the centered ball moment under this
law; the whole-plane area coordinate change isolates the random additive
circle average at radius one.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC}

private def recentered (X : Ω → DistC) (z : ℂ) (ω : Ω) : DistC :=
  addConst (affineComp 1 z (X ω)) (-circleAvg (X ω) 1 z)

private theorem measurable_recentered (hX : IsNormalizedWPGFF X P) (z : ℂ) :
    Measurable (recentered X z) := by
  exact ((hX.1.affineComp one_pos z).addConst
    (((measurable_circleAvg_left 1 z).comp hX.1.measurable).neg)).measurable

private theorem law_recentered (hX : IsNormalizedWPGFF X P) (z : ℂ) :
    P.map (recentered X z) = P.map X := by
  exact CircleAvg.map_affine_sub_circleAvg hX one_pos z

private theorem normalized_recentered (hX : IsNormalizedWPGFF X P) (z : ℂ) :
    IsNormalizedWPGFF (recentered X z) P := by
  have hm := measurable_recentered hX z
  have hG := LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq hm hX.1
    (law_recentered hX z)
  refine ⟨hG, ?_⟩
  have hS : MeasurableSet {h : DistC | circleAvg h 1 0 = 0} :=
    measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const
  have hmap : ∀ᵐ h ∂(P.map X), circleAvg h 1 0 = 0 :=
    (ae_map_iff hX.1.measurable.aemeasurable hS).2 hX.2
  rw [← law_recentered hX z] at hmap
  exact (ae_map_iff hm.aemeasurable hS).1 hmap

/-- The mass of a ball for the recentered field has the centered GMC law. -/
theorem lintegral_recentered_ball_eq_origin
    (hX : IsNormalizedWPGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (z : ℂ) {ρ q : ℝ} (hρ : 0 < ρ) :
    ∫⁻ ω, MatedCRTHarmonic.CellScaling.lqgArea γ (recentered X z ω) (ball 0 ρ) ^ q ∂P =
      ∫⁻ ω, MatedCRTHarmonic.CellScaling.lqgArea γ (X ω) (ball 0 ρ) ^ q ∂P := by
  letI : IsProbabilityMeasure P := hX.1.gaussian.isProbabilityMeasure
  set U : Set ℂ := ball 0 ρ
  set F : DistC → ℝ≥0∞ := fun h => MatedCRTHarmonic.ConeScaling.areaOpenFun γ U h ^ q
  have hFm : Measurable F :=
    (MatedCRTHarmonic.ConeScaling.measurable_areaOpenFun γ U).pow_const q
  have hXv := MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp hX.1 hγ hγ2
  have hYv := MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp
    (normalized_recentered hX z).1 hγ hγ2
  have hXe : (fun ω => F (X ω)) =ᵐ[P]
      fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ (X ω) U ^ q := by
    filter_upwards [hXv] with ω hv
    exact congrArg (· ^ q)
      (MatedCRTHarmonic.ConeScaling.areaOpenFun_eq_lqgArea
        isOpen_ball isBounded_ball hv)
  have hYe : (fun ω => F (recentered X z ω)) =ᵐ[P]
      fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ (recentered X z ω) U ^ q := by
    filter_upwards [hYv] with ω hv
    exact congrArg (· ^ q)
      (MatedCRTHarmonic.ConeScaling.areaOpenFun_eq_lqgArea
        isOpen_ball isBounded_ball hv)
  rw [← lintegral_congr_ae hYe, ← lintegral_congr_ae hXe]
  calc
    ∫⁻ ω, F (recentered X z ω) ∂P = ∫⁻ h, F h ∂(P.map (recentered X z)) :=
      (lintegral_map hFm (measurable_recentered hX z)).symm
    _ = ∫⁻ h, F h ∂(P.map X) := by rw [law_recentered hX z]
    _ = ∫⁻ ω, F (X ω) ∂P := lintegral_map hFm hX.1.measurable

private lemma image_translate_ball (z : ℂ) (ρ : ℝ) :
    (fun w : ℂ => ((1 : ℝ) : ℂ) * w + z) '' ball 0 ρ = ball z ρ := by
  ext w
  simp only [mem_image, mem_ball, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [Complex.ofReal_one, one_mul, add_sub_cancel_right] using hv
  · intro hw
    refine ⟨w - z, ?_, by simp⟩
    simpa only [sub_zero] using hw

/-- The area translation rule, with the radius-one circle average made explicit. -/
theorem ae_area_recentered_ball
    (hX : IsNormalizedWPGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (z : ℂ) (ρ : ℝ) :
    ∀ᵐ ω ∂P,
      MatedCRTHarmonic.CellScaling.lqgArea γ (recentered X z ω) (ball 0 ρ) =
        ENNReal.ofReal (Real.exp (-γ * circleAvg (X ω) 1 z)) *
          MatedCRTHarmonic.CellScaling.lqgArea γ (X ω) (ball z ρ) := by
  filter_upwards [MatedCRTHarmonic.LQGCoord.ae_lqgArea_affine_wp hX.1 hγ hγ2]
    with ω hω
  specialize hω 1 one_pos (-circleAvg (X ω) 1 z) z (ball 0 ρ)
  simp only [Real.log_one, mul_zero, zero_add] at hω
  rw [image_translate_ball] at hω
  convert hω using 1
  congr 2
  ring

/-- Radius-one circle averages have Gaussian exponential moments bounded
uniformly over the unit disc. -/
theorem lintegral_exp_circleAvg_one_le
    (hX : IsNormalizedWPGFF X P) {z : ℂ} (hz : ‖z‖ ≤ 1) (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * circleAvg (X ω) 1 z)) ∂P ≤
      ENNReal.ofReal (Real.exp (s ^ 2 * Real.log 5)) := by
  obtain ⟨H, hG, -, hae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hX
  have he : (fun ω => ENNReal.ofReal (Real.exp (s * circleAvg (X ω) 1 z))) =ᵐ[P]
      fun ω => ENNReal.ofReal (Real.exp (s * H 1 z ω)) := by
    filter_upwards [hae 1 one_pos z] with ω hω
    rw [hω]
  rw [lintegral_congr_ae he, LQGMetric.DG.lintegral_exp_circleAvg hG one_pos z s]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hv := MatedCRTHarmonic.GMCFacts.gffCircleCov_self_le one_pos le_rfl
    (w := z) (hz.trans (by norm_num : (1 : ℝ) ≤ 4))
  simp only [Real.log_one, neg_zero, zero_add] at hv
  nlinarith [sq_nonneg s, mul_nonneg (sub_nonneg.2 hv) (sq_nonneg s)]

/-- Undo the radius-one normalization in the area translation identity. -/
theorem ae_area_translated_ball
    (hX : IsNormalizedWPGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (z : ℂ) (ρ : ℝ) :
    ∀ᵐ ω ∂P,
      MatedCRTHarmonic.CellScaling.lqgArea γ (X ω) (ball z ρ) =
        ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) 1 z)) *
          MatedCRTHarmonic.CellScaling.lqgArea γ (recentered X z ω) (ball 0 ρ) := by
  filter_upwards [ae_area_recentered_ball hX hγ hγ2 z ρ] with ω hω
  rw [hω, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  have he : γ * circleAvg (X ω) 1 z + -γ * circleAvg (X ω) 1 z = 0 := by ring
  rw [he, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- The centered [16] moment constant works for every recentered field,
because the recentered fields have the same law. -/
theorem exists_uniform_recentered_ball_moment
    (hX : IsNormalizedWPGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {p : ℝ} (hp0 : 0 < p) (hp : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 64 →
      ∫⁻ ω, MatedCRTHarmonic.CellScaling.lqgArea γ (recentered X z ω) (ball 0 ρ) ^ p ∂P ≤
        C * ENNReal.ofReal (ρ ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) := by
  obtain ⟨H, hH, hHm, -, hμ⟩ := MatedCRTHarmonic.GMCFacts.exists_isLQGAreaOf hX hγ hγ2
  obtain ⟨C, hCtop, hC⟩ := MatedCRTHarmonic.GMCFacts.exists_lintegral_ball_origin_rpow_le
    hH hHm hγ hμ hp0 hp
  refine ⟨C, hCtop, fun z ρ hρ hρ64 => ?_⟩
  rw [lintegral_recentered_ball_eq_origin hX hγ hγ2 z hρ]
  simp only [MatedCRTHarmonic.LQGCone.lqgArea_eq_qAreaC]
  exact hC ρ hρ hρ64

/-- The whole-plane GMC small-ball moment, uniform over centres in the closed
unit disc. The slight loss from `p > q` comes from Hölder on the random
radius-one additive constant. -/
theorem exists_uniform_translated_ball_moment
    (hX : IsNormalizedWPGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {q p : ℝ} (hq : 0 < q) (hqp : q < p) (hp : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ), ‖z‖ ≤ 1 → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 64 →
      ∫⁻ ω, MatedCRTHarmonic.CellScaling.lqgArea γ (X ω) (ball z ρ) ^ q ∂P ≤
        C * ENNReal.ofReal
          (ρ ^ (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2)) := by
  letI : IsProbabilityMeasure P := hX.1.gaussian.isProbabilityMeasure
  have hp0 : 0 < p := lt_trans hq hqp
  have hpq : 0 < p - q := sub_pos.mpr hqp
  set a : ℝ := p / (p - q)
  set b : ℝ := p / q
  have ha : 0 < a := div_pos hp0 hpq
  have hb : 0 < b := div_pos hp0 hq
  have hab : a.HolderConjugate b := by
    refine ⟨?_, ha, hb⟩
    dsimp [a, b]
    field_simp
    ring
  obtain ⟨C₀, hC₀, hcenter⟩ :=
    exists_uniform_recentered_ball_moment hX hγ hγ2 hp0 hp
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (a * q ^ 2 * γ ^ 2 * Real.log 5))
  refine ⟨K * C₀ ^ (q / p), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hC₀.ne), ?_⟩
  intro z hz ρ hρ hρ64
  set M : Ω → ℝ≥0∞ := fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ (recentered X z ω) (ball 0 ρ)
  set F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) 1 z))
  have hMm : AEMeasurable M P := by
    have hYv := MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp
      (normalized_recentered hX z).1 hγ hγ2
    have he : (fun ω => MatedCRTHarmonic.ConeScaling.areaOpenFun γ (ball 0 ρ)
        (recentered X z ω)) =ᵐ[P] M := by
      filter_upwards [hYv] with ω hv
      exact MatedCRTHarmonic.ConeScaling.areaOpenFun_eq_lqgArea
        isOpen_ball isBounded_ball hv
    exact ((MatedCRTHarmonic.ConeScaling.measurable_areaOpenFun γ (ball 0 ρ)).comp
      (measurable_recentered hX z)).aemeasurable.congr he
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp
    ((((measurable_circleAvg_left 1 z).comp hX.1.measurable).const_mul γ).exp)
  have harea : (fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ (X ω) (ball z ρ) ^ q) =ᵐ[P]
      fun ω => F ω ^ q * M ω ^ q := by
    filter_upwards [ae_area_translated_ball hX hγ hγ2 z ρ] with ω hω
    rw [hω, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_congr_ae harea]
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq P hab
    (hFm.pow_const q).aemeasurable (hMm.pow_const q)
  have hGauss : ∫⁻ ω, (F ω ^ q) ^ a ∂P ≤
      ENNReal.ofReal (Real.exp ((a * q * γ) ^ 2 * Real.log 5)) := by
    have he : ∀ ω, (F ω ^ q) ^ a =
        ENNReal.ofReal (Real.exp ((a * q * γ) * circleAvg (X ω) 1 z)) := by
      intro ω
      rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
        ← Real.exp_mul]
      congr 2
      ring
    simp_rw [he]
    exact lintegral_exp_circleAvg_one_le hX hz (a * q * γ)
  have hMass : ∫⁻ ω, (M ω ^ q) ^ b ∂P ≤
      C₀ * ENNReal.ofReal
        (ρ ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) := by
    have he : ∀ ω, (M ω ^ q) ^ b = M ω ^ p := by
      intro ω
      rw [← ENNReal.rpow_mul]
      congr 1
      dsimp [b]
      field_simp
    simp_rw [he]
    exact hcenter z ρ hρ hρ64
  calc
    ∫⁻ ω, F ω ^ q * M ω ^ q ∂P ≤
        (∫⁻ ω, (F ω ^ q) ^ a ∂P) ^ (1 / a) *
          (∫⁻ ω, (M ω ^ q) ^ b ∂P) ^ (1 / b) := hhold
    _ ≤ ENNReal.ofReal (Real.exp ((a * q * γ) ^ 2 * Real.log 5)) ^ (1 / a) *
          (C₀ * ENNReal.ofReal
            (ρ ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2))) ^ (1 / b) := by
          gcongr
    _ = (K * C₀ ^ (q / p)) * ENNReal.ofReal
          (ρ ^ (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2)) := by
          have hba : 1 / b = q / p := by
            dsimp [b]
            field_simp
          have hgaussId : ENNReal.ofReal
              (Real.exp ((a * q * γ) ^ 2 * Real.log 5)) ^ (1 / a) = K := by
            dsimp [K]
            rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
            congr 2
            field_simp [ha.ne']
          have hrhoId : ENNReal.ofReal
              (ρ ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) ^ (q / p) =
              ENNReal.ofReal
                (ρ ^ (q * (2 + γ ^ 2 / 2) - p * q * γ ^ 2 / 2)) := by
            rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hρ _),
              ← Real.rpow_mul hρ.le]
            congr 1
            field_simp [hp0.ne']
          rw [hba, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hgaussId, hrhoId]
          ring

end MatedCRTHarmonic.GMCUpper
