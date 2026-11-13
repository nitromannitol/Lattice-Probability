/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3FieldMom at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3FieldCM

/-!
# Exponential moments of the energy of the coupled shift

[18], end of the proof of Lemma A.5: "`E[M_δ^{a/δ}] ≲ 1` … follows from
Lemma A.4". Here: for `κ` with `200 (25π κ energyConst) C_L δ² ≤ (∫ψ)²` (`C_L = logCovConst`),
`E_{P⊗P} exp(κ MfG δ) ≤ 2`, by Jensen over `B̄_{5δ}(0)`, `(a − b)² ≤ 2a² + 2b²`, the product structure of `P ⊗ P`,
and the pointwise bound `lintegral_exp_sq_pairing_le` (the convex domination step of Lemma A.4).

* `GMSAppA.logCovConst` — the constant of `exists_logCov_radDiff_le_sq`.
* `GMSAppA.DiskMarkov.lintegral_exp_MfG_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-- the constant `C_L` with `logCov(ψ_y − ψ_0) ≤ C_L |y|²` for `|y| ≤ 1/2` -/
def logCovConst : ℝ := Classical.choose exists_logCov_radDiff_le_sq

lemma logCovConst_nonneg : 0 ≤ logCovConst := (Classical.choose_spec exists_logCov_radDiff_le_sq).1

lemma logCov_radDiff_le_logCovConst {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    logCov (radDiff quarter_pos.le y 0).1 (radDiff quarter_pos.le y 0).1 ≤ logCovConst * ‖y‖ ^ 2 :=
  (Classical.choose_spec exists_logCov_radDiff_le_sq).2 y hy

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

namespace DiskMarkov
lemma indepFun_G_hz (M : DiskMarkov P h) : IndepFun M.G M.hz P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left M.indep.symm M.G_meas.comap_le

lemma continuous_pvG (M : DiskMarkov P h) (ω : Ω) : Continuous fun y => M.pvG (ω, y) := by
  have e : (fun y => M.pvG (ω, y)) = fun y => (M.G ω (radBump (1 / 4) quarter_pos.le y) -
      M.G ω (radBump (1 / 4) quarter_pos.le 0)) / massQ := by
    funext y
    simp only [pvG]
    congr 1
    show M.G ω (radBump (1 / 4) quarter_pos.le y - radBump (1 / 4) quarter_pos.le 0) = _
    rw [map_sub]
  rw [e]
  exact (((map_continuous (M.G ω)).comp (continuous_radBump (1 / 4) quarter_pos.le)).sub
    continuous_const).div_const _

/-- **Exponential moment of the energy bound**: `E_{P⊗P} exp(κ MfG δ) ≤ 2`. -/
theorem lintegral_exp_MfG_le [IsProbabilityMeasure P] (M : DiskMarkov P h) (hh : IsWholePlaneGFF h P)
    {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ < 1 / 10) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : 200 * (25 * Real.pi * κ * energyConst) * logCovConst * δ ^ 2 ≤ massQ ^ 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (κ * M.MfG δ x)) ∂(P.prod P) ≤ ENNReal.ofReal 2 := by
  set K := closedBall (0 : ℂ) (5 * δ) with hK
  set β := 25 * Real.pi * κ * energyConst with hβ
  have hβ0 : 0 ≤ β := by have := energyConst_nonneg; positivity
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hvol : volume.real K = Real.pi * (5 * δ) ^ 2 := volume_real_closedBall _ (by positivity)
  have hvol0 : volume K ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.2 (by linarith)).ne')
      (by simpa using NNReal.pi_pos.ne')
  have hvolt : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hvolr : 0 < volume.real K := ENNReal.toReal_pos hvol0 hvolt
  have hpm := M.measurable_pvG hh.measurable
  -- the one-point factor
  set Fp : Ω × ℂ → ℝ := fun p => Real.exp (2 * β * M.pvG p ^ 2) with hFp
  have hFpm : Measurable Fp := Real.measurable_exp.comp (measurable_const.mul (hpm.pow_const 2))
  have hFpc : ∀ ω, Continuous fun y => Fp (ω, y) := fun ω =>
    Real.continuous_exp.comp (continuous_const.mul ((M.continuous_pvG ω).pow 2))
  -- (1) pointwise in `x`
  have hpt : ∀ x : Ω × Ω, ENNReal.ofReal (Real.exp (κ * M.MfG δ x)) ≤
      ENNReal.ofReal (volume.real K)⁻¹ *
        ∫⁻ y in K, ENNReal.ofReal (Fp (x.1, y)) * ENNReal.ofReal (Fp (x.2, y)) := by
    intro x
    set D : ℂ → ℝ := fun y => M.pvG (x.1, y) - M.pvG (x.2, y) with hD
    have hDc : Continuous D := (M.continuous_pvG x.1).sub (M.continuous_pvG x.2)
    have hMf : κ * M.MfG δ x = ⨍ y in K, β * D y ^ 2 := by
      have e : M.MfG δ x = energyConst / δ ^ 2 * ∫ y in K, D y ^ 2 := rfl
      rw [setAverage_eq, smul_eq_mul, integral_const_mul, hvol, e]
      set I := ∫ y in K, D y ^ 2
      rw [hβ]
      field_simp
      ring
    have hbD : Continuous fun y => β * D y ^ 2 := continuous_const.mul (hDc.pow 2)
    have hJ := convexOn_exp.map_set_average_le (f := fun y => β * D y ^ 2)
      Real.continuous_exp.continuousOn isClosed_univ
      hvol0 hvolt (ae_of_all _ fun _ => mem_univ _) (hbD.continuousOn.integrableOn_compact hKc)
      ((Real.continuous_exp.comp hbD).continuousOn.integrableOn_compact hKc)
    have hprod : ∀ y, Real.exp (β * D y ^ 2) ≤ Fp (x.1, y) * Fp (x.2, y) := by
      intro y
      simp only [hFp, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      simp only [hD]
      nlinarith [sq_nonneg (M.pvG (x.1, y) + M.pvG (x.2, y)), hβ0]
    have hint2 : IntegrableOn (fun y => Fp (x.1, y) * Fp (x.2, y)) K :=
      ((hFpc x.1).mul (hFpc x.2)).continuousOn.integrableOn_compact hKc
    have havg : ⨍ y in K, Real.exp (β * D y ^ 2) ≤ ⨍ y in K, Fp (x.1, y) * Fp (x.2, y) := by
      rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hvolr.le)
      exact setIntegral_mono_on
        ((Real.continuous_exp.comp hbD).continuousOn.integrableOn_compact hKc)
        hint2 measurableSet_closedBall fun y _ => hprod y
    calc ENNReal.ofReal (Real.exp (κ * M.MfG δ x))
        = ENNReal.ofReal (Real.exp (⨍ y in K, β * D y ^ 2)) := by rw [hMf]
      _ ≤ ENNReal.ofReal (⨍ y in K, Fp (x.1, y) * Fp (x.2, y)) :=
          ENNReal.ofReal_le_ofReal (hJ.trans havg)
      _ = ENNReal.ofReal (volume.real K)⁻¹ *
          ∫⁻ y in K, ENNReal.ofReal (Fp (x.1, y)) * ENNReal.ofReal (Fp (x.2, y)) := by
          rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.2 hvolr.le),
            ofReal_integral_eq_lintegral_ofReal hint2
              (ae_of_all _ fun y => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
          congr 1
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  -- (2) the one-point moment
  have hone : ∀ y ∈ K, ∫⁻ ω, ENNReal.ofReal (Fp (ω, y)) ∂P ≤ ENNReal.ofReal (√2) := by
    intro y hy
    have hyn : ‖y‖ ≤ 5 * δ := by rwa [hK, mem_closedBall, dist_zero_right] at hy
    have hy34 : ‖y‖ < 3 / 4 := by linarith
    set μ := 2 * β / massQ ^ 2
    have hμ0 : 0 ≤ μ := div_nonneg (by positivity) (sq_nonneg _)
    have hvar : 4 * μ * logCov (radDiff quarter_pos.le y 0).1 (radDiff quarter_pos.le y 0).1 ≤ 1 := by
      have hL := logCov_radDiff_le_logCovConst (y := y) (by linarith)
      have hq := massQ_pos
      calc 4 * μ * logCov (radDiff quarter_pos.le y 0).1 (radDiff quarter_pos.le y 0).1
          ≤ 4 * μ * (logCovConst * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left hL (by positivity)
        _ ≤ 4 * μ * (logCovConst * (5 * δ) ^ 2) := by
            gcongr
            · exact logCovConst_nonneg
        _ = 200 * β * logCovConst * δ ^ 2 / massQ ^ 2 := by simp only [μ]; field_simp; ring
        _ ≤ 1 := by
            rw [div_le_one (by positivity)]
            simpa [hβ, mul_assoc, mul_comm, mul_left_comm] using hκ
    have := lintegral_exp_sq_pairing_le hh (M.measurable_G hh.measurable) M.dec M.indepFun_G_hz M.zb
      hy34 hμ0 hvar
    refine le_of_eq_of_le (lintegral_congr fun ω => ?_) this
    simp only [hFp, pvG, μ]
    congr 2
    field_simp
  -- (3) integrate
  have hFF : Measurable fun q : (Ω × Ω) × ℂ =>
      ENNReal.ofReal (Fp (q.1.1, q.2)) * ENNReal.ofReal (Fp (q.1.2, q.2)) :=
    ((hFpm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal).mul
      ((hFpm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal)
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (κ * M.MfG δ x)) ∂(P.prod P)
      ≤ ∫⁻ x, ENNReal.ofReal (volume.real K)⁻¹ *
          (∫⁻ y in K, ENNReal.ofReal (Fp (x.1, y)) * ENNReal.ofReal (Fp (x.2, y))) ∂(P.prod P) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (volume.real K)⁻¹ *
          ∫⁻ y in K, (∫⁻ x, ENNReal.ofReal (Fp (x.1, y)) * ENNReal.ofReal (Fp (x.2, y)) ∂(P.prod P)) := by
        rw [lintegral_const_mul _ (hFF.lintegral_prod_right' (ν := volume.restrict K))]
        congr 1
        exact lintegral_lintegral_swap hFF.aemeasurable
    _ ≤ ENNReal.ofReal (volume.real K)⁻¹ * ∫⁻ _ in K, ENNReal.ofReal 2 := by
        gcongr ENNReal.ofReal (volume.real K)⁻¹ * ?_
        refine setLIntegral_mono measurable_const fun y hy => ?_
        have hfy : AEMeasurable (fun ω => ENNReal.ofReal (Fp (ω, y))) P :=
          (hFpm.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal.aemeasurable
        rw [lintegral_prod_mul (μ := P) (ν := P) (f := fun ω => ENNReal.ofReal (Fp (ω, y)))
          (g := fun ω => ENNReal.ofReal (Fp (ω, y))) hfy hfy]
        calc (∫⁻ ω, ENNReal.ofReal (Fp (ω, y)) ∂P) * ∫⁻ ω, ENNReal.ofReal (Fp (ω, y)) ∂P
            ≤ ENNReal.ofReal (√2) * ENNReal.ofReal (√2) := mul_le_mul' (hone y hy) (hone y hy)
          _ = ENNReal.ofReal 2 := by
              rw [← ENNReal.ofReal_mul (by positivity), Real.mul_self_sqrt (by norm_num)]
    _ = ENNReal.ofReal 2 := by
        rw [setLIntegral_const, ← mul_assoc, mul_comm _ (ENNReal.ofReal 2), mul_assoc]
        rw [← ENNReal.ofReal_toReal hvolt, ← ENNReal.ofReal_mul (inv_nonneg.2 hvolr.le)]
        rw [show (volume.real K)⁻¹ * (volume K).toReal = 1 from inv_mul_cancel₀ hvolr.ne']
        simp

end DiskMarkov

end MatedCRTHarmonic.GMSAppA
