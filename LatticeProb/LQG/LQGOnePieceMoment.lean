import Mathlib
import LatticeProb.LQG.LQGOnePieceScaling
import LatticeProb.LQG.LQGCircleMoments
import LatticeProb.LQG.LQGBallMassGrid2

/-!
# Moments of the mass of a small ball under the approximate Liouville measure

Let `μ_ε = lqgApprox γ h ε` be the approximate Liouville measure of the circle averages `h` of a whole-plane
Gaussian free field, `R = 2^{-k}`, `z ∈ ℂ` with `|z| + R ≤ 1`, and `n > k`.  By the exact scaling of the ball mass
(`lqgApprox_ball_dyadic`), `μ_{2^{-n}}(B(z, R/4)) = R^{2+γ²/2} e^{γ h_R(z)} μ'_{2^{-(n-k)}}(B(0, 1/4))`, where `μ'`
is the approximation of the recentred and dilated circle averages, and `h_R(z)` is independent of `μ'(B(0, 1/4))`
(`indepFun_circle_lqgApprox_ball`).  Since `E e^{p γ h_R(z)} = R^{-p²γ²/2}` (the variance of `h_R(z)` is `-log R`),
for `p ≥ 0`
`E[μ_{2^{-n}}(B(z, R/4))^p] = R^{p(2+γ²/2) - p²γ²/2} E[μ'_{2^{-(n-k)}}(B(0, 1/4))^p]`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The ball mass `ω ↦ μ'_δ(B(0, ρ))` of the approximation of the recentred and dilated circle averages is
almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_lqgApprox_recentred_ball (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (k : ℕ) (z : ℂ) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    AEMeasurable (fun ω => lqgApprox γ (recentredField hcirc k z ω) δ (ball 0 ρ)) P := by
  classical
  have hR := dyadicScale_pos' k
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hRδ : 0 < dyadicScale k * δ := mul_pos hR hδ
  let Y : Ω → ball (0 : ℂ) ρ → ℝ := fun ω w =>
    H ω (dyadicScale k * δ) ((dyadicScale k : ℂ) * w + z) - H ω (dyadicScale k) z
  have hYm : ∀ w, Measurable (fun ω => Y ω w) := fun w =>
    (((hHm _ hRδ).comp (measurable_const.prodMk measurable_id)).sub
      ((hHm _ hR).comp (measurable_const.prodMk measurable_id)))
  have hcont : ∀ ω, Continuous fun w : ball (0 : ℂ) ρ => Y ω w := fun ω =>
    ((hHc ω _ hRδ).comp (by fun_prop : Continuous fun w : ball (0 : ℂ) ρ =>
      (dyadicScale k : ℂ) * (w : ℂ) + z)).sub continuous_const
  have : IsFiniteMeasure
      (Measure.comap Subtype.val (volume : Measure ℂ) : Measure (ball (0 : ℂ) ρ)) :=
    ⟨by rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply,
      Subtype.coe_image_univ]; exact measure_ball_lt_top⟩
  let F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (δ ^ (γ ^ 2 / 2) * Real.exp (γ * r))
  have hF : Measurable F := Measurable.ennreal_ofReal (by fun_prop)
  have hT : Measurable fun ω => ∫⁻ w : ball (0 : ℂ) ρ, F (Y ω w)
      ∂(Measure.comap Subtype.val (volume : Measure ℂ)) :=
    measurable_lintegral_of_continuous _ hcont hYm hF
  have hae : (fun ω => lqgApprox γ (recentredField hcirc k z ω) δ (ball 0 ρ)) =ᵐ[P]
      fun ω => ∫⁻ w : ball (0 : ℂ) ρ, F (Y ω w)
        ∂(Measure.comap Subtype.val (volume : Measure ℂ)) := by
    filter_upwards [hHae] with ω hω
    simp only [lqgApprox]
    rw [withDensity_apply _ measurableSet_ball, ← lintegral_subtype_comap measurableSet_ball]
    refine lintegral_congr fun w => ?_
    simp only [F, Y, recentredField, hω]
  exact hT.aemeasurable.congr hae.symm

/-- **Exponential moment of the scaling factor.** For `p ≥ 0`, `‖z‖ + 2^{-k} ≤ 1` and `R = 2^{-k}`,
`E[(R^{2+γ²/2} e^{γ h_R(z)})^p] = R^{p(2+γ²/2) - p²γ²/2}`. -/
theorem IsWholePlaneGFF.lintegral_dyadicFactor_rpow (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {p : ℝ}
    (hp : 0 ≤ p) {k : ℕ} {z : ℂ} (hz : ‖z‖ + dyadicScale k ≤ 1) :
    ∫⁻ ω, (dyadicFactor γ k (hcirc ω (dyadicScale k) z)) ^ p ∂P =
      ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) := by
  have hR := dyadicScale_pos' k
  set R := dyadicScale k with hRdef
  have hpt : ∀ ω, (dyadicFactor γ k (hcirc ω R z)) ^ p =
      ENNReal.ofReal (R ^ (p * (2 + γ ^ 2 / 2))) *
        ENNReal.ofReal (Real.exp (p * γ * hcirc ω R z)) := by
    intro ω
    unfold dyadicFactor
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR.le, ← Real.exp_mul]
    congr 3
    all_goals ring
  simp_rw [hpt]
  have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (p * γ * hcirc ω R z)) :=
    Measurable.ennreal_ofReal (Real.measurable_exp.comp
      ((hh.measurable_circle R z hR).const_mul _))
  rw [lintegral_const_mul _ hm]
  have hint := hh.integrable_exp_sum_circle hR (fun _ : Fin 1 => z) (fun _ => p * γ)
  have hexp := hh.integral_exp_sum_circle hR (fun _ : Fin 1 => z) (fun _ => p * γ)
  have hcov : cov[fun ω => hcirc ω R z, fun ω => hcirc ω R z; P] = -Real.log R := by
    rw [hh.covariance_circle_inside hR hR hz hz, circlePairPotential_self_center hR.le, max_self]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hint hexp
  rw [hcov] at hexp
  have hl : ∫⁻ ω, ENNReal.ofReal (Real.exp (p * γ * hcirc ω R z)) ∂P =
      ENNReal.ofReal (Real.exp (p * γ * (p * γ) * -Real.log R / 2)) := by
    rw [← hexp, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  rw [hl, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_sub hR, Real.rpow_def_of_pos hR (p ^ 2 * γ ^ 2 / 2),
    div_eq_mul_inv (R ^ _) (Real.exp _), ← Real.exp_neg]
  congr 2
  ring

/-- **Moment of the ball mass at a dyadic scale.** For `p ≥ 0`, `k < n`, `‖z‖ + 2^{-k} ≤ 1` and `R = 2^{-k}`,
`E[μ_{2^{-n}}(B(z, R/4))^p] = R^{p(2+γ²/2) - p²γ²/2} E[μ'_{2^{-(n-k)}}(B(0, 1/4))^p]`, where `μ'` is the
approximation of the recentred and dilated circle averages. -/
theorem IsWholePlaneGFF.lintegral_rpow_lqgApprox_ball_dyadic (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : γ ≠ 0) {p : ℝ} (hp : 0 ≤ p) {k n : ℕ} (hkn : k < n) {z : ℂ}
    (hz : ‖z‖ + dyadicScale k ≤ 1) :
    ∫⁻ ω, (lqgApprox γ (hcirc ω) (dyadicScale n) (ball z (dyadicScale k * (1 / 4)))) ^ p ∂P =
      ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
        ∫⁻ ω, (lqgApprox γ (recentredField hcirc k z ω) (dyadicScale (n - k)) (ball 0 (1 / 4))) ^ p ∂P := by
  have hR := dyadicScale_pos' k
  have hδ := dyadicScale_pos' (n - k)
  have hδ2 : dyadicScale (n - k) ≤ 1 / 2 := by
    obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
    rw [hm, dyadicScale_succ_eq_half]
    have := dyadicScale_le_one' m
    linarith
  have hscale : ∀ ω, lqgApprox γ (hcirc ω) (dyadicScale n) (ball z (dyadicScale k * (1 / 4))) =
      dyadicFactor γ k (hcirc ω (dyadicScale k) z) *
        lqgApprox γ (recentredField hcirc k z ω) (dyadicScale (n - k)) (ball 0 (1 / 4)) := by
    intro ω
    have h := lqgApprox_ball_dyadic hγ (hcirc ω) k z hδ.le (1 / 4)
    rw [dyadicScale_mul_dyadicScale, Nat.sub_add_cancel hkn.le] at h
    exact h
  simp_rw [hscale, ENNReal.mul_rpow_of_nonneg _ _ hp]
  have hind := LatticeProb.LQG.IsWholePlaneGFF.indepFun_circle_lqgApprox_ball hh γ hz hδ
    (by linarith : (1 / 4 : ℝ) + dyadicScale (n - k) ≤ 1)
  have hφ : Measurable fun x : ℝ => (dyadicFactor γ k x) ^ p := by
    unfold dyadicFactor
    exact (Measurable.ennreal_ofReal (by fun_prop)).pow_const _
  have hind2 := hind.comp hφ (measurable_id.pow_const p)
  have hf : AEMeasurable (fun ω => (dyadicFactor γ k (hcirc ω (dyadicScale k) z)) ^ p) P :=
    (hφ.comp (hh.measurable_circle _ z hR)).aemeasurable
  have hg := (LatticeProb.LQG.IsWholePlaneGFF.aemeasurable_lqgApprox_recentred_ball hh γ k z hδ (1 / 4)).pow_const p
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hf hg hind2,
    LatticeProb.LQG.IsWholePlaneGFF.lintegral_dyadicFactor_rpow hh γ hp hz]

end LatticeProb.LQG
