import Mathlib
import LatticeProb.Gauss.GFFCovPSD2
import LatticeProb.Gauss.GFFCovPSD5

/-!
# Logarithmic potentials, the unit circle, and the covariance decomposition

* `logPotential X = ∫ w_X(a) log⁺‖p_X a‖ dλ_X(a)` is the integral of the kernel `log⁺|·|` of the covariance
  (`wholePlaneCov x y = log⁺|x| + log⁺|y| - log|x - y|` off the diagonal, from `wholePlaneCov_eq_log_sub` in `LatticeProb.Gauss.GFFCovSymm`).
* `cov_eq`: `Cov(X, Y) = L_X B_Y + B_X L_Y - Λ(X, Y)`, the covariance split off the diagonal (diagonal null set).
* The unit circle `∂B_1(0)` (`unitCircle`): total mass `B = 1`, `log⁺|·| = 0` on it, and by Jensen's formula
  (`Real.circleAverage_log_norm_sub_const_eq_posLog`) `Λ(unitCircle, Y) = Λ(Y, unitCircle) = L_Y`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped Real

namespace LatticeProb.Gauss.GFFCovPSD

namespace SmearRep

/-- The logarithmic potential `L_X = ∫ w_X(a) log⁺‖p_X a‖ dλ_X(a)`. -/
noncomputable def logPotential {o : GFFObservable} (X : SmearRep o) : ℝ :=
  ∫ a, X.w a * Real.posLog ‖X.p a‖ ∂X.lam

/-- The logarithmic energy `Λ(X, Y) = ∫∫ w_X(a) w_Y(b) log‖p_X a - p_Y b‖`. -/
noncomputable def logEnergy {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') : ℝ :=
  ∫ q, X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖ ∂(X.lam.prod Y.lam)

/-- The weight times the logarithmic potential is integrable (bounded support, `log⁺` continuous). -/
lemma integrable_w_posLog {o : GFFObservable} (X : SmearRep o) :
    Integrable (fun a => X.w a * Real.posLog ‖X.p a‖) X.lam := by
  obtain ⟨R, hR⟩ := X.w_supp
  refine Integrable.mono' (X.w_int.norm.mul_const (Real.posLog (max R 0))) ?_ (ae_of_all _ fun a => ?_)
  · exact (X.w_meas.mul (Real.continuous_posLog.measurable.comp X.p_meas.norm)).aestronglyMeasurable
  · by_cases h : X.w a = 0
    · simp [h]
    · have hp : ‖X.p a‖ ≤ max R 0 := le_max_of_le_left (hR a h)
      rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ Real.posLog ‖X.p a‖ from Real.posLog_nonneg)]
      exact mul_le_mul_of_nonneg_left (Real.posLog_le_posLog (by linarith [norm_nonneg (X.p a)]) hp)
        (norm_nonneg _)

lemma logPot_eq (x : ℂ) : Real.log (max ‖x‖ 1) = Real.posLog ‖x‖ := by
  rw [Real.posLog_eq_log_max_one (norm_nonneg x), max_comm]

/-- The covariance splits off the diagonal (a null set for both smearing measures):
`Cov(X, Y) = L_X B_Y + B_X L_Y - Λ(X, Y)`. -/
theorem cov_eq {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') :
    wholePlaneGFFCov o o' = X.logPotential * Y.mass + X.mass * Y.logPotential - X.logEnergy Y := by
  rw [wholePlaneGFFCov_eq_integral X Y]
  have hpt : ∀ᵐ q ∂(X.lam.prod Y.lam), kern X Y q =
      (X.w q.1 * Real.posLog ‖X.p q.1‖) * Y.w q.2 + X.w q.1 * (Y.w q.2 * Real.posLog ‖Y.p q.2‖)
        - X.w q.1 * Y.w q.2 * Real.log ‖X.p q.1 - Y.p q.2‖ := by
    filter_upwards [X.ae_ne Y] with q hq
    rw [kern, LatticeProb.Gauss.GFFCovSymm.wholePlaneCov_eq_log_sub hq, logPot_eq, logPot_eq]
    ring
  have i1 : Integrable (fun q : X.α × Y.α => (X.w q.1 * Real.posLog ‖X.p q.1‖) * Y.w q.2)
      (X.lam.prod Y.lam) := (X.integrable_w_posLog).mul_prod Y.w_int
  have i2 : Integrable (fun q : X.α × Y.α => X.w q.1 * (Y.w q.2 * Real.posLog ‖Y.p q.2‖))
      (X.lam.prod Y.lam) := X.w_int.mul_prod Y.integrable_w_posLog
  have i12 : Integrable (fun q : X.α × Y.α => (X.w q.1 * Real.posLog ‖X.p q.1‖) * Y.w q.2 +
      X.w q.1 * (Y.w q.2 * Real.posLog ‖Y.p q.2‖)) (X.lam.prod Y.lam) := i1.add i2
  rw [integral_congr_ae hpt, integral_sub i12 (integrable_log_mul X Y), integral_add i1 i2,
    integral_prod_mul (fun a => X.w a * Real.posLog ‖X.p a‖) Y.w,
    integral_prod_mul X.w (fun b => Y.w b * Real.posLog ‖Y.p b‖)]
  simp only [logPotential, mass, logEnergy]

/-- The unit circle `∂B_1(0)`, the smearing representation of the observable `circle 1 0`. -/
noncomputable def unitCircle : SmearRep (GFFObservable.circle 1 0) := circleRep one_pos

lemma unitCircle_w (a : unitCircle.α) : unitCircle.w a = (2 * π)⁻¹ := rfl

lemma unitCircle_p (a : unitCircle.α) : unitCircle.p a = circleMap 0 1 a := rfl

/-- The unit circle has total mass one. -/
lemma unitCircle_mass : unitCircle.mass = 1 := by
  show ∫ _ : ℝ, (2 * π)⁻¹ ∂(volume.restrict (Ioc (0 : ℝ) (2 * π))) = 1
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal Real.two_pi_pos.le, smul_eq_mul]
  field_simp

/-- The logarithmic potential of the unit circle vanishes: `log⁺|p_0 a| = log⁺ 1 = 0`. -/
lemma unitCircle_logPotential : unitCircle.logPotential = 0 := by
  have hn : ∀ a : unitCircle.α, ‖unitCircle.p a‖ = 1 := fun a => by
    rw [unitCircle_p]
    exact (norm_circleMap_zero 1 a).trans (by norm_num)
  unfold logPotential
  simp only [hn, Real.posLog_one, mul_zero, integral_zero]

/-- Jensen's formula on the unit circle: `∫ w_0(a) log‖p_0 a - y‖ dλ_0(a) = log⁺|y|`. -/
lemma unitCircle_log (y : ℂ) :
    ∫ a, unitCircle.w a * Real.log ‖unitCircle.p a - y‖ ∂unitCircle.lam = Real.posLog ‖y‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := y)
  simp only [Real.circleAverage_def, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity),
    smul_eq_mul] at h
  rw [← h]
  simp only [unitCircle_w, unitCircle_p]
  rw [integral_const_mul]
  rfl

/-- The circle is the first factor: `Λ(unitCircle, Y) = L_Y`. -/
lemma logEnergy_unitCircle_left {o : GFFObservable} (Y : SmearRep o) :
    unitCircle.logEnergy Y = Y.logPotential := by
  unfold logEnergy logPotential
  have hswap : ∫ a, ∫ b, unitCircle.w a * Y.w b * Real.log ‖unitCircle.p a - Y.p b‖ ∂Y.lam ∂unitCircle.lam
      = ∫ b, ∫ a, unitCircle.w a * Y.w b * Real.log ‖unitCircle.p a - Y.p b‖ ∂unitCircle.lam ∂Y.lam :=
    integral_integral_swap (integrable_log_mul unitCircle Y)
  rw [integral_prod _ (integrable_log_mul unitCircle Y), hswap]
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  calc ∫ a, unitCircle.w a * Y.w b * Real.log ‖unitCircle.p a - Y.p b‖ ∂unitCircle.lam
      = Y.w b * ∫ a, unitCircle.w a * Real.log ‖unitCircle.p a - Y.p b‖ ∂unitCircle.lam :=
        by rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun a => by ring)
    _ = Y.w b * Real.posLog ‖Y.p b‖ := by rw [unitCircle_log]

/-- Symmetry of the logarithmic energy. -/
lemma logEnergy_comm {o o' : GFFObservable} (X : SmearRep o) (Y : SmearRep o') :
    Y.logEnergy X = X.logEnergy Y := by
  unfold logEnergy
  have h := integral_prod_swap (μ := X.lam) (ν := Y.lam)
    (fun z : X.α × Y.α => X.w z.1 * Y.w z.2 * Real.log ‖X.p z.1 - Y.p z.2‖)
  refine Eq.trans ?_ h
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]
  ring

/-- The circle is the second factor: `Λ(Y, unitCircle) = L_Y`. -/
lemma logEnergy_unitCircle_right {o : GFFObservable} (Y : SmearRep o) :
    Y.logEnergy unitCircle = Y.logPotential := by
  rw [logEnergy_comm, logEnergy_unitCircle_left]

/-- `Λ(unitCircle, unitCircle) = 0`. -/
lemma logEnergy_unitCircle_self : unitCircle.logEnergy unitCircle = 0 := by
  rw [logEnergy_unitCircle_left, unitCircle_logPotential]

end SmearRep

end LatticeProb.Gauss.GFFCovPSD
