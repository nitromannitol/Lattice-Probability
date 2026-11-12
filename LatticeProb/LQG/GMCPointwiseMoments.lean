import LatticeProb.Gauss.CircleAverageCovariance

/-!
# Pointwise exponential moments of circle averages (truncated second-moment method)

Let `h` be a whole-plane GFF with circle averages `h_r(z)`. Fix `0 < ε`, `R` and `z` with `‖z‖ + ε ≤ R`, and write
`X = h_ε(z) - h_R(0)` (law `N(0, L)`, `L = log (R / ε)`) and `D = h_{ε/2}(z) - h_ε(z)` (law `N(0, log 2)`).
This file proves the pointwise estimates behind the construction of the Gaussian multiplicative chaos
`ε^{γ²/2} e^{γ h_ε(z)} dz` by the truncated second-moment method (Duplantier-Sheffield 2011, Section 3):

* `D` is independent of `X`, and of `(X_z, X_w, D_w)` when the discs `B_ε(z)` and `B_ε(w)` have disjoint
  interiors (`indepFun_recentred_increment`, `indepFun_recentred_increment_of_le`);
* thick points: `E[e^{γ X}; X ≥ α L] ≤ e^{L (γ²/2 - (α - γ)²/2)}` for `γ ≤ α`, and the coarse-to-fine identity
  `E[e^{γ X} e^{γ D}; X ≥ a] = 2^{γ²/2} E[e^{γ X}; X ≥ a]` (`integral_thick_le`, `integral_thick_mul_exp_increment`);
* thin points: the martingale increment `T = e^{γ X} 1{X ≤ α L} (2^{-γ²/2} e^{γ D} - 1)` satisfies
  `E[T_z T_w] = 0` when `2 ε ≤ |z - w|`, and `E[T²] ≤ (2^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}` for `α ≤ 2γ`
  (`integral_thin_mul_thin_eq_zero`, `integral_thin_sq_le`);
* the deterministic decomposition `(ε/2)^{γ²/2} e^{γ(x + d)} - ε^{γ²/2} e^{γ x} = ε^{γ²/2} e^{γ x} W(d)` with
  `W(d) = 2^{-γ²/2} e^{γ d} - 1` (`rpow_mul_exp_add_sub_eq`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace LatticeProb.GaussTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Upper-truncated exponential moment in the scale parametrization, for a random variable of law `N(0, L)`:
`E[e^{tX}; X ≥ α L] ≤ exp (L (t² / 2 - (α - t)² / 2))` for `t ≤ α`. -/
theorem integral_indicator_Ici_exp_mul_le_of_hasLaw {L : ℝ≥0} (hX : HasLaw X (gaussianReal 0 L) P) {t α : ℝ}
    (htα : t ≤ α) :
    ∫ ω, (Set.Ici (α * L)).indicator (fun x => rexp (t * x)) (X ω) ∂P ≤
      rexp (L * (t ^ 2 / 2 - (α - t) ^ 2 / 2)) := by
  have hm : Measurable ((Set.Ici (α * (L : ℝ))).indicator fun x => rexp (t * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (t * x)).indicator measurableSet_Ici
  have h := hX.integral_comp hm.aestronglyMeasurable
  rw [integral_indicator measurableSet_Ici] at h
  exact (le_of_eq h).trans (setIntegral_Ici_exp_mul_gaussianReal_le_scale L htα)

/-- Lower-truncated exponential moment in the scale parametrization, for a random variable of law `N(0, L)`:
`E[e^{tX}; X ≤ α L] ≤ exp (L (t² / 2 - (t - α)² / 2))` for `α ≤ t`. -/
theorem integral_indicator_Iic_exp_mul_le_of_hasLaw {L : ℝ≥0} (hX : HasLaw X (gaussianReal 0 L) P) {t α : ℝ}
    (hαt : α ≤ t) :
    ∫ ω, (Set.Iic (α * L)).indicator (fun x => rexp (t * x)) (X ω) ∂P ≤
      rexp (L * (t ^ 2 / 2 - (t - α) ^ 2 / 2)) := by
  have hm : Measurable ((Set.Iic (α * (L : ℝ))).indicator fun x => rexp (t * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (t * x)).indicator measurableSet_Iic
  have h := hX.integral_comp hm.aestronglyMeasurable
  rw [integral_indicator measurableSet_Iic] at h
  exact (le_of_eq h).trans (setIntegral_Iic_exp_mul_gaussianReal_le_scale L hαt)

/-- The square of a truncated exponential is a truncated exponential. -/
theorem indicator_exp_mul_sq (s : Set ℝ) (γ x : ℝ) :
    s.indicator (fun x => rexp (γ * x)) x ^ 2 = s.indicator (fun x => rexp (2 * γ * x)) x := by
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    rw [sq, ← Real.exp_add]
    ring_nf
  · simp [hx]

end LatticeProb.GaussTail

namespace LatticeProb.GaussIndep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {β : Type*} [MeasurableSpace β] {Y : Ω → β}
  {D : Ω → ℝ} {v : ℝ≥0}

/-- If `D ~ N(0, v)` is independent of `Y`, then `E[F(Y) e^{γ D}] = E[F(Y)] e^{γ² v / 2}`. No integrability of
`F ∘ Y` is needed. -/
theorem integral_mul_exp_mul (hD : HasLaw D (gaussianReal 0 v) P) (hY : AEMeasurable Y P)
    (hind : IndepFun Y D P) {F : β → ℝ} (hF : Measurable F) (γ : ℝ) :
    ∫ ω, F (Y ω) * rexp (γ * D ω) ∂P = (∫ ω, F (Y ω) ∂P) * rexp (γ ^ 2 * v / 2) := by
  have hE : Measurable fun x : ℝ => rexp (γ * x) := by fun_prop
  have hi : IndepFun (F ∘ Y) ((fun x : ℝ => rexp (γ * x)) ∘ D) P := hind.comp hF hE
  have h := hi.integral_mul_eq_mul_integral (hF.comp_aemeasurable hY).aestronglyMeasurable
    (hE.comp_aemeasurable hD.aemeasurable).aestronglyMeasurable
  have h0 : ∫ ω, ((fun x : ℝ => rexp (γ * x)) ∘ D) ω ∂P = rexp (γ ^ 2 * v / 2) := by
    refine (hD.integral_comp (f := fun x : ℝ => rexp (γ * x)) hE.aestronglyMeasurable).trans ?_
    rw [GaussTail.integral_exp_mul_gaussianReal_zero]
    congr 1
    ring
  rw [h0] at h
  exact h

end LatticeProb.GaussIndep

namespace LatticeProb.Gauss

/-- The deterministic coarse-to-fine decomposition of the normalized exponential:
`(ε/2)^{γ²/2} e^{γ (x + d)} - ε^{γ²/2} e^{γ x} = ε^{γ²/2} e^{γ x} (2^{-γ²/2} e^{γ d} - 1)`, the last factor being the
exponential weight of variance `log 2`. -/
theorem rpow_mul_exp_add_sub_eq {ε : ℝ} (hε : 0 < ε) (γ x d : ℝ) :
    (ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) - ε ^ (γ ^ 2 / 2) * rexp (γ * x) =
      ε ^ (γ ^ 2 / 2) * rexp (γ * x) * GaussIndep.expWeight γ (Real.log 2).toNNReal d := by
  have hlog : ((Real.log 2).toNNReal : ℝ) = Real.log 2 :=
    Real.coe_toNNReal _ (Real.log_nonneg one_le_two)
  have h2 : (2 : ℝ) ^ (γ ^ 2 / 2) = rexp (γ ^ 2 * Real.log 2 / 2) := by
    rw [Real.rpow_def_of_pos two_pos]
    congr 1
    ring
  have hneg : rexp (-(γ ^ 2 * Real.log 2) / 2) = (rexp (γ ^ 2 * Real.log 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [GaussIndep.expWeight, hlog, hneg, Real.div_rpow hε.le zero_le_two, h2, mul_add, Real.exp_add]
  field_simp

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The dyadic increment `h_{ε/2}(z) - h_ε(z)` is independent of the recentred circle average
`h_ε(z) - h_R(0)`. -/
theorem indepFun_recentred_increment (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ‖z‖ + ε ≤ R) :
    IndepFun (fun ω => hcirc ω ε z - hcirc ω R 0) (fun ω => hcirc ω (ε / 2) z - hcirc ω ε z) P := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have key := GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (hh.circle_sub_mem_span (half_pos hε) hε z z)
    (B := fun _ : Unit => fun ω => hcirc ω ε z - hcirc ω R 0)
    (fun _ => hh.circle_sub_mem_span hε hR z 0)
    (fun _ => hh.covariance_increment_recentred_same_center hε le_rfl hz)
  exact (key.comp (φ := id) (ψ := fun f : Unit → ℝ => f ()) measurable_id (measurable_pi_apply ())).symm

/-- When the discs `B_ε(z)` and `B_ε(w)` have disjoint interiors, the dyadic increment at `z` is independent of the
recentred circle averages at `z` and `w` and of the dyadic increment at `w`. -/
theorem indepFun_recentred_increment_of_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε)
    {z w : ℂ} (hz : ‖z‖ + ε ≤ R) (hw : ‖w‖ + ε ≤ R) (hzw : 2 * ε ≤ ‖z - w‖) :
    IndepFun (fun ω => (hcirc ω ε z - hcirc ω R 0, hcirc ω ε w - hcirc ω R 0,
        hcirc ω (ε / 2) w - hcirc ω ε w)) (fun ω => hcirc ω (ε / 2) z - hcirc ω ε z) P := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have key := GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (hh.circle_sub_mem_span (half_pos hε) hε z z)
    (B := ![fun ω => hcirc ω ε z - hcirc ω R 0, fun ω => hcirc ω ε w - hcirc ω R 0,
      fun ω => hcirc ω (ε / 2) w - hcirc ω ε w])
    (by
      intro t
      fin_cases t
      exacts [hh.circle_sub_mem_span hε hR z 0, hh.circle_sub_mem_span hε hR w 0,
        hh.circle_sub_mem_span (half_pos hε) hε w w])
    (by
      intro t
      fin_cases t
      exacts [hh.covariance_increment_recentred_same_center hε le_rfl hz,
        hh.covariance_increment_recentred_of_add_le hε hε hz hw (by linarith),
        hh.covariance_increment_increment_of_le hε hzw])
  have hm : Measurable fun f : Fin 3 → ℝ => (f 0, f 1, f 2) := by fun_prop
  exact (key.comp (φ := id) (ψ := fun f : Fin 3 → ℝ => (f 0, f 1, f 2)) measurable_id hm).symm

/-- Thick points: `E[e^{γ X}; X ≥ α L] ≤ e^{L (γ²/2 - (α - γ)²/2)}` for `X = h_ε(z) - h_R(0)`,
`L = log (R / ε)` and `γ ≤ α`. -/
theorem integral_thick_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ‖z‖ + ε ≤ R) {γ α : ℝ} (hγα : γ ≤ α) :
    ∫ ω, (Set.Ici (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) ∂P ≤
      rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) := by
  have hεR : ε ≤ R := by linarith [norm_nonneg z]
  have hL : ((Real.log (R / ε)).toNNReal : ℝ) = Real.log (R / ε) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hε).mpr hεR))
  have h := GaussTail.integral_indicator_Ici_exp_mul_le_of_hasLaw (hh.hasLaw_recentred_circle hε hz) hγα
  rwa [hL] at h

/-- Coarse-to-fine identity on the thick event: `E[e^{γ X} e^{γ D}; X ≥ a] = 2^{γ²/2} E[e^{γ X}; X ≥ a]`, written
with `2^{γ²/2} = e^{γ² log 2 / 2}`. -/
theorem integral_thick_mul_exp_increment (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ‖z‖ + ε ≤ R) (γ a : ℝ) :
    ∫ ω, (Set.Ici a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z)) ∂P =
      (∫ ω, (Set.Ici a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) ∂P) *
        rexp (γ ^ 2 * Real.log 2 / 2) := by
  have hlog : ((Real.log 2).toNNReal : ℝ) = Real.log 2 :=
    Real.coe_toNNReal _ (Real.log_nonneg one_le_two)
  have hm : Measurable ((Set.Ici a).indicator fun x => rexp (γ * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ici
  have h := GaussIndep.integral_mul_exp_mul (hh.hasLaw_increment hε z)
    (hh.hasLaw_recentred_circle hε hz).aemeasurable (hh.indepFun_recentred_increment hε hz) hm γ
  rwa [hlog] at h

/-- Thin points, orthogonality: for `T_z = e^{γ X_z} 1{X_z ≤ a} W(D_z)` with the exponential weight
`W(d) = 2^{-γ²/2} e^{γ d} - 1`, `E[T_z T_w] = 0` whenever `2 ε ≤ |z - w|`. -/
theorem integral_thin_mul_thin_eq_zero (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z w : ℂ}
    (hz : ‖z‖ + ε ≤ R) (hw : ‖w‖ + ε ≤ R) (hzw : 2 * ε ≤ ‖z - w‖) (γ a : ℝ) :
    ∫ ω, (Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z) *
        ((Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε w - hcirc ω R 0) *
          GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) w - hcirc ω ε w)) ∂P = 0 := by
  set F : ℝ → ℝ := (Set.Iic a).indicator fun x => rexp (γ * x) with hFdef
  have hF : Measurable F :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  set G : ℝ × ℝ × ℝ → ℝ := fun p => F p.1 * (F p.2.1 * GaussIndep.expWeight γ (Real.log 2).toNNReal p.2.2)
    with hGdef
  have hG : Measurable G :=
    (hF.comp measurable_fst).mul ((hF.comp (measurable_fst.comp measurable_snd)).mul
      ((GaussIndep.measurable_expWeight γ _).comp (measurable_snd.comp measurable_snd)))
  have hY : AEMeasurable (fun ω => (hcirc ω ε z - hcirc ω R 0, hcirc ω ε w - hcirc ω R 0,
      hcirc ω (ε / 2) w - hcirc ω ε w)) P :=
    (hh.hasLaw_recentred_circle hε hz).aemeasurable.prodMk
      ((hh.hasLaw_recentred_circle hε hw).aemeasurable.prodMk (hh.hasLaw_increment hε w).aemeasurable)
  have h := GaussIndep.integral_mul_expWeight_eq_zero (hh.hasLaw_increment hε z) hY
    (hh.indepFun_recentred_increment_of_le hε hz hw hzw) hG γ
  refine Eq.trans ?_ h
  congr 1
  funext ω
  simp only [hGdef]
  ring

/-- Thin points, second moment: `E[T²] = (2^{γ²} - 1) E[e^{2γ X}; X ≤ a]`, written with `2^{γ²} = e^{γ² log 2}`. -/
theorem integral_thin_sq (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ‖z‖ + ε ≤ R) (γ a : ℝ) :
    ∫ ω, ((Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z)) ^ 2 ∂P =
      (∫ ω, (Set.Iic a).indicator (fun x => rexp (2 * γ * x)) (hcirc ω ε z - hcirc ω R 0) ∂P) *
        (rexp (γ ^ 2 * Real.log 2) - 1) := by
  have hlog : ((Real.log 2).toNNReal : ℝ) = Real.log 2 :=
    Real.coe_toNNReal _ (Real.log_nonneg one_le_two)
  have hm : Measurable ((Set.Iic a).indicator fun x => rexp (γ * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  have h := GaussIndep.integral_mul_expWeight_sq (hh.hasLaw_increment hε z)
    (hh.hasLaw_recentred_circle hε hz).aemeasurable (hh.indepFun_recentred_increment hε hz) hm γ
  rw [hlog] at h
  rw [h]
  congr 2
  funext ω
  exact GaussTail.indicator_exp_mul_sq _ γ _

/-- Thin points, second-moment bound: for `α ≤ 2γ`,
`E[T²] ≤ (2^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}` with `L = log (R / ε)` and the truncation `X ≤ α L`. -/
theorem integral_thin_sq_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    ∫ ω, ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z)) ^ 2 ∂P ≤
      (rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) := by
  have hεR : ε ≤ R := by linarith [norm_nonneg z]
  have hL : ((Real.log (R / ε)).toNNReal : ℝ) = Real.log (R / ε) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hε).mpr hεR))
  have hb := GaussTail.integral_indicator_Iic_exp_mul_le_of_hasLaw (hh.hasLaw_recentred_circle hε hz) hα
  rw [hL] at hb
  have hc : 0 ≤ rexp (γ ^ 2 * Real.log 2) - 1 := by
    have : 0 ≤ γ ^ 2 * Real.log 2 := mul_nonneg (sq_nonneg γ) (Real.log_nonneg one_le_two)
    linarith [Real.add_one_le_exp (γ ^ 2 * Real.log 2)]
  rw [hh.integral_thin_sq hε hz, mul_comm]
  refine mul_le_mul_of_nonneg_left (hb.trans (le_of_eq ?_)) hc
  congr 1
  ring

end IsWholePlaneGFF

end LatticeProb.Gauss
