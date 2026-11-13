/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.JointScalingOPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaScalingHolds

/-!
#  the pathwise identities of the joint-scaling identity (area parametrization and its rescaling)

Deterministic statements about one
sample, used almost surely in `JointScalingOMain`:

* `coe_eq_parEval_of_areaParam`: if the area approximations of the field `h` converge vaguely and
  `c = c_L ∘ φ` (`φ : ℝ ≃o ℝ`, `φ 0 = 0`) is parametrized by `μ_h`-area, then
  `c(t) = parEval γ h c_L t` for every `t` — the area-parametrized curve is the measurable
  functional `parEval` of (field, Lebesgue-parametrized curve);
* `coe_coneRescaleCurve_eq_parEval`: under the random-dilation covariance
  `μ_{h_b}(A) = b⁻¹ μ_h(R A)` for all sets `A` and the positivity of
  `μ_h` on `B_R(0)`, the rescaled curve `η^b = R⁻¹ η(b ·)` is the same functional of
  the rescaled pair: `η^b(t) = parEval γ h_b (dilCurve R c_L) t`, `dilCurve R c_L = R⁻¹ c_L(R² ·)`.
  This is the scaling identity `Par(ν, c')(t) = R⁻¹ Par(m, c)(bt)` (`ν = b⁻¹(R·)^* m`, `c' = R⁻¹ c(R² ·)`);
  the reparametrization is `ψ(t) = R⁻² φ(bt)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

open LQGMetric

/-- A vague limit of the area approximations exists ⇒ `lqgArea` is one. -/
theorem isVagueLimitC_lqgArea_of_exists {γ : ℝ} {h : DistC}
    (hv : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ) :
    IsVagueLimitC (lqgAreaApprox γ h) (lqgArea γ h) := by
  unfold lqgArea
  rw [dite_eq_left hv]
  exact Classical.choose_spec hv

/-- **The area-parametrized curve is `parEval` of the Lebesgue-parametrized one** (pathwise). -/
theorem coe_eq_parEval_of_areaParam {γ : ℝ} {h : DistC} {cL c : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ}
    (hv : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ) (hφ0 : φ 0 = 0) (hφ : ∀ t, c t = cL (φ t))
    (harea : ∀ s t : ℝ, s ≤ t → lqgArea γ h (c '' Icc s t) = ENNReal.ofReal (t - s)) :
    (⇑c : ℝ → ℂ) = fun t => parEval γ h cL t := by
  have hcφ : (⇑c : ℝ → ℂ) = fun u => cL (φ u) := funext hφ
  have harea' : ∀ s t : ℝ, s ≤ t →
      lqgArea γ h ((fun u => cL (φ u)) '' Icc s t) = ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [← hcφ]
    exact harea s t hst
  funext t
  rw [parEval_eq (isVagueLimitC_lqgArea_of_exists hv) hφ0 harea' t, hφ t]

/-- `(R ·)(η^b([s, t])) = η([bs, bt])`. -/
theorem image_mul_coneRescaleCurve {R b : ℝ} (hR : 0 < R) (hb : 0 < b) (c : C(ℝ, ℂ)) {s t : ℝ}
    (hst : s ≤ t) :
    (fun w : ℂ => (R : ℂ) * w) '' (coneRescaleCurve R b c '' Icc s t) = c '' Icc (b * s) (b * t) := by
  rw [image_image]
  have e : (fun u => (R : ℂ) * coneRescaleCurve R b c u) = fun u => c (b * u) := by
    funext u
    change (R : ℂ) * (((R⁻¹ : ℝ) : ℂ) * c (b * u)) = c (b * u)
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hR.ne', Complex.ofReal_one, one_mul]
  rw [e, ← image_mul_left_Icc hb.le hst, image_image]

/-- **The rescaled curve is `parEval` of the rescaled pair** (pathwise; the scaling argument step 4). -/
theorem coe_coneRescaleCurve_eq_parEval {γ : ℝ} {h : DistC} {cL c : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ}
    {R b : ℝ} (hR : 0 < R) (hb : 0 < b) (hφ0 : φ 0 = 0) (hφ : ∀ t, c t = cL (φ t))
    (harea : ∀ s t : ℝ, s ≤ t → lqgArea γ h (c '' Icc s t) = ENNReal.ofReal (t - s))
    (hcov : ∀ A : Set ℂ, lqgArea γ (coneRescaleField γ R b h) A =
      ENNReal.ofReal b⁻¹ * lqgArea γ h ((fun w => (R : ℂ) * w) '' A))
    (hpos : 0 < lqgArea γ h (ball 0 R)) :
    (⇑(coneRescaleCurve R b c) : ℝ → ℂ) =
      fun t => parEval γ (coneRescaleField γ R b h) (dilCurve R cL) t := by
  -- the rescaled field has a genuine area limit (its area is not the junk `0`)
  have hv' : IsVagueLimitC (lqgAreaApprox γ (coneRescaleField γ R b h))
      (lqgArea γ (coneRescaleField γ R b h)) := by
    apply isVagueLimitC_lqgArea_of_exists
    apply ConeScaling.exists_isVagueLimitC_of_lqgArea_ne_zero (U := ball 0 1)
    rw [hcov, ConeScaling.image_mul_ball_one hR]
    refine mul_ne_zero ?_ hpos.ne'
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, inv_pos]
    exact hb
  -- the reparametrization `ψ(t) = R⁻² φ(bt)`
  have hR2 : 0 < (R ^ 2)⁻¹ := by positivity
  let ψ : ℝ ≃o ℝ := (OrderIso.mulLeft₀ b hb).trans (φ.trans (OrderIso.mulLeft₀ ((R ^ 2)⁻¹) hR2))
  have hψ : ∀ u, ψ u = (R ^ 2)⁻¹ * φ (b * u) := fun u => rfl
  have hψ0 : ψ 0 = 0 := by rw [hψ, mul_zero, hφ0, mul_zero]
  have hcurveψ : ∀ u, dilCurve R cL (ψ u) = coneRescaleCurve R b c u := by
    intro u
    rw [dilCurve_apply, hψ, ← mul_assoc, mul_inv_cancel₀ (by positivity : R ^ 2 ≠ 0), one_mul,
      ← hφ]
    rfl
  have harea' : ∀ s t : ℝ, s ≤ t → lqgArea γ (coneRescaleField γ R b h)
      ((fun u => dilCurve R cL (ψ u)) '' Icc s t) = ENNReal.ofReal (t - s) := by
    intro s t hst
    have e1 : (fun u => dilCurve R cL (ψ u)) = fun u => coneRescaleCurve R b c u := funext hcurveψ
    have hbst : b * s ≤ b * t := mul_le_mul_of_nonneg_left hst hb.le
    rw [e1, hcov, show (fun u => coneRescaleCurve R b c u) = ⇑(coneRescaleCurve R b c) from rfl,
      image_mul_coneRescaleCurve hR hb c hst, harea _ _ hbst,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hb.le)]
    congr 1
    field_simp
  funext t
  rw [parEval_eq hv' hψ0 harea' t, hcurveψ]

end JointScalingO

end MatedCRTHarmonic.CellScaling
