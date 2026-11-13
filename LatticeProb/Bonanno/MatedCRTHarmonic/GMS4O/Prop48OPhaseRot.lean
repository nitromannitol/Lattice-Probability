/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OPhaseRot at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Field

/-!
# Rotation covariance of the dyadic GMC and of the area clock

Deterministic part of the phase-independence argument used in [18] Lemma 4.9 / Proposition 4.8
. If the dyadic circle averages of a
field `h'` are those of `h` read in rotated coordinates, `h'_{2^{-k}}(z) = h_{2^{-k}}(e^{iθ} z)` for
a.e. `z`, then

* the dyadic GMC approximations of `h'` are the images of those of `h` under `z ↦ e^{-iθ} z`
  (`p48o_lqgAreaApprox_eq_map_rot`), hence so is every vague limit (`p48o_isVagueLimitC_rot`);
* the area clock of the rotated Lebesgue curve `e^{-iθ} c` for `h'` is that of `c` for `h`, so the
  area-parametrized evaluation is rotated: `parEval γ h' (e^{-iθ} c) t = e^{-iθ} parEval γ h c t`
  (`p48o_parEval_rot`).

`p48oRot θ` is the rotation `z ↦ e^{iθ} z` as a real linear isometry of `ℂ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4O

open LQGMetric MatedCRTHarmonic.CellScaling

/-- The rotation `z ↦ e^{iθ} z`. -/
abbrev p48oRot (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ := rotation (Circle.exp θ)

lemma p48oRot_apply (θ : ℝ) (z : ℂ) : p48oRot θ z = Complex.exp (θ * Complex.I) * z := by
  simp [p48oRot, rotation_apply, Circle.coe_exp]

lemma p48oRot_neg_apply_rot (θ : ℝ) (z : ℂ) : p48oRot (-θ) (p48oRot θ z) = z := by
  rw [p48oRot_apply, p48oRot_apply, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

lemma p48oRot_apply_rot_neg (θ : ℝ) (z : ℂ) : p48oRot θ (p48oRot (-θ) z) = z := by
  have h := p48oRot_neg_apply_rot (-θ) z
  rwa [neg_neg] at h

lemma measurePreserving_p48oRot (θ : ℝ) :
    MeasurePreserving (p48oRot θ) (volume : Measure ℂ) volume :=
  (p48oRot θ).measurePreserving

lemma measurableEmbedding_p48oRot (θ : ℝ) : MeasurableEmbedding (p48oRot θ) :=
  (p48oRot θ).toHomeomorph.measurableEmbedding

lemma measurable_p48oRot (θ : ℝ) : Measurable (p48oRot θ) :=
  (p48oRot θ).continuous.measurable

/-- Lebesgue densities transform contravariantly under rotation. -/
lemma p48o_map_withDensity_rot (θ : ℝ) (d : ℂ → ℝ≥0∞) :
    (volume.withDensity d).map (p48oRot (-θ)) =
      volume.withDensity (fun z => d (p48oRot θ z)) := by
  ext A hA
  rw [Measure.map_apply (measurable_p48oRot (-θ)) hA,
    withDensity_apply _ ((measurable_p48oRot (-θ)) hA), withDensity_apply _ hA]
  have hpre : (p48oRot θ) ⁻¹' ((p48oRot (-θ)) ⁻¹' A) = A := by
    ext z
    simp only [mem_preimage, p48oRot_neg_apply_rot]
  have h := (measurePreserving_p48oRot θ).setLIntegral_comp_preimage_emb
    (measurableEmbedding_p48oRot θ) d ((p48oRot (-θ)) ⁻¹' A)
  rw [hpre] at h
  exact h.symm

/-- Vague limits on `ℂ` are transported by a rotation. -/
lemma p48o_isVagueLimitC_map_rot {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hv : IsVagueLimitC μs μ) (θ : ℝ) :
    IsVagueLimitC (fun k => (μs k).map (p48oRot θ)) (μ.map (p48oRot θ)) := by
  refine ⟨fun K hK => ?_, fun f hf hfs => ?_⟩
  · rw [Measure.map_apply (measurable_p48oRot θ) hK.isClosed.measurableSet]
    have hK' : IsCompact ((p48oRot θ) ⁻¹' K) := by
      have := hK.image (p48oRot (-θ)).continuous
      convert this using 1
      ext z
      simp only [mem_preimage, mem_image]
      constructor
      · intro hz
        exact ⟨p48oRot θ z, hz, p48oRot_neg_apply_rot θ z⟩
      · rintro ⟨w, hw, rfl⟩
        rwa [p48oRot_apply_rot_neg]
    exact hv.1 _ hK'
  · have hcomp : Continuous fun z => f (p48oRot θ z) := hf.comp (p48oRot θ).continuous
    have hcs : HasCompactSupport fun z => f (p48oRot θ z) :=
      hfs.comp_homeomorph (p48oRot θ).toHomeomorph
    have hmeas : AEStronglyMeasurable f (μ.map (p48oRot θ)) :=
      hf.aestronglyMeasurable
    have hlim := hv.2 _ hcomp hcs
    have e1 : ∀ k, ∫ z, f z ∂((μs k).map (p48oRot θ)) = ∫ z, f (p48oRot θ z) ∂(μs k) := by
      intro k
      rw [integral_map (measurable_p48oRot θ).aemeasurable hf.aestronglyMeasurable]
    have e2 : ∫ z, f z ∂(μ.map (p48oRot θ)) = ∫ z, f (p48oRot θ z) ∂μ := by
      rw [integral_map (measurable_p48oRot θ).aemeasurable hmeas]
    simp only [e1, e2]
    exact hlim

/-- **Dyadic GMC approximations under rotated circle averages.** -/
lemma p48o_lqgAreaApprox_eq_map_rot {γ : ℝ} {h h' : DistC} (θ : ℝ) (k : ℕ)
    (hcov : ∀ᵐ z : ℂ, circleAvg h' (dyadicScale k) z =
      circleAvg h (dyadicScale k) (p48oRot θ z)) :
    lqgAreaApprox γ h' k = (lqgAreaApprox γ h k).map (p48oRot (-θ)) := by
  rw [lqgAreaApprox, lqgAreaApprox, p48o_map_withDensity_rot]
  apply withDensity_congr_ae
  filter_upwards [hcov] with z hz
  rw [hz]

/-- **Vague limits of the rotated field.** -/
theorem p48o_isVagueLimitC_rot {γ : ℝ} {h h' : DistC} {μ : Measure ℂ} (θ : ℝ)
    (hcov : ∀ k : ℕ, ∀ᵐ z : ℂ, circleAvg h' (dyadicScale k) z =
      circleAvg h (dyadicScale k) (p48oRot θ z))
    (hv : IsVagueLimitC (lqgAreaApprox γ h) μ) :
    IsVagueLimitC (lqgAreaApprox γ h') (μ.map (p48oRot (-θ))) := by
  have e : lqgAreaApprox γ h' = fun k => (lqgAreaApprox γ h k).map (p48oRot (-θ)) := by
    funext k
    exact p48o_lqgAreaApprox_eq_map_rot θ k (hcov k)
  rw [e]
  exact p48o_isVagueLimitC_map_rot hv (-θ)

/-- The rotated Lebesgue curve `t ↦ e^{-iθ} c(t)`. -/
def p48oRotCurve (θ : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => p48oRot θ (c t), (p48oRot θ).continuous.comp c.continuous⟩

lemma p48oRotCurve_apply (θ : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    p48oRotCurve θ c t = Complex.exp (θ * Complex.I) * c t := by
  simp [p48oRotCurve]

lemma image_p48oRotCurve (θ : ℝ) (c : C(ℝ, ℂ)) (S : Set ℝ) :
    p48oRotCurve θ c '' S = p48oRot θ '' (c '' S) := by
  rw [image_image]
  rfl

/-- **The area clock is unchanged** when field and Lebesgue curve are rotated together. -/
theorem p48o_clock_rot {γ : ℝ} {h h' : DistC} {μ : Measure ℂ} (θ : ℝ)
    (hv : IsVagueLimitC (lqgAreaApprox γ h) μ)
    (hv' : IsVagueLimitC (lqgAreaApprox γ h') (μ.map (p48oRot (-θ))))
    (c : C(ℝ, ℂ)) (q : ℝ) :
    JointScalingO.clock γ h' (p48oRotCurve (-θ) c) q = JointScalingO.clock γ h c q := by
  have hseg : JointScalingO.areaSeg γ h' (p48oRotCurve (-θ) c) q =
      JointScalingO.areaSeg γ h c q := by
    rw [JointScalingO.areaSeg_eq γ hv' _ q, JointScalingO.areaSeg_eq γ hv c q,
      image_p48oRotCurve]
    have hcK : IsCompact (c '' uIcc 0 q) := isCompact_uIcc.image c.continuous
    have hK : IsCompact (p48oRot (-θ) '' (c '' uIcc 0 q)) :=
      hcK.image (p48oRot (-θ)).continuous
    rw [Measure.map_apply (measurable_p48oRot (-θ)) hK.isClosed.measurableSet,
      (p48oRot (-θ)).injective.preimage_image]
  unfold JointScalingO.clock
  rw [hseg]

/-- **Rotation covariance of the area-parametrized evaluation.** -/
theorem p48o_parEval_rot {γ : ℝ} {h h' : DistC} {μ : Measure ℂ} (θ : ℝ)
    (hv : IsVagueLimitC (lqgAreaApprox γ h) μ)
    (hv' : IsVagueLimitC (lqgAreaApprox γ h') (μ.map (p48oRot (-θ))))
    (c : C(ℝ, ℂ)) (t : ℝ) :
    JointScalingO.parEval γ h' (p48oRotCurve (-θ) c) t =
      p48oRot (-θ) (JointScalingO.parEval γ h c t) := by
  have htime : JointScalingO.timeOf γ h' (p48oRotCurve (-θ) c) t =
      JointScalingO.timeOf γ h c t := by
    unfold JointScalingO.timeOf
    simp only [p48o_clock_rot θ hv hv' c]
  rw [JointScalingO.parEval, JointScalingO.parEval, htime]
  rfl

end MatedCRTHarmonic.GMS4O
