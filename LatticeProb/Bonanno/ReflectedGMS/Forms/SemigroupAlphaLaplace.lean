/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupAlphaLaplace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.RealSemigroup
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpectralSemigroup
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LatticeProb.Bonanno.ReflectedGMS.Forms.EulerResolvent

/-! The actual full-form semigroup has the correct Laplace transform at every
positive discount rate. Reuse the existing CFC integral theorem and the checked
Euler multiplier identification of the parameterized resolvent. -/

-- Merged from `ReflectedGMS/Forms/SemigroupLaplace.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_SemigroupLaplace

/-!
# The Laplace transform recovers the full-form resolvent

Reuse: mathlib's `cfc_setIntegral` and `integrableOn_cfc` interchange the
continuous functional calculus and a genuinely integrable Bochner integral.
The only scalar adapter needed is the discounted multiplier's expression as
`expNegInvGlue (x / t)`. Joint continuity is used only for positive times.
No operator-norm continuity at zero or association with a process is assumed.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace ReflectedGMS.SemigroupMultiplier

theorem exp_neg_mul_k_eq_glue {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.exp (-t) * k (Real.toNNReal t) x = expNegInvGlue (x / t) := by
  have ht0 : Real.toNNReal t ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr ht)
  rw [k, ite_eq_right ht0, Real.coe_toNNReal t ht.le, ← mul_assoc, ← Real.exp_add]
  simp

/-- Discounting removes the growing exponential prefactor at positive times. -/
theorem continuousOn_exp_neg_mul_k (s : Set ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Real.exp (-p.1) * k (Real.toNNReal p.1) p.2)
      (Ioi 0 ×ˢ s) := by
  have hg : Continuous expNegInvGlue :=
    (expNegInvGlue.contDiff (n := (⊤ : ℕ∞))).continuous
  have hd : ContinuousOn (fun p : ℝ × ℝ => p.2 / p.1) (Ioi 0 ×ˢ s) :=
    continuous_snd.continuousOn.div continuous_fst.continuousOn
      (fun p hp => ne_of_gt hp.1)
  exact (hg.comp_continuousOn hd).congr fun p hp => exp_neg_mul_k_eq_glue hp.1 p.2

private theorem exp_neg_mul_k_eq_exp {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    Real.exp (-t) * k (Real.toNNReal t) x = Real.exp (-(x⁻¹) * t) := by
  rw [k_eq_exp (Real.toNNReal_pos.mpr ht) hx, Real.coe_toNNReal t ht.le,
    ← Real.exp_add]
  congr 1
  simp only [one_div]
  ring

end ReflectedGMS.SemigroupMultiplier

namespace ReflectedGMS.FullNetworkForm

open SemigroupMultiplier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem exp_neg_mul_k_bound (R : H →L[ℂ] H)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ) :
    ∀ x ∈ spectrum ℝ R, ‖Real.exp (-t) * k (Real.toNNReal t) x‖ ≤ Real.exp (-t) := by
  intro x hx
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (k_nonneg _ _)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (k_le_one (t := Real.toNNReal t) (hspec hx).1 (hspec hx).2)
      (Real.exp_nonneg (-t))

end ReflectedGMS.FullNetworkForm

end Merged_SemigroupLaplace

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace ReflectedGMS.SemigroupMultiplier

theorem continuousOn_exp_neg_alpha_mul_k (alpha : ℝ) (s : Set ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-alpha * p.1) * k (Real.toNNReal p.1) p.2) (Ioi 0 ×ˢ s) := by
  have he : Continuous (fun p : ℝ × ℝ => Real.exp ((1 - alpha) * p.1)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_fst)
  apply (he.continuousOn.mul (continuousOn_exp_neg_mul_k s)).congr
  intro p _
  change Real.exp (-alpha * p.1) * k (Real.toNNReal p.1) p.2 =
    Real.exp ((1 - alpha) * p.1) * (Real.exp (-p.1) * k (Real.toNNReal p.1) p.2)
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integral_exp_neg_alpha_mul_k {alpha : ℝ} (ha : 0 < alpha)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) * k (Real.toNNReal t) x) =
      (1 / alpha) * eulerStep (1 / alpha) x := by
  rcases hx.1.eq_or_lt with rfl | hx0
  · rw [show eulerStep (1 / alpha) 0 = 0 by simp [eulerStep], mul_zero]
    apply integral_eq_zero_of_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      change Real.exp (-alpha * t) * k (Real.toNNReal t) 0 = 0
      simp [k, (Real.toNNReal_pos.mpr ht).ne']
  · have hinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).2 hx.2
    have hr : 0 < alpha + x⁻¹ - 1 := by linarith
    have he (t : ℝ) (ht : 0 < t) :
        Real.exp (-alpha * t) * k (Real.toNNReal t) x =
          Real.exp (-(alpha + x⁻¹ - 1) * t) := by
      rw [k_eq_exp (Real.toNNReal_pos.mpr ht) hx0, Real.coe_toNNReal t ht.le,
        ← Real.exp_add]
      congr 1
      simp only [one_div]
      ring
    calc
      _ = ∫ t : ℝ in Ioi 0, Real.exp (-(alpha + x⁻¹ - 1) * t) := by
        apply integral_congr_ae
        exact ae_restrict_of_forall_mem measurableSet_Ioi he
      _ = (alpha + x⁻¹ - 1)⁻¹ := by
        rw [integral_exp_mul_Ioi (neg_neg_of_pos hr)]
        simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
      _ = (1 / alpha) * eulerStep (1 / alpha) x := by
        rw [eulerStep_eq_inv _ hx0.ne']
        field_simp
        ring

end ReflectedGMS.SemigroupMultiplier

namespace ReflectedGMS.FullNetworkForm

open SemigroupMultiplier ComplexSequenceSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem exp_neg_alpha_mul_k_bound (R : H →L[ℂ] H)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (alpha t : ℝ) :
    ∀ x ∈ spectrum ℝ R,
      ‖Real.exp (-alpha * t) * k (Real.toNNReal t) x‖ ≤ Real.exp (-alpha * t) := by
  intro x hx
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (k_nonneg _ _)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (k_le_one (t := Real.toNNReal t) (hspec hx).1 (hspec hx).2)
      (Real.exp_nonneg (-alpha * t))

theorem integrableOn_exp_neg_alpha_smul_spectralSemigroup
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {alpha : ℝ} (ha : 0 < alpha) :
    IntegrableOn (fun t : ℝ => Real.exp (-alpha * t) •
      spectralSemigroup R (Real.toNNReal t)) (Ioi 0) := by
  have hi := integrableOn_cfc (μ := volume) measurableSet_Ioi
    (fun t x : ℝ => Real.exp (-alpha * t) * k (Real.toNNReal t) x)
    (fun t : ℝ => Real.exp (-alpha * t)) R
    (continuousOn_exp_neg_alpha_mul_k alpha (spectrum ℝ R))
    (Filter.Eventually.of_forall (exp_neg_alpha_mul_k_bound R hspec alpha))
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).hasFiniteIntegral hR
  simpa only [cfc_const_mul _ _ _ (continuous_k _).continuousOn, spectralSemigroup] using hi

theorem integral_exp_neg_alpha_smul_spectralSemigroup
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {alpha : ℝ} (ha : 0 < alpha) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) • spectralSemigroup R (Real.toNNReal t)) =
      (1 / alpha) • cfc (eulerStep (1 / alpha)) R := by
  have hi := cfc_setIntegral (μ := volume) measurableSet_Ioi
    (fun t x : ℝ => Real.exp (-alpha * t) * k (Real.toNNReal t) x)
    (fun t : ℝ => Real.exp (-alpha * t)) R
    (continuousOn_exp_neg_alpha_mul_k alpha (spectrum ℝ R))
    (Filter.Eventually.of_forall (exp_neg_alpha_mul_k_bound R hspec alpha))
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).hasFiniteIntegral hR
  have hid : cfc (fun x : ℝ => ∫ t : ℝ in Ioi 0,
      Real.exp (-alpha * t) * k (Real.toNNReal t) x) R =
        (1 / alpha) • cfc (eulerStep (1 / alpha)) R := by
    rw [cfc_congr (fun x hx => integral_exp_neg_alpha_mul_k ha (hspec hx)),
      cfc_const_mul _ _ _ ((continuousOn_eulerStep (one_div_pos.mpr ha)).mono hspec)]
  rw [hid] at hi
  simpa only [cfc_const_mul _ _ _ (continuous_k _).continuousOn, spectralSemigroup] using hi.symm

theorem integral_exp_neg_alpha_smul_fullFormSemigroupComplex {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) {alpha : ℝ} (ha : 0 < alpha) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) •
      fullFormSemigroupComplex G m (Real.toNNReal t)) =
        (1 / alpha) • complexify (parameterizedResolvent G m (1 / alpha)) := by
  rw [complexify_parameterizedResolvent_eq_cfc_eulerStep G m (one_div_pos.mpr ha)]
  exact integral_exp_neg_alpha_smul_spectralSemigroup (complexOneResolvent G m)
    (complexOneResolvent_isSelfAdjoint G m) (complexOneResolvent_spectrum_subset G m) ha

theorem integrableOn_exp_neg_alpha_smul_fullFormSemigroupComplex {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) {alpha : ℝ} (ha : 0 < alpha) :
    IntegrableOn (fun t : ℝ => Real.exp (-alpha * t) •
      fullFormSemigroupComplex G m (Real.toNNReal t)) (Ioi 0) :=
  integrableOn_exp_neg_alpha_smul_spectralSemigroup (complexOneResolvent G m)
    (complexOneResolvent_isSelfAdjoint G m) (complexOneResolvent_spectrum_subset G m) ha

private noncomputable def alphaOperatorComplexification {V : Type*} :
    (ValueSpace V →L[ℝ] ValueSpace V) →ₗᵢ[ℝ]
      (ComplexL2 V →L[ℂ] ComplexL2 V) where
  toLinearMap := (complexifyAlgHom (V := V)).toLinearMap
  norm_map' := complexify_norm

@[simp] private theorem alphaOperatorComplexification_apply {V : Type*}
    (T : ValueSpace V →L[ℝ] ValueSpace V) :
    alphaOperatorComplexification T = complexify T := rfl

theorem integrableOn_exp_neg_alpha_smul_fullFormSemigroup {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) {alpha : ℝ} (ha : 0 < alpha) :
    IntegrableOn (fun t : ℝ => Real.exp (-alpha * t) •
      fullFormSemigroup G m (Real.toNNReal t)) (Ioi 0) := by
  let C := alphaOperatorComplexification (V := V)
  have hC : IntegrableOn (fun t : ℝ => C (Real.exp (-alpha * t) •
      fullFormSemigroup G m (Real.toNNReal t))) (Ioi 0) := by
    simpa only [map_smul, C, alphaOperatorComplexification_apply,
      complexify_fullFormSemigroup] using
      integrableOn_exp_neg_alpha_smul_fullFormSemigroupComplex G m ha
  change Integrable (C ∘ fun t : ℝ => Real.exp (-alpha * t) •
    fullFormSemigroup G m (Real.toNNReal t)) (volume.restrict (Ioi 0)) at hC
  exact (C.isometry.lipschitzWith.integrable_comp_iff_of_antilipschitz
    C.isometry.antilipschitzWith C.map_zero).mp hC

/-- The positive-discount Laplace transform has exactly the occupation-resolvent
normalization: `(1/alpha) * (I + A/alpha)⁻¹`. -/
theorem integral_exp_neg_alpha_smul_fullFormSemigroup {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) {alpha : ℝ} (ha : 0 < alpha) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) •
      fullFormSemigroup G m (Real.toNNReal t)) =
        (1 / alpha) • parameterizedResolvent G m (1 / alpha) := by
  let C := alphaOperatorComplexification (V := V)
  apply C.injective
  calc
    C (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) •
        fullFormSemigroup G m (Real.toNNReal t)) =
        ∫ t : ℝ in Ioi 0, C (Real.exp (-alpha * t) •
          fullFormSemigroup G m (Real.toNNReal t)) :=
      (C.toContinuousLinearMap.integral_comp_comm
        (integrableOn_exp_neg_alpha_smul_fullFormSemigroup G m ha)).symm
    _ = (1 / alpha) • complexify (parameterizedResolvent G m (1 / alpha)) := by
      simpa only [map_smul, C, alphaOperatorComplexification_apply,
        complexify_fullFormSemigroup] using
        integral_exp_neg_alpha_smul_fullFormSemigroupComplex G m ha
    _ = C ((1 / alpha) • parameterizedResolvent G m (1 / alpha)) := by
      rw [map_smul]
      rfl

theorem integral_exp_neg_alpha_smul_fullFormSemigroup_apply {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) {alpha : ℝ} (ha : 0 < alpha)
    (u : ValueSpace V) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) •
      fullFormSemigroup G m (Real.toNNReal t) u) =
        (1 / alpha) • parameterizedResolvent G m (1 / alpha) u := by
  calc
    _ = (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) •
        fullFormSemigroup G m (Real.toNNReal t)) u := by
      simpa only [smul_apply] using (ContinuousLinearMap.integral_apply
        (integrableOn_exp_neg_alpha_smul_fullFormSemigroup G m ha) u).symm
    _ = _ := by
      rw [integral_exp_neg_alpha_smul_fullFormSemigroup G m ha]
      rfl

end ReflectedGMS.FullNetworkForm
