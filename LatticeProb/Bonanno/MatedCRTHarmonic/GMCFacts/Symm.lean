/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.Symm at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF

/-!
# Radial symmetrization of test functions

For a test function `φ` on `ℂ`, its rotation average `φ̄(w) = (2π)⁻¹ ∫_0^{2π} φ(e^{iθ} w) dθ` (`rotSymm`) is again a
test function (`symmTest`), it is radial (`symmTest_radial`: `φ̄(w) = φ̄(|w|)`), and it has the same integral against
every radial locally integrable function (`integral_rotSymm_mul`). This is the projection of the proof of DMS Lemma
4.2–4.4 (the decomposition `H(ℂ) = H₁(ℂ) ⊕ H₂(ℂ)` into radial functions and functions with mean zero
on circles about `0`) used for the lateral part of a whole-plane GFF in `Replaced.lean`.

Ingredients (own elementary arguments): smoothness of parametric interval integrals of jointly smooth functions
(`contDiff_intervalIntegral_param`, induction with mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`), and the
invariance of Lebesgue measure on `ℂ` under multiplication by a unit complex number (`measurePreserving_mul_unit`:
the real determinant of `w ↦ a w` is `|a|²`, mathlib `Algebra.norm_complex_apply`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff Real

namespace MatedCRTHarmonic.GMCFacts

/-! ### Smoothness of parametric interval integrals -/

/-- **Smoothness of parametric interval integrals**: if `F : ℂ × ℝ → E` is smooth, then
`x ↦ ∫_a^b F(x, θ) dθ` is `C^n` for every `n`. -/
theorem contDiff_intervalIntegral_param (a b : ℝ) (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : ℂ × ℝ → E},
      ContDiff ℝ ∞ F → ContDiff ℝ n (fun x : ℂ => ∫ θ in a..b, F (x, θ)) := by
  induction n with
  | zero =>
    intro E _ _ _ F hF
    rw [Nat.cast_zero, contDiff_zero]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x θ => F (x, θ)) hF.continuous a b
  | succ n ih =>
    intro E _ _ _ F hF
    set G : ℂ × ℝ → (ℂ →L[ℝ] E) := fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)
    have hG : ContDiff ℝ ∞ G :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    have hderiv : ∀ x₀ : ℂ, HasFDerivAt (fun x : ℂ => ∫ θ in a..b, F (x, θ))
        (∫ θ in a..b, G (x₀, θ)) x₀ := by
      intro x₀
      obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn hG.continuous.continuousOn
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
        (ball_mem_nhds x₀ one_pos) (Eventually.of_forall fun x =>
          (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        ((hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
        (hG.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (ae_of_all _ fun θ hθ x hx => hC (x, θ) ⟨ball_subset_closedBall hx, uIoc_subset_uIcc hθ⟩)
        intervalIntegrable_const (ae_of_all _ fun θ _ x _ => ?_)
      have h1 : HasFDerivAt F (fderiv ℝ F (x, θ)) (x, θ) :=
        (hF.differentiable (by simp) _).hasFDerivAt
      have h2 : HasFDerivAt (fun y : ℂ => (y, θ)) (ContinuousLinearMap.inl ℝ ℂ ℝ) x :=
        (hasFDerivAt_id x).prodMk (hasFDerivAt_const θ x)
      exact h1.comp x h2
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun x₀ => ∫ θ in a..b, G (x₀, θ), ih hG, hderiv⟩

/-! ### Rotations of `ℂ` preserve Lebesgue measure -/

/-- Multiplication by a unit complex number preserves Lebesgue measure on `ℂ`. -/
theorem measurePreserving_mul_unit {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (fun w : ℂ => a * w) volume volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ a) = 1 := by
    have e : LinearMap.mulLeft ℝ a = Algebra.lmul ℝ ℂ a := rfl
    rw [e, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, ha, one_pow]
  refine ⟨by fun_prop, ?_⟩
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ))
    (f := LinearMap.mulLeft ℝ a) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at this
  exact this

/-- Rotation invariance of integrals on `ℂ`. -/
lemma integral_comp_mul_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℂ}
    (ha : ‖a‖ = 1) (f : ℂ → E) : ∫ w, f (a * w) = ∫ w, f w := by
  have ha0 : a ≠ 0 := by rw [← norm_ne_zero_iff, ha]; exact one_ne_zero
  exact (measurePreserving_mul_unit ha).integral_comp (Homeomorph.mulLeft₀ a ha0).measurableEmbedding f

/-! ### The rotation average -/

/-- The rotation average `(2π)⁻¹ ∫_0^{2π} φ(e^{iθ} w) dθ`. -/
def rotSymm (φ : ℂ → ℝ) (w : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, φ (Complex.exp (θ * Complex.I) * w)

lemma norm_exp_ofReal_mul_I' (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- `θ ↦ φ(e^{iθ} w)` is `2π`-periodic. -/
lemma periodic_rot (φ : ℂ → ℝ) (w : ℂ) :
    Function.Periodic (fun θ : ℝ => φ (Complex.exp (θ * Complex.I) * w)) (2 * π) := by
  intro θ
  simp only
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The rotation average is rotation invariant. -/
lemma rotSymm_exp_mul (φ : ℂ → ℝ) (α : ℝ) (w : ℂ) :
    rotSymm φ (Complex.exp (α * Complex.I) * w) = rotSymm φ w := by
  unfold rotSymm
  congr 1
  set g : ℝ → ℝ := fun θ => φ (Complex.exp (θ * Complex.I) * w)
  have e : (fun θ : ℝ => φ (Complex.exp (θ * Complex.I) * (Complex.exp (α * Complex.I) * w))) =
      fun θ => g (θ + α) := by
    funext θ
    simp only [g, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [e, intervalIntegral.integral_comp_add_right g α, zero_add,
    show 2 * π + α = α + 2 * π by ring, (periodic_rot φ w).intervalIntegral_add_eq α 0, zero_add]

/-- The rotation average is radial. -/
lemma rotSymm_radial (φ : ℂ → ℝ) (w : ℂ) : rotSymm φ w = rotSymm φ ((‖w‖ : ℝ) : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w, mul_comm]
  exact rotSymm_exp_mul φ (Complex.arg w) _

/-- A function on `ℂ` invariant under all rotations. -/
def IsRotInv (u : ℂ → ℝ) : Prop := ∀ (α : ℝ) (w : ℂ), u (Complex.exp (α * Complex.I) * w) = u w

/-- **The rotation average has the same integral against every rotation-invariant locally integrable function.** -/
theorem integral_rotSymm_mul {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {u : ℂ → ℝ} (hu : IsRotInv u) (hloc : LocallyIntegrable u volume) :
    ∫ w, rotSymm φ w * u w = ∫ w, φ w * u w := by
  obtain ⟨R, hR⟩ := hφs.isCompact.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hφs
  have hφ0 : ∀ w, R < ‖w‖ → φ w = 0 := fun w hw =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  set F : ℝ × ℂ → ℝ := fun p => φ (Complex.exp (p.1 * Complex.I) * p.2) * u p.2
  have hcont : Continuous fun p : ℝ × ℂ => φ (Complex.exp (p.1 * Complex.I) * p.2) :=
    hφc.comp (by fun_prop)
  have huR : IntegrableOn u (closedBall 0 R) volume := hloc.integrableOn_isCompact (isCompact_closedBall 0 R)
  -- integrability on `(0, 2π] × ℂ`
  have hFint : Integrable F ((volume.restrict (Ioc 0 (2 * π))).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => M * (closedBall (0 : ℂ) R).indicator (fun w => ‖u w‖) p.2)
        ((volume.restrict (Ioc 0 (2 * π))).prod volume) :=
      (((integrable_indicator_iff measurableSet_closedBall).2 huR.norm).const_mul M).comp_snd _
    refine hg.mono' (hcont.aestronglyMeasurable.mul
      (hloc.aestronglyMeasurable.aemeasurable.comp_snd).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    simp only [F, norm_mul]
    by_cases hp : p.2 ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem hp]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [indicator_of_notMem hp, mul_zero]
      rw [mem_closedBall, dist_zero_right, not_le] at hp
      rw [hφ0 _ (by rw [norm_mul, norm_exp_ofReal_mul_I', one_mul]; exact hp), norm_zero, zero_mul]
  have hinner : ∀ θ : ℝ, ∫ w, F (θ, w) = ∫ w, φ w * u w := by
    intro θ
    have h1 := integral_comp_mul_unit (norm_exp_ofReal_mul_I' (-θ)) (fun w => F (θ, w))
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [F, ← mul_assoc, ← Complex.exp_add]
    rw [hu]
    congr 2
    push_cast
    ring_nf
    simp
  calc ∫ w, rotSymm φ w * u w
      = ∫ w, (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), F (θ, w) := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [rotSymm, F]
        rw [mul_assoc, ← intervalIntegral.integral_mul_const,
          intervalIntegral.integral_of_le (by positivity)]
    _ = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ∫ w, F (θ, w) := by
        rw [integral_const_mul, integral_integral_swap (f := fun (w : ℂ) (θ : ℝ) => F (θ, w)) hFint.swap]
    _ = ∫ w, φ w * u w := by
        simp_rw [hinner]
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), sub_zero, smul_eq_mul,
          ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ### Symmetrized test functions -/

/-- The rotation average of a test function is a test function. -/
def symmTest (φ : LQGMetric.TestC) : LQGMetric.TestC where
  toFun := rotSymm φ
  contDiff' := by
    have hof : ContDiff ℝ ∞ (fun p : ℂ × ℝ => ((p.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_snd
    have hexp : ContDiff ℝ ∞ (fun p : ℂ × ℝ => Complex.exp (p.2 * Complex.I)) :=
      ((Complex.contDiff_exp (n := ∞)).restrict_scalars (𝕜 := ℝ) (𝕜' := ℂ)).comp
        (hof.mul contDiff_const)
    have hF : ContDiff ℝ ∞ (fun p : ℂ × ℝ => φ (Complex.exp (p.2 * Complex.I) * p.1)) :=
      φ.contDiff.comp (hexp.mul contDiff_fst)
    refine contDiff_infty.2 fun n => ?_
    exact contDiff_const.mul (contDiff_intervalIntegral_param 0 (2 * π) n hF)
  hasCompactSupport' := by
    obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun w hw => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hw
    simp only [rotSymm]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun θ _ => ?_),
      intervalIntegral.integral_zero, mul_zero]
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hR h
    rw [mem_closedBall, dist_zero_right, norm_mul, norm_exp_ofReal_mul_I', one_mul] at this
    linarith
  tsupport_subset' := subset_univ _

@[simp] lemma symmTest_apply (φ : LQGMetric.TestC) (w : ℂ) : symmTest φ w = rotSymm φ w := rfl

/-- `symmTest φ` is radial about `0`. -/
lemma symmTest_radial (φ : LQGMetric.TestC) (w : ℂ) : symmTest φ w = symmTest φ ((‖w‖ : ℝ) : ℂ) :=
  rotSymm_radial φ w

/-- `∫ φ̄ u = ∫ φ u` for rotation-invariant locally integrable `u`. -/
lemma integral_symmTest_mul (φ : LQGMetric.TestC) {u : ℂ → ℝ} (hu : IsRotInv u)
    (hloc : LocallyIntegrable u volume) : ∫ w, symmTest φ w * u w = ∫ w, φ w * u w :=
  integral_rotSymm_mul φ.continuous φ.hasCompactSupport hu hloc

/-- `∫ φ̄ = ∫ φ`. -/
lemma integral_symmTest (φ : LQGMetric.TestC) : ∫ w, symmTest φ w = ∫ w, φ w := by
  have := integral_symmTest_mul φ (u := fun _ => 1) (fun _ _ => rfl) (locallyIntegrable_const 1)
  simpa only [mul_one] using this

/-- `φ − φ̄` has integral zero. -/
lemma integral_sub_symmTest (φ : LQGMetric.TestC) : ∫ w, (φ - symmTest φ) w = 0 := by
  have h1 : Integrable (⇑φ) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have h2 : Integrable (⇑(symmTest φ)) :=
    (symmTest φ).continuous.integrable_of_hasCompactSupport (symmTest φ).hasCompactSupport
  simp only [LQGMetric.TestC] at *
  rw [show (fun w => (φ - symmTest φ) w) = fun w => φ w - symmTest φ w from rfl,
    integral_sub h1 h2, integral_symmTest, sub_self]

end MatedCRTHarmonic.GMCFacts
