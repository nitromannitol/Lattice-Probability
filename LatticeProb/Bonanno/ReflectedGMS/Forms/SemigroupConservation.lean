/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupConservation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.RealSemigroup
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Conservation of constants for summable speed

When the total atomic speed is finite, constant functions belong to the actual
weighted vertex `L²` space. Their full network energy vanishes, so the weak
resolvent uniqueness theorem makes their weighted representatives fixed points
of the actual full-form resolvent. The checked continuous functional calculus
then preserves this eigenvector at spectral value one.

The summability assumption is essential here: no claim is made that a nonzero
constant belongs to `L²(m)` when the total speed is infinite.
-/

set_option autoImplicit false

open scoped ENNReal InnerProductSpace NNReal

namespace ReflectedGMS.FullNetworkForm

open ComplexSequenceSpace SemigroupMultiplier

variable {V : Type*}

/-- A constant vertex function belongs to weighted `L²` when the speed is summable. -/
theorem hasSpeedL2_const {m : V → ℝ} (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (a : ℝ) :
    HasSpeedL2 m (fun _ : V ↦ a) := by
  apply memℓp_gen
  refine (hmsum.mul_left (a ^ 2)).congr fun v => ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  conv_rhs => rw [mul_pow]
  rw [Real.sq_sqrt (hm v).le, sq_abs]
  ring

/-- The actual one-resolvent fixes the weighted representative of every constant. -/
theorem oneResolvent_weightedValue_const_fixed (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (hmsum : Summable m) (a : ℝ) :
    oneResolvent G m (weightedValue m (fun _ : V ↦ a) (hasSpeedL2_const hm hmsum a)) =
      weightedValue m (fun _ : V ↦ a) (hasSpeedL2_const hm hmsum a) := by
  let hL2 := hasSpeedL2_const hm hmsum a
  let hE : G.HasFiniteEnergy (fun _ : V ↦ a) := G.hasFiniteEnergy_const a
  let u := inHilbertDomain G m hm (fun _ : V ↦ a) hL2 hE
  have hu : u = oneResolventLift G m (weightedValue m (fun _ : V ↦ a) hL2) := by
    apply oneResolventLift_unique G m
    intro v
    simp only [u, valueInclusion_inHilbertDomain, gradientInclusion_inHilbertDomain]
    have hgrad : weightedGradient G (fun _ : V ↦ a) hE = 0 := by
      apply lp.ext
      funext p
      simp [weightedGradient, weightedGradientCoord]
    rw [hgrad]
    simp
  change valueInclusion G m (oneResolventLift G m
      (weightedValue m (fun _ : V ↦ a) (hasSpeedL2_const hm hmsum a))) = _
  rw [← hu]
  rfl

/-- Continuous functional calculus preserves an eigenvector with eigenvalue one. -/
private theorem cfc_apply_of_apply_eq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (u : H) (hu : R u = u)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) (hf1 : f 1 = 1) :
    cfc f R u = u := by
  by_cases hu0 : u = 0
  · simp [hu0]
  have heigvec : Module.End.HasEigenvector (R : Module.End ℂ H) (1 : ℂ) u := by
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, hu0⟩
    simpa using hu
  have hspecC : (1 : ℂ) ∈ spectrum ℂ R := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector heigvec).mem_spectrum
  have hspec : (1 : ℝ) ∈ spectrum ℝ R := by
    exact hR.coe_mem_spectrum_complex.mp (by simpa using hspecC)
  rw [cfc_apply f R hR hf]
  let x : spectrum ℝ R := ⟨1, hspec⟩
  have hind (g : C(spectrum ℝ R, ℝ)) :
      cfcHom hR g u = (g x : ℂ) • u := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
        rw [show ContinuousMap.const (spectrum ℝ R) r =
          algebraMap ℝ C(spectrum ℝ R, ℝ) r by rfl]
        rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
        simp
    | id =>
        rw [cfcHom_id]
        simpa [x] using hu
    | star_id =>
        rw [map_star, cfcHom_id, hR.star_eq]
        simpa [x] using hu
    | add g h hg hh => simp only [map_add, ContinuousLinearMap.add_apply, hg, hh,
        ContinuousMap.add_apply, Complex.ofReal_add, add_smul]
    | mul g h hg hh =>
        simp only [map_mul, ContinuousLinearMap.mul_apply, hh, map_smul, hg,
          ContinuousMap.mul_apply, Complex.ofReal_mul]
        rw [smul_smul]
        exact congrArg (fun z : ℂ => z • u)
          (mul_comm (h x : ℂ) (g x : ℂ))
    | frequently g hg =>
        let S : Set C(spectrum ℝ R, ℝ) :=
          {h | cfcHom hR h u = (h x : ℂ) • u}
        have hclosed : IsClosed S := by
          dsimp only [S]
          exact isClosed_eq
            ((ContinuousLinearMap.apply ℂ H u).continuous.comp (cfcHom_continuous hR))
            ((Complex.ofRealCLM.continuous.comp (ContinuousMap.evalCLM ℝ x).continuous).smul
              continuous_const)
        change g ∈ S
        rw [← hclosed.closure_eq]
        exact mem_closure_of_frequently_of_tendsto hg continuousAt_id
  have hfinal := hind
    ⟨(spectrum ℝ R).domRestrict f, hf.domRestrict⟩
  change cfcHom hR ⟨(spectrum ℝ R).domRestrict f, hf.domRestrict⟩ u =
    ((f 1 : ℝ) : ℂ) • u at hfinal
  simpa only [hf1, Complex.ofReal_one, one_smul] using hfinal

/-- The actual full-form semigroup conserves every weighted constant at all times. -/
theorem fullFormSemigroup_weightedValue_const_fixed
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (a : ℝ) (t : ℝ≥0) :
    fullFormSemigroup G m t
        (weightedValue m (fun _ : V ↦ a) (hasSpeedL2_const hm hmsum a)) =
      weightedValue m (fun _ : V ↦ a) (hasSpeedL2_const hm hmsum a) := by
  let u := weightedValue m (fun _ : V ↦ a) (hasSpeedL2_const hm hmsum a)
  have hRu : complexOneResolvent G m (ofReal V u) = ofReal V u := by
    rw [complexOneResolvent_ofReal, oneResolvent_weightedValue_const_fixed G m hm hmsum a]
  have hk1 : k t 1 = 1 := by
    by_cases ht : t = 0
    · simp [ht]
    rw [k_eq_exp (pos_iff_ne_zero.2 ht) zero_lt_one]
    simp
  have hcfc : fullFormSemigroupComplex G m t (ofReal V u) = ofReal V u := by
    exact cfc_apply_of_apply_eq_one (complexOneResolvent G m)
      (complexOneResolvent_isSelfAdjoint G m) (ofReal V u) hRu (k t)
      (continuous_k t).continuousOn hk1
  rw [fullFormSemigroupComplex_ofReal] at hcfc
  exact ofReal_injective V hcfc

end ReflectedGMS.FullNetworkForm
