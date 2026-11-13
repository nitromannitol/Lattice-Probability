/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexPotentialDynkin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexResolventExcessive
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedSemigroupAction
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupAlphaLaplace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The ordinary Dynkin identity for vertex potentials

The positive-discount vertex potential is in the range of the full-form
resolvent.  On that range the spectral multiplier is differentiable, including
at the zero spectral endpoint after multiplication by the resolvent.  Integrating
this exact scalar identity gives the ordinary (undiscounted) Dynkin formula.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace ReflectedGMS.SemigroupMultiplier

/-- The scalar multiplier of the positive-discount occupation resolvent. -/
noncomputable def occupationResolventMultiplier (alpha x : ℝ) : ℝ :=
  (1 / alpha) * eulerStep (1 / alpha) x

private theorem occupationResolventMultiplier_eq_inv
    {alpha x : ℝ} (ha : 0 < alpha) (hx : 0 < x) :
    occupationResolventMultiplier alpha x = (alpha + x⁻¹ - 1)⁻¹ := by
  rw [occupationResolventMultiplier, eulerStep_eq_inv _ hx.ne']
  field_simp [ha.ne']
  ring

/-- The scalar fundamental theorem underlying the Dynkin identity. -/
theorem integral_k_mul_occupationResolventGenerator
    {alpha : ℝ} (ha : 0 < alpha) (t : ℝ≥0) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        k (Real.toNNReal s) x *
          (alpha * occupationResolventMultiplier alpha x - 1)) =
      k t x * occupationResolventMultiplier alpha x -
        occupationResolventMultiplier alpha x := by
  rcases hx.1.eq_or_lt with rfl | hx0
  · have hk : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (t : ℝ)),
        k (Real.toNNReal s) 0 = 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hspos : 0 < s := hs.1
      simp [k, (Real.toNNReal_pos.mpr hspos).ne', expNegInvGlue.zero]
    rw [occupationResolventMultiplier, eulerStep]
    simp only [zero_div, mul_zero, sub_zero]
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    apply integral_eq_zero_of_ae
    filter_upwards [hk] with s hs
    simp [hs]
  · have hq := occupationResolventMultiplier_eq_inv ha hx0
    let c : ℝ := 1 - x⁻¹
    let q : ℝ := occupationResolventMultiplier alpha x
    have hden : alpha + x⁻¹ - 1 ≠ 0 := by
      have hinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).2 hx.2
      linarith
    have hgen : alpha * q - 1 = c * q := by
      have hdq : (alpha + x⁻¹ - 1) * q = 1 := by
        dsimp only [q]
        rw [hq]
        exact mul_inv_cancel₀ hden
      calc
        alpha * q - 1 = alpha * q - (alpha + x⁻¹ - 1) * q := by rw [hdq]
        _ = c * q := by dsimp only [c]; ring
    have hderiv (s : ℝ) : HasDerivAt (fun r : ℝ ↦ Real.exp (c * r) * q)
        (Real.exp (c * s) * (c * q)) s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((Real.hasDerivAt_exp (c * s)).comp s
          ((hasDerivAt_id s).const_mul c)).mul_const q
    have hint : IntervalIntegrable
        (fun s : ℝ ↦ Real.exp (c * s) * (c * q)) volume 0 (t : ℝ) :=
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul continuous_const).intervalIntegrable _ _
    calc
      (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          k (Real.toNNReal s) x * (alpha * q - 1)) =
          ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
            Real.exp (c * s) * (c * q) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) (t : ℝ) := by
          simpa [uIcc_of_le t.coe_nonneg] using hs
        rw [hgen]
        by_cases hs0 : s = 0
        · subst s
          simp [c]
        · have hspos : 0 < s := lt_of_le_of_ne hs'.1 (Ne.symm hs0)
          change k (Real.toNNReal s) x * (c * q) = _
          rw [k_eq_exp (Real.toNNReal_pos.mpr hspos) hx0,
            Real.coe_toNNReal s hspos.le]
          simp only
          congr 2
          dsimp only [c]
          ring
      _ = Real.exp (c * (t : ℝ)) * q - Real.exp (c * 0) * q :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s) hint
      _ = k t x * q - q := by
        by_cases ht : t = 0
        · simp [ht]
        · have hexp : Real.exp (c * (t : ℝ)) = k t x := by
            rw [k_eq_exp (pos_iff_ne_zero.2 ht) hx0]
            congr 1
            dsimp only [c]
            ring
          rw [hexp]
          simp

end ReflectedGMS.SemigroupMultiplier

namespace ReflectedGMS.FullNetworkForm

open SemigroupMultiplier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Match the real scalar structure used by the real functional calculus.
noncomputable local instance : SMul ℝ (H →L[ℂ] H) :=
  ⟨fun r T => (r : ℂ) • T⟩
noncomputable local instance : NormedSpace ℝ (H →L[ℂ] H) := NormedSpace.complexToReal
noncomputable local instance : Algebra ℝ (H →L[ℂ] H) := Algebra.complexToReal
noncomputable local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.complexToReal

private theorem continuousOn_k_mul_occupationGenerator
    {alpha : ℝ} (ha : 0 < alpha) (t : ℝ≥0) (s : Set ℝ)
    (hs : s ⊆ Icc (0 : ℝ) 1) :
    ContinuousOn (Function.uncurry (fun r x : ℝ ↦
      k (Real.toNNReal r) x *
        (alpha * occupationResolventMultiplier alpha x - 1)))
      (Ioc (0 : ℝ) (t : ℝ) ×ˢ s) := by
  have hkdisc := continuousOn_exp_neg_mul_k s
  have hk : ContinuousOn (fun p : ℝ × ℝ ↦ k (Real.toNNReal p.1) p.2)
      (Ioc (0 : ℝ) (t : ℝ) ×ˢ s) := by
    have hkdisc' : ContinuousOn
      (fun p : ℝ × ℝ ↦ Real.exp (-p.1) * k (Real.toNNReal p.1) p.2)
        (Ioc (0 : ℝ) (t : ℝ) ×ˢ s) :=
      hkdisc.mono (prod_mono (fun _ h ↦ h.1) Subset.rfl)
    have hprod : ContinuousOn (fun p : ℝ × ℝ ↦
        Real.exp p.1 * (Real.exp (-p.1) * k (Real.toNNReal p.1) p.2))
        (Ioc (0 : ℝ) (t : ℝ) ×ˢ s) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦ Real.exp p.1).continuousOn.mul hkdisc'
    apply hprod.congr
    intro p hp
    change k (Real.toNNReal p.1) p.2 =
      Real.exp p.1 * (Real.exp (-p.1) * k (Real.toNNReal p.1) p.2)
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hq : ContinuousOn (occupationResolventMultiplier alpha) s := by
    unfold occupationResolventMultiplier
    exact continuousOn_const.mul
      ((continuousOn_eulerStep (one_div_pos.mpr ha)).mono hs)
  exact hk.mul ((continuousOn_const.mul
    (hq.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2))).sub continuousOn_const)

theorem integrableOn_spectralSemigroup_occupationGenerator
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {alpha : ℝ} (ha : 0 < alpha) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ ↦
      spectralSemigroup R (Real.toNNReal s) *
        (alpha • cfc (occupationResolventMultiplier alpha) R - 1))
      (Ioc (0 : ℝ) (t : ℝ)) := by
  let q : ℝ → ℝ := occupationResolventMultiplier alpha
  let f : ℝ → ℝ → ℝ := fun s x ↦
    k (Real.toNNReal s) x * (alpha * q x - 1)
  have hfcont : ContinuousOn (Function.uncurry f)
      (Ioc (0 : ℝ) (t : ℝ) ×ˢ spectrum ℝ R) := by
    simpa only [f, q] using
      continuousOn_k_mul_occupationGenerator ha t (spectrum ℝ R) hspec
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (t : ℝ)),
      ∀ x ∈ spectrum ℝ R, ‖f s x‖ ≤ 1 := by
    filter_upwards [] with s
    intro x hx
    have hx' := hspec hx
    have hk0 := k_nonneg (Real.toNNReal s) x
    have hk1 := k_le_one (t := Real.toNNReal s) hx'.1 hx'.2
    have he := eulerStep_mem_Icc (one_div_pos.mpr ha) hx'
    have hscale : alpha * q x = eulerStep (1 / alpha) x := by
      dsimp only [q, occupationResolventMultiplier]
      field_simp [ha.ne']
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0, hscale,
      abs_of_nonpos (sub_nonpos.mpr he.2)]
    calc
      k (Real.toNNReal s) x * -(eulerStep (1 / alpha) x - 1) =
          k (Real.toNNReal s) x * (1 - eulerStep (1 / alpha) x) := by ring
      _ ≤ 1 * (1 - eulerStep (1 / alpha) x) :=
        mul_le_mul_of_nonneg_right hk1 (sub_nonneg.mpr he.2)
      _ ≤ 1 := by linarith [he.1]
  have hfin : HasFiniteIntegral (fun _ : ℝ ↦ (1 : ℝ))
      (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) := by
    letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) :=
      Real.isFiniteMeasure_restrict_Ioc 0 (t : ℝ)
    exact hasFiniteIntegral_const 1
  have hi := integrableOn_cfc measurableSet_Ioc f (fun _ : ℝ ↦ (1 : ℝ))
    R hfcont hbound hfin hR
  have hqcont : ContinuousOn q (spectrum ℝ R) := by
    dsimp only [q, occupationResolventMultiplier]
    exact continuousOn_const.mul
      ((continuousOn_eulerStep (one_div_pos.mpr ha)).mono hspec)
  apply hi.congr
  filter_upwards [] with s
  have hkcont : ContinuousOn (k (Real.toNNReal s)) (spectrum ℝ R) :=
    (continuous_k (Real.toNNReal s)).continuousOn
  have hgcont : ContinuousOn (fun x ↦ alpha * q x - 1) (spectrum ℝ R) :=
    (continuousOn_const.mul hqcont).sub continuousOn_const
  rw [show f s = fun x ↦ k (Real.toNNReal s) x * (alpha * q x - 1) by rfl,
    cfc_mul _ _ R hkcont hgcont,
    cfc_sub (fun x ↦ alpha * q x) (fun _ : ℝ ↦ (1 : ℝ)) R
      (continuousOn_const.mul hqcont) continuousOn_const,
    cfc_const_mul _ _ R hqcont, cfc_const_one ℝ R hR]
  rfl

/-- Operator-valued Dynkin identity on the range of a positive resolvent. -/
theorem spectralSemigroup_occupationResolvent_dynkin
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {alpha : ℝ} (ha : 0 < alpha) (t : ℝ≥0) :
    spectralSemigroup R t * cfc (occupationResolventMultiplier alpha) R -
        cfc (occupationResolventMultiplier alpha) R =
      ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        spectralSemigroup R (Real.toNNReal s) *
          (alpha • cfc (occupationResolventMultiplier alpha) R - 1) := by
  let q : ℝ → ℝ := occupationResolventMultiplier alpha
  let f : ℝ → ℝ → ℝ := fun s x ↦
    k (Real.toNNReal s) x * (alpha * q x - 1)
  have hfcont : ContinuousOn (Function.uncurry f)
      (Ioc (0 : ℝ) (t : ℝ) ×ˢ spectrum ℝ R) := by
    simpa only [f, q] using
      continuousOn_k_mul_occupationGenerator ha t (spectrum ℝ R) hspec
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (t : ℝ)),
      ∀ x ∈ spectrum ℝ R, ‖f s x‖ ≤ 1 := by
    filter_upwards [] with s
    intro x hx
    have hx' := hspec hx
    have hk0 := k_nonneg (Real.toNNReal s) x
    have hk1 := k_le_one (t := Real.toNNReal s) hx'.1 hx'.2
    have he := eulerStep_mem_Icc (one_div_pos.mpr ha) hx'
    have hscale : alpha * q x = eulerStep (1 / alpha) x := by
      dsimp only [q, occupationResolventMultiplier]
      field_simp [ha.ne']
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0, hscale,
      abs_of_nonpos (sub_nonpos.mpr he.2)]
    calc
      k (Real.toNNReal s) x * -(eulerStep (1 / alpha) x - 1) =
          k (Real.toNNReal s) x * (1 - eulerStep (1 / alpha) x) := by ring
      _ ≤ 1 * (1 - eulerStep (1 / alpha) x) :=
        mul_le_mul_of_nonneg_right hk1 (sub_nonneg.mpr he.2)
      _ ≤ 1 := by linarith [he.1]
  have hfin : HasFiniteIntegral (fun _ : ℝ ↦ (1 : ℝ))
      (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) := by
    letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) :=
      Real.isFiniteMeasure_restrict_Ioc 0 (t : ℝ)
    exact hasFiniteIntegral_const 1
  have hi := cfc_setIntegral (μ := volume) measurableSet_Ioc f
    (fun _ : ℝ ↦ (1 : ℝ)) R hfcont hbound hfin hR
  have hqcont : ContinuousOn q (spectrum ℝ R) := by
    dsimp only [q, occupationResolventMultiplier]
    exact continuousOn_const.mul
      ((continuousOn_eulerStep (one_div_pos.mpr ha)).mono hspec)
  have hscalar (x : ℝ) (hx : x ∈ spectrum ℝ R) :
      (∫ s : ℝ in Ioc (0 : ℝ) (t : ℝ), f s x) = k t x * q x - q x := by
    rw [← intervalIntegral.integral_of_le t.coe_nonneg]
    exact integral_k_mul_occupationResolventGenerator ha t (hspec hx)
  rw [cfc_congr hscalar] at hi
  have hcfc_left : cfc (fun x : ℝ ↦ k t x * q x - q x) R =
      spectralSemigroup R t * cfc q R - cfc q R := by
    rw [cfc_sub (fun x ↦ k t x * q x) q R
      ((continuous_k t).continuousOn.mul hqcont) hqcont,
      cfc_mul (k t) q R (continuous_k t).continuousOn hqcont]
    rfl
  have hcfc_integrand (s : ℝ) : cfc (f s) R =
      spectralSemigroup R (Real.toNNReal s) * (alpha • cfc q R - 1) := by
    have hkcont : ContinuousOn (k (Real.toNNReal s)) (spectrum ℝ R) :=
      (continuous_k (Real.toNNReal s)).continuousOn
    have hgcont : ContinuousOn (fun x ↦ alpha * q x - 1) (spectrum ℝ R) :=
      (continuousOn_const.mul hqcont).sub continuousOn_const
    rw [show f s = fun x ↦ k (Real.toNNReal s) x * (alpha * q x - 1) by rfl,
      cfc_mul _ _ R hkcont hgcont,
      cfc_sub (fun x ↦ alpha * q x) (fun _ : ℝ ↦ (1 : ℝ)) R
        (continuousOn_const.mul hqcont) continuousOn_const,
      cfc_const_mul _ _ R hqcont, cfc_const_one ℝ R hR]
    rfl
  rw [hcfc_left] at hi
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  simpa only [hcfc_integrand] using hi

theorem cfc_occupationResolventMultiplier
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {alpha : ℝ} (ha : 0 < alpha) :
    cfc (occupationResolventMultiplier alpha) R =
      (1 / alpha) • cfc (eulerStep (1 / alpha)) R := by
  rw [show occupationResolventMultiplier alpha =
      fun x : ℝ ↦ (1 / alpha) * eulerStep (1 / alpha) x by rfl,
    cfc_const_mul (p := IsSelfAdjoint) _ _ R
      ((continuousOn_eulerStep (one_div_pos.mpr ha)).mono hspec)]

open ComplexSequenceSpace

variable {V : Type*}

/-- The full `L²(m)` vector represented by a vertex occupation potential. -/
noncomputable def vertexOccupationPotentialValue
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (alpha : ℝ) (y : V) : ValueSpace V :=
  (1 / alpha) • parameterizedResolvent G m (1 / alpha)
    (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))

@[simp] theorem unweight_vertexOccupationPotentialValue
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    unweight m (vertexOccupationPotentialValue G m alpha y) x =
      vertexOccupationPotential G m alpha x y := by
  rw [vertexOccupationPotential_eq_resolvent G m ha]
  change ((1 / alpha) *
      (parameterizedResolvent G m (1 / alpha)
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x) /
      Real.sqrt (m x) =
    (1 / alpha) *
      ((parameterizedResolvent G m (1 / alpha)
        (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x /
          Real.sqrt (m x))
  ring

private theorem cfc_occupationResolventMultiplier_eq_complexify
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {alpha : ℝ} (ha : 0 < alpha) :
    cfc (occupationResolventMultiplier alpha) (complexOneResolvent G m) =
      complexify ((1 / alpha) • parameterizedResolvent G m (1 / alpha)) := by
  have hcomplexify_smul (r : ℝ) (T : ValueSpace V →L[ℝ] ValueSpace V) :
      complexify (r • T) = r • complexify T := by
    apply ContinuousLinearMap.ext
    intro z
    apply ext_parts V
    · rw [realPart_complexify]
      change r • T (realPart V z) = realPart V ((r : ℂ) • complexify T z)
      rw [realPart_complex_smul]
      simp
    · rw [imagPart_complexify]
      change r • T (imagPart V z) = imagPart V ((r : ℂ) • complexify T z)
      rw [imagPart_complex_smul]
      simp
  rw [cfc_occupationResolventMultiplier _ (complexOneResolvent_isSelfAdjoint G m)
    (complexOneResolvent_spectrum_subset G m) ha]
  rw [hcomplexify_smul, complexify_parameterizedResolvent_eq_cfc_eulerStep G m
    (one_div_pos.mpr ha)]

/-- The ordinary full-semigroup Dynkin identity for an arbitrary resolvent input. -/
theorem fullFormSemigroup_scaledResolvent_dynkin
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha)
    (t : ℝ≥0) (F : ValueSpace V) :
    fullFormSemigroup G m t ((1 / alpha) • parameterizedResolvent G m (1 / alpha) F) -
        (1 / alpha) • parameterizedResolvent G m (1 / alpha) F =
      ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        fullFormSemigroup G m (Real.toNNReal s)
          (alpha • ((1 / alpha) • parameterizedResolvent G m (1 / alpha) F) - F) := by
  let R := complexOneResolvent G m
  let U := (1 / alpha) • parameterizedResolvent G m (1 / alpha) F
  let Q := cfc (occupationResolventMultiplier alpha) R
  let g := alpha • U - F
  have hQ : Q = complexify ((1 / alpha) • parameterizedResolvent G m (1 / alpha)) := by
    simpa only [Q, R] using cfc_occupationResolventMultiplier_eq_complexify G m ha
  have hQU : Q (ofReal V F) = ofReal V U := by
    rw [hQ]
    exact complexify_ofReal _ _
  have hop := spectralSemigroup_occupationResolvent_dynkin R
    (complexOneResolvent_isSelfAdjoint G m)
    (complexOneResolvent_spectrum_subset G m) ha t
  have hIntOp := integrableOn_spectralSemigroup_occupationGenerator R
    (complexOneResolvent_isSelfAdjoint G m)
    (complexOneResolvent_spectrum_subset G m) ha t
  change spectralSemigroup R t * Q - Q =
    ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      spectralSemigroup R (Real.toNNReal s) * (alpha • Q - 1) at hop
  change IntegrableOn (fun s : ℝ ↦
    spectralSemigroup R (Real.toNNReal s) * (alpha • Q - 1))
    (Ioc (0 : ℝ) (t : ℝ)) at hIntOp
  rw [intervalIntegral.integral_of_le t.coe_nonneg] at hop ⊢
  have happ := congrArg (fun T : ComplexL2 V →L[ℂ] ComplexL2 V ↦ T (ofReal V F)) hop
  have happly :
      (∫ s : ℝ in Ioc (0 : ℝ) (t : ℝ),
        spectralSemigroup R (Real.toNNReal s) * (alpha • Q - 1)) (ofReal V F) =
      ∫ s : ℝ in Ioc (0 : ℝ) (t : ℝ),
        (spectralSemigroup R (Real.toNNReal s) * (alpha • Q - 1)) (ofReal V F) :=
    ContinuousLinearMap.integral_apply hIntOp (ofReal V F)
  rw [happly] at happ
  have hcomplex (s : ℝ) :
      (spectralSemigroup R (Real.toNNReal s) *
          (alpha • Q - 1)) (ofReal V F) =
        ofReal V (fullFormSemigroup G m (Real.toNNReal s) g) := by
    change spectralSemigroup R (Real.toNNReal s)
      (alpha • Q (ofReal V F) - ofReal V F) = _
    rw [hQU]
    change spectralSemigroup R (Real.toNNReal s)
      (alpha • ofReal V U - ofReal V F) = _
    have harg : alpha • ofReal V U - ofReal V F = ofReal V g := by
      simp only [g, map_sub, map_smul]
    rw [harg]
    change fullFormSemigroupComplex G m (Real.toNNReal s) (ofReal V g) = _
    exact fullFormSemigroupComplex_ofReal G m (Real.toNNReal s) g
  have hgcont : Continuous (fun s : ℝ ↦
      fullFormSemigroup G m (Real.toNNReal s) g) :=
    (fullFormSemigroup_continuous G m hm g).comp continuous_real_toNNReal
  have hgint : IntegrableOn (fun s : ℝ ↦
      fullFormSemigroup G m (Real.toNNReal s) g) (Ioc (0 : ℝ) (t : ℝ)) :=
    (hgcont.intervalIntegrable 0 (t : ℝ)).1
  apply ofReal_injective V
  calc
    ofReal V (fullFormSemigroup G m t U - U) =
        (spectralSemigroup R t * Q - Q) (ofReal V F) := by
      change ofReal V (fullFormSemigroup G m t U - U) =
        spectralSemigroup R t (Q (ofReal V F)) - Q (ofReal V F)
      rw [hQU, map_sub]
      change ofReal V (fullFormSemigroup G m t U) - ofReal V U =
        fullFormSemigroupComplex G m t (ofReal V U) - ofReal V U
      rw [fullFormSemigroupComplex_ofReal]
    _ = ∫ s : ℝ in Ioc (0 : ℝ) (t : ℝ),
        (spectralSemigroup R (Real.toNNReal s) * (alpha • Q - 1)) (ofReal V F) := happ
    _ = ∫ s : ℝ in Ioc (0 : ℝ) (t : ℝ),
        ofReal V (fullFormSemigroup G m (Real.toNNReal s) g) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      exact hcomplex s
    _ = ofReal V (∫ s : ℝ in Ioc (0 : ℝ) (t : ℝ),
        fullFormSemigroup G m (Real.toNNReal s) g) := by
      exact (ofReal V).integral_comp_comm hgint

/-- The ordinary full-semigroup Dynkin identity for a vertex resolvent vector. -/
theorem fullFormSemigroup_vertexOccupationPotentialValue_dynkin
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha)
    (t : ℝ≥0) (y : V) :
    fullFormSemigroup G m t (vertexOccupationPotentialValue G m alpha y) -
        vertexOccupationPotentialValue G m alpha y =
      ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        fullFormSemigroup G m (Real.toNNReal s)
          (alpha • vertexOccupationPotentialValue G m alpha y -
            weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)) :=
  fullFormSemigroup_scaledResolvent_dynkin G m hm ha t
    (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))

theorem vertexOccupationPotential_dynkin
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (_hmsum : Summable m)
    {alpha : ℝ} (ha : 0 < alpha) (t : ℝ≥0) (x y : V) :
    unweight m (fullFormSemigroup G m t
        (vertexOccupationPotentialValue G m alpha y)) x -
        vertexOccupationPotential G m alpha x y =
      ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        unweight m (fullFormSemigroup G m (Real.toNNReal s)
          (alpha • vertexOccupationPotentialValue G m alpha y -
            weightedValue m (G.indic y)
              (VertexTest.indic_hasSpeedL2 G m y))) x := by
  let L : ValueSpace V →L[ℝ] ℝ :=
    (1 / Real.sqrt (m x)) • lp.evalCLM ℝ (fun _ : V ↦ ℝ) 2 x
  have hL (u : ValueSpace V) : L u = unweight m u x := by
    change (1 / Real.sqrt (m x)) * u x = u x / Real.sqrt (m x)
    ring
  have h := congrArg L
    (fullFormSemigroup_vertexOccupationPotentialValue_dynkin G m hm ha t y)
  let g : ℝ → ValueSpace V := fun s ↦
    fullFormSemigroup G m (Real.toNNReal s)
      (alpha • vertexOccupationPotentialValue G m alpha y -
        weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))
  have hgint : IntervalIntegrable g volume 0 (t : ℝ) :=
    by simpa only [g, Function.comp_def] using (((fullFormSemigroup_continuous G m hm _).comp
      continuous_real_toNNReal).intervalIntegrable 0 (t : ℝ))
  change L (fullFormSemigroup G m t
      (vertexOccupationPotentialValue G m alpha y) -
        vertexOccupationPotentialValue G m alpha y) =
    L (∫ s : ℝ in (0 : ℝ)..(t : ℝ), g s) at h
  rw [← L.intervalIntegral_comp_comm hgint] at h
  simp_rw [hL] at h
  have hsub : unweight m
      (fullFormSemigroup G m t (vertexOccupationPotentialValue G m alpha y) -
        vertexOccupationPotentialValue G m alpha y) x =
      unweight m (fullFormSemigroup G m t
        (vertexOccupationPotentialValue G m alpha y)) x -
        unweight m (vertexOccupationPotentialValue G m alpha y) x := by
    change ((fullFormSemigroup G m t
        (vertexOccupationPotentialValue G m alpha y)) x -
          (vertexOccupationPotentialValue G m alpha y) x) /
        Real.sqrt (m x) =
      (fullFormSemigroup G m t
        (vertexOccupationPotentialValue G m alpha y)) x / Real.sqrt (m x) -
          (vertexOccupationPotentialValue G m alpha y) x / Real.sqrt (m x)
    ring
  rw [hsub, unweight_vertexOccupationPotentialValue G m ha] at h
  simpa only [g] using h

end ReflectedGMS.FullNetworkForm
