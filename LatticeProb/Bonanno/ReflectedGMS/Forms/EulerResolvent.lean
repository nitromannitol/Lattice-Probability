/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.EulerResolvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ParameterizedResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.EulerApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.RealSemigroup

/-!
# Euler multipliers are the parameterized resolvents

The checked algebraic `h`-resolvent is exactly the real pullback of the Euler
multiplier applied by the existing complex continuous functional calculus.
-/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.FullNetworkForm

open SemigroupMultiplier
open ComplexSequenceSpace

variable {V : Type*}

-- Use the same real restriction of the complex operator algebra as `realCFC`.
noncomputable local instance : SMul ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) :=
  ⟨fun r T => (r : ℂ) • T⟩
noncomputable local instance : Algebra ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) :=
  Algebra.complexToReal

/-- Complexifying the algebraic `h`-resolvent gives the Euler multiplier of the
complexified `1`-resolvent. -/
theorem complexify_parameterizedResolvent_eq_cfc_eulerStep
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) {h : ℝ} (hh : 0 < h) :
    complexify (parameterizedResolvent G m h) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (eulerStep h)
        (complexOneResolvent G m) := by
  let R := complexOneResolvent G m
  let B := resolventDenominator G m h
  let Bc : ComplexL2 V →L[ℂ] ComplexL2 V := h • 1 + (1 - h) • R
  have hB : IsUnit B := resolventDenominator_isUnit G m hh
  have hcomplexify_smul (r : ℝ) (T : ValueSpace V →L[ℝ] ValueSpace V) :
      complexify (r • T) = r • complexify T := by
    apply ContinuousLinearMap.ext
    intro z
    apply ComplexSequenceSpace.ext_parts V
    · rw [ComplexSequenceSpace.realPart_complexify]
      change r • T (ComplexSequenceSpace.realPart V z) =
        ComplexSequenceSpace.realPart V ((r : ℂ) • complexify T z)
      rw [ComplexSequenceSpace.realPart_complex_smul]
      simp
    · rw [ComplexSequenceSpace.imagPart_complexify]
      change r • T (ComplexSequenceSpace.imagPart V z) =
        ComplexSequenceSpace.imagPart V ((r : ℂ) • complexify T z)
      rw [ComplexSequenceSpace.imagPart_complex_smul]
      simp
  have hBc_eq : complexify B = Bc := by
    change ComplexSequenceSpace.complexifyAlgHom B = Bc
    simp [B, Bc, R, resolventDenominator, complexOneResolvent, hcomplexify_smul]
  have hBc : IsUnit Bc := by
    rw [← hBc_eq]
    exact hB.map (ComplexSequenceSpace.complexifyAlgHom (V := V))
  have hinv : complexify (Ring.inverse B) = Ring.inverse Bc := by
    apply (Ring.eq_mul_inverse_iff_mul_eq (complexify (Ring.inverse B))
      (1 : ComplexL2 V →L[ℂ] ComplexL2 V) Bc hBc).2
    rw [← hBc_eq, ← ComplexSequenceSpace.complexify_mul,
      Ring.inverse_mul_cancel B hB, ComplexSequenceSpace.complexify_one]
  have hspec := complexOneResolvent_spectrum_subset G m
  have hR : IsSelfAdjoint R := complexOneResolvent_isSelfAdjoint G m
  have hden_ne (x : ℝ) (hx : x ∈ spectrum ℝ R) :
      x + h * (1 - x) ≠ 0 :=
    (eulerStep_denominator_pos hh (hspec hx)).ne'
  have hden_cont : ContinuousOn (fun x : ℝ => x + h * (1 - x))
      (spectrum ℝ R) := by
    fun_prop
  have hden_cfc :
      cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x + h * (1 - x)) R = Bc := by
    have hfun : (fun x : ℝ => x + h * (1 - x)) =
        (fun x : ℝ => h + (1 - h) * x) := by
      funext x
      ring
    rw [hfun, cfc_const_add h (fun x : ℝ => (1 - h) * x) R
      (by fun_prop) hR, cfc_const_mul_id (1 - h) R hR]
    simp [Bc, R, Algebra.algebraMap_eq_smul_one]
  rw [parameterizedResolvent, ComplexSequenceSpace.complexify_mul, hinv]
  change R * Ring.inverse Bc =
    cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => x / (x + h * (1 - x))) R
  rw [cfc_map_div (p := IsSelfAdjoint) (fun x : ℝ => x)
    (fun x : ℝ => x + h * (1 - x)) R
    hden_ne (hf := continuousOn_id) (hg := hden_cont) (ha := hR),
    cfc_id' ℝ R hR, hden_cfc]

/-- Dyadic powers of the actual real parameterized resolvents converge in
operator norm to the checked real full-form semigroup. -/
theorem dyadic_parameterizedResolvent_pow_tendsto
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto
      (fun n => parameterizedResolvent G m
        ((t : ℝ) / (2 : ℝ) ^ n) ^ (2 ^ n : ℕ))
      atTop (𝓝 (fullFormSemigroup G m t)) := by
  rw [ComplexSequenceSpace.complexifyAlgHom_isometry.isClosedEmbedding.tendsto_nhds_iff]
  change Tendsto
    (fun n => complexify
      (parameterizedResolvent G m ((t : ℝ) / (2 : ℝ) ^ n) ^ (2 ^ n : ℕ)))
    atTop (𝓝 (complexify (fullFormSemigroup G m t)))
  have hpow (T : ValueSpace V →L[ℝ] ValueSpace V) (n : ℕ) :
      complexify (T ^ n) = complexify T ^ n := by
    change ComplexSequenceSpace.complexifyAlgHom (T ^ n) =
      ComplexSequenceSpace.complexifyAlgHom T ^ n
    exact map_pow _ T n
  have hstep (n : ℕ) :
      complexify (parameterizedResolvent G m ((t : ℝ) / (2 : ℝ) ^ n)) =
        cfc (R := ℝ) (p := IsSelfAdjoint)
          (eulerStep ((t : ℝ) / (2 : ℝ) ^ n)) (complexOneResolvent G m) :=
    complexify_parameterizedResolvent_eq_cfc_eulerStep G m
      (div_pos (show 0 < (t : ℝ) from ht) (pow_pos (by norm_num) n))
  simp_rw [hpow, hstep]
  rw [complexify_fullFormSemigroup]
  exact dyadicEuler_pow_tendsto (complexOneResolvent G m)
    (complexOneResolvent_isSelfAdjoint G m)
    (complexOneResolvent_spectrum_subset G m) ht

end ReflectedGMS.FullNetworkForm
