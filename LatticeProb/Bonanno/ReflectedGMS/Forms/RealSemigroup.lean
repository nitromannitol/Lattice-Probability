/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.RealSemigroup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.RealFunctionalCalculus
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpectralSemigroup

/-!
# The full-form semigroup on the original real space

The real semigroup is the unique real pullback of the checked spectral semigroup
of the actual full-form resolvent. Algebraic identities, the contraction bound,
and continuous orbits transfer along that exact complexification map.

Positivity preservation, the Markov property, and association with a process are
separate obligations; none is a hypothesis or conclusion of this adapter.
-/

-- Merged from `ReflectedGMS/Forms/SemigroupContinuity.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_SemigroupContinuity

/-! Strong continuity at zero of a contraction semigroup extends to every
nonnegative time. Only the semigroup law, contraction bound and continuity at
zero are used; no differentiability or bounded generator is assumed. -/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.FullNetworkForm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem contraction_apply_norm_le (A : E →L[𝕜] E) (hA : ‖A‖ ≤ 1) (x : E) :
    ‖A x‖ ≤ ‖x‖ := by
  calc
    ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Compare two times using an increment at zero, on either side of the time. -/
theorem contraction_semigroup_increment_bound
    (S : ℝ≥0 → E →L[𝕜] E)
    (hadd : ∀ s t, S (s + t) = S s * S t) (hS : ∀ t, ‖S t‖ ≤ 1)
    (s t : ℝ≥0) (x : E) :
    ‖S s x - S t x‖ ≤ ‖S (max s t - min s t) x - x‖ := by
  have hle (a b : ℝ≥0) (hab : a ≤ b) :
      ‖S a x - S b x‖ ≤ ‖S (b - a) x - x‖ := by
    have heq : S b x = S a (S (b - a) x) := by
      calc
        S b x = S (a + (b - a)) x :=
          congrArg (fun u => S u x) (add_tsub_cancel_of_le hab).symm
        _ = S a (S (b - a) x) := by rw [hadd]; rfl
    calc
      _ = ‖S a (x - S (b - a) x)‖ := by rw [map_sub, heq]
      _ ≤ ‖x - S (b - a) x‖ := contraction_apply_norm_le (S a) (hS a) _
      _ = ‖S (b - a) x - x‖ := norm_sub_rev _ _
  rcases le_total s t with h | h
  · simpa only [max_eq_right h, min_eq_left h] using hle s t h
  · simpa only [max_eq_left h, min_eq_right h, norm_sub_rev (S t x) (S s x)]
      using hle t s h

/-- A contraction semigroup strongly continuous at zero has continuous orbits. -/
theorem contraction_semigroup_continuous
    (S : ℝ≥0 → E →L[𝕜] E)
    (hadd : ∀ s t, S (s + t) = S s * S t) (hS : ∀ t, ‖S t‖ ≤ 1)
    (hzero : ∀ x, Tendsto (fun t => S t x) (𝓝 0) (𝓝 x)) (x : E) :
    Continuous (fun t => S t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have htime : Tendsto (fun s : ℝ≥0 => max s t - min s t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ≥0 => max s t - min s t) :=
      (continuous_id.max continuous_const).sub (continuous_id.min continuous_const)
    simpa using (hc.continuousAt (x := t)).tendsto
  have hnorm : Tendsto (fun s : ℝ≥0 => ‖S s x - x‖) (𝓝 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hzero x)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun s => contraction_semigroup_increment_bound S hadd hS s t x) (hnorm.comp htime)

/-- Continuous orbits of the concrete full-form spectral semigroup. -/
theorem fullFormSemigroupComplex_continuous {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (x : ComplexSequenceSpace.ComplexL2 V) :
    Continuous (fun t => fullFormSemigroupComplex G m t x) :=
  contraction_semigroup_continuous (fullFormSemigroupComplex G m)
    (spectralSemigroup_add (complexOneResolvent G m))
    (spectralSemigroup_norm_le_one (complexOneResolvent G m)
      (complexOneResolvent_spectrum_subset G m))
    (fullFormSemigroupComplex_tendsto_zero G m hm) x

end ReflectedGMS.FullNetworkForm

end Merged_SemigroupContinuity

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.FullNetworkForm

open ComplexSequenceSpace SemigroupMultiplier

variable {V : Type*}

/-- The spectral construction pulled back to the original real vertex space. -/
noncomputable def fullFormSemigroup (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (t : ℝ≥0) : ValueSpace V →L[ℝ] ValueSpace V :=
  realCFC (k t) (oneResolvent G m)

@[simp] theorem complexify_fullFormSemigroup (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (t : ℝ≥0) :
    complexify (fullFormSemigroup G m t) = fullFormSemigroupComplex G m t :=
  complexify_realCFC (k t) (oneResolvent G m)

theorem fullFormSemigroupComplex_ofReal (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (t : ℝ≥0) (u : ValueSpace V) :
    fullFormSemigroupComplex G m t (ofReal V u) =
      ofReal V (fullFormSemigroup G m t u) := by
  rw [← complexify_fullFormSemigroup, complexify_ofReal]

theorem fullFormSemigroup_zero (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) :
    fullFormSemigroup G m 0 = 1 := by
  apply complexifyAlgHom_isometry.injective
  change complexify (fullFormSemigroup G m 0) = complexify 1
  rw [complexify_fullFormSemigroup, complexify_one]
  exact spectralSemigroup_zero _ (complexOneResolvent_isSelfAdjoint G m)

theorem fullFormSemigroup_add (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (s t : ℝ≥0) :
    fullFormSemigroup G m (s + t) = fullFormSemigroup G m s * fullFormSemigroup G m t := by
  apply complexifyAlgHom_isometry.injective
  change complexify (fullFormSemigroup G m (s + t)) =
    complexify (fullFormSemigroup G m s * fullFormSemigroup G m t)
  simp only [complexify_mul, complexify_fullFormSemigroup]
  exact spectralSemigroup_add _ s t

theorem fullFormSemigroup_isSelfAdjoint (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (t : ℝ≥0) : IsSelfAdjoint (fullFormSemigroup G m t) := by
  rw [isSelfAdjoint_iff]
  apply complexifyAlgHom_isometry.injective
  change complexify (star (fullFormSemigroup G m t)) = complexify (fullFormSemigroup G m t)
  simp only [complexify_star, complexify_fullFormSemigroup]
  exact spectralSemigroup_isSelfAdjoint _ t

theorem fullFormSemigroup_norm_le_one (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (t : ℝ≥0) : ‖fullFormSemigroup G m t‖ ≤ 1 := by
  rw [← complexify_norm (fullFormSemigroup G m t), complexify_fullFormSemigroup]
  exact spectralSemigroup_norm_le_one _ (complexOneResolvent_spectrum_subset G m) t

theorem fullFormSemigroup_continuous (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (u : ValueSpace V) :
    Continuous (fun t => fullFormSemigroup G m t u) := by
  have h := (realPart V).continuous.comp
    (fullFormSemigroupComplex_continuous G m hm (ofReal V u))
  simpa only [Function.comp_def, fullFormSemigroupComplex_ofReal,
    ComplexSequenceSpace.realPart_ofReal] using h

end ReflectedGMS.FullNetworkForm
