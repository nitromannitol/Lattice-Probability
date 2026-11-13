/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventProperties at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.Resolvent
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Positivity, contraction and spectrum of the full-form 1-resolvent

All operator theory is reused from mathlib. These properties concern the actual
`J ∘ J.adjoint` resolvent on the existing weighted vertex `lp 2` space.
No continuous functional calculus for real operators or semigroup is assumed.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- The bounded inclusion has operator norm at most one. -/
theorem valueInclusion_opNorm_le_one (m : V → ℝ) : ‖valueInclusion G m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  simpa only [one_mul] using valueInclusion_norm_le G m u

/-- The adjoint solution map has the same operator norm bound. -/
theorem oneResolventLift_opNorm_le_one (m : V → ℝ) : ‖oneResolventLift G m‖ ≤ 1 := by
  simpa only [oneResolventLift, LinearIsometryEquiv.norm_map]
    using valueInclusion_opNorm_le_one G m

/-- Positivity of the exact full-form resolvent follows from `J ∘ J.adjoint`. -/
theorem oneResolvent_isPositive (m : V → ℝ) : (oneResolvent G m).IsPositive := by
  simpa only [oneResolvent, oneResolventLift]
    using ContinuousLinearMap.isPositive_self_comp_adjoint (valueInclusion G m)

/-- The 1-resolvent is self-adjoint on weighted vertex `L²`. -/
theorem oneResolvent_isSelfAdjoint (m : V → ℝ) : IsSelfAdjoint (oneResolvent G m) :=
  (oneResolvent_isPositive G m).isSelfAdjoint

/-- Nonnegativity in the existing Loewner order on Hilbert-space operators. -/
theorem oneResolvent_nonneg (m : V → ℝ) : 0 ≤ oneResolvent G m :=
  ContinuousLinearMap.nonneg_iff_isPositive.2 (oneResolvent_isPositive G m)

/-- The actual 1-resolvent is a contraction in operator norm. -/
theorem oneResolvent_opNorm_le_one (m : V → ℝ) : ‖oneResolvent G m‖ ≤ 1 := by
  calc
    ‖oneResolvent G m‖ ≤ ‖valueInclusion G m‖ * ‖oneResolventLift G m‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (valueInclusion_opNorm_le_one G m)
      (oneResolventLift_opNorm_le_one G m) (norm_nonneg (oneResolventLift G m)) (by norm_num)
    _ = 1 := one_mul 1

/-- The corresponding norm contraction for every weighted vertex function. -/
theorem oneResolvent_apply_norm_le (m : V → ℝ) (f : ValueSpace V) :
    ‖oneResolvent G m f‖ ≤ ‖f‖ := by
  calc
    ‖oneResolvent G m f‖ ≤ ‖oneResolvent G m‖ * ‖f‖ :=
      (oneResolvent G m).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (oneResolvent_opNorm_le_one G m)
      (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-- The real spectrum is contained in `[0,1]`, including the trivial-space case. -/
theorem oneResolvent_spectrum_subset (m : V → ℝ) :
    spectrum ℝ (oneResolvent G m) ⊆ Set.Icc (0 : ℝ) 1 := by
  rcases subsingleton_or_nontrivial (ValueSpace V) with h | h
  · letI := h
    simp only [spectrum.of_subsingleton, Set.empty_subset]
  · letI := h
    intro x hx
    exact ⟨spectrum_nonneg_of_nonneg (oneResolvent_nonneg G m) hx,
      (Real.le_norm_self x).trans
        ((spectrum.norm_le_norm_of_mem hx).trans (oneResolvent_opNorm_le_one G m))⟩

end ReflectedGMS.FullNetworkForm
