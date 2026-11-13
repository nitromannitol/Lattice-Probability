/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedOccupationFormDomain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventRange
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# A full-domain criterion for stopped occupation densities

A weighted `L²` vector belongs to the full energy domain whenever pairing
against it is bounded in the graph norm of the lifted resolvent. The proof
extends the induced functional on the resolvent range and uses Hilbert-space
duality. In particular, no finite-support closure replaces the full domain.

Applying this criterion to an actual stopped occupation density still requires
its `L²` construction and the stopped Dynkin graph-norm bound.
-/

set_option autoImplicit false
open scoped InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- The resolvent graph-norm dual bound puts a weighted occupation candidate
in the actual full form domain. Positivity of the speed measure ensures
injectivity of the lifted resolvent. -/
theorem exists_fullDomain_of_resolvent_pairing_bound
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (w : ValueSpace V)
    (hw : ∃ C : ℝ, ∀ f : ValueSpace V,
      |⟪f, w⟫_ℝ| ≤ C * ‖oneResolventLift G m f‖) :
    ∃ W : hilbertDomain G m, valueInclusion G m W = w := by
  classical
  obtain ⟨C, hC⟩ := hw
  let R := (oneResolventLift G m).toLinearMap
  have hR : Function.Injective R :=
    LinearMap.ker_eq_bot.mp (oneResolventLift_ker_eq_bot G m hm)
  let e : ValueSpace V ≃ₗ[ℝ] R.range := LinearEquiv.ofInjective R hR
  let L : R.range →ₗ[ℝ] ℝ :=
    (innerSL ℝ w).toLinearMap.comp e.symm.toLinearMap
  have hL : ∀ u : R.range, ‖L u‖ ≤ C * ‖u‖ := by
    intro u
    have hu : oneResolventLift G m (e.symm u) = (u : hilbertDomain G m) :=
      LinearEquiv.ofInjective_symm_apply R (h := hR) u
    change ‖⟪w, e.symm u⟫_ℝ‖ ≤ C * ‖u‖
    rw [Real.norm_eq_abs, real_inner_comm]
    simpa only [hu, Submodule.norm_coe] using hC (e.symm u)
  obtain ⟨Λ, hΛ, _⟩ := exists_extension_norm_eq R.range (L.mkContinuous C hL)
  let W : hilbertDomain G m := (InnerProductSpace.toDual ℝ (hilbertDomain G m)).symm Λ
  refine ⟨W, ext_inner_left ℝ fun f ↦ ?_⟩
  have hΛf : Λ (oneResolventLift G m f) = ⟪w, f⟫_ℝ := by
    have h := hΛ (e f)
    change Λ (oneResolventLift G m f) = ⟪w, e.symm (e f)⟫_ℝ at h
    simpa only [e.symm_apply_apply] using h
  calc
    ⟪f, valueInclusion G m W⟫_ℝ = ⟪oneResolventLift G m f, W⟫_ℝ :=
      (oneResolventLift_weak G m f W).symm
    _ = ⟪W, oneResolventLift G m f⟫_ℝ := real_inner_comm _ _
    _ = Λ (oneResolventLift G m f) := InnerProductSpace.toDual_symm_apply
    _ = ⟪w, f⟫_ℝ := hΛf
    _ = ⟪f, w⟫_ℝ := real_inner_comm _ _

end ReflectedGMS.FullNetworkForm
