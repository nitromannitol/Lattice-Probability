/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventMarkov

/-! Resolvent lifts are dense in the entire form domain. This is the existing
Hilbert-space adjoint range/kernel identity applied to the injective inclusion. -/

set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)

theorem denseRange_valueInclusion_adjoint :
    DenseRange ((valueInclusion G m).adjoint) := by
  change Dense ((valueInclusion G m).adjoint.range : Set (hilbertDomain G m))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← (valueInclusion G m).orthogonal_ker]
  have hker : (valueInclusion G m).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (valueInclusion_injective G m)
  rw [hker, Submodule.bot_orthogonal_eq_top]

theorem denseRange_oneResolventLift : DenseRange (oneResolventLift G m) :=
  denseRange_valueInclusion_adjoint G m

end ReflectedGMS.FullNetworkForm
