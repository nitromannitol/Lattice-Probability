/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DomainDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventProperties

/-! Injectivity and dense range of the actual full-form resolvent. These facts
remove a zero eigenspace obstruction in the later semigroup construction.
All Hilbert-space duality is reused from mathlib. -/
set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

theorem oneResolventLift_ker_eq_bot (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    (oneResolventLift G m).ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hd : Dense ((valueInclusion G m).range : Set (ValueSpace V)) :=
    denseRange_valueInclusion G m hm
  apply hd.eq_zero_of_mem_orthogonal
  rw [(valueInclusion G m).orthogonal_range]
  exact hx

theorem oneResolvent_ker_eq_bot (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    (oneResolvent G m).ker = ⊥ := by
  change ((valueInclusion G m).comp (valueInclusion G m).adjoint).ker = ⊥
  rw [(valueInclusion G m).ker_self_comp_adjoint]
  exact oneResolventLift_ker_eq_bot G m hm

theorem oneResolvent_injective (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    Function.Injective (oneResolvent G m) :=
  LinearMap.ker_eq_bot.mp (oneResolvent_ker_eq_bot G m hm)

theorem denseRange_oneResolvent (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    DenseRange (oneResolvent G m) := by
  change Dense ((oneResolvent G m).range : Set (ValueSpace V))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.IsStarNormal.orthogonal_range
      (oneResolvent_isSelfAdjoint G m).isStarNormal,
    oneResolvent_ker_eq_bot G m hm]

end ReflectedGMS.FullNetworkForm
