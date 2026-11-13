/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DomainDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.Resolvent
import LatticeProb.Bonanno.ReflectedWalk.Proposition13

/-! Density of the full form domain in weighted vertex L². Only finite-support
functions are used to prove L² density; the energy domain itself remains the
entire finite-energy domain, with no energy-norm closure restriction. -/
set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

@[simp] theorem weightedValue_unweight (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (u : ValueSpace V) :
    weightedValue m (unweight m u) (hasSpeedL2_unweight m hm u) = u := by
  apply lp.ext
  funext v
  exact mul_div_cancel₀ (u v) (Real.sqrt_pos.2 (hm v)).ne'

/-- Every coordinate vector belongs to the range of the actual inclusion.
Finite energy comes from the existing finite-support theorem, not local
finiteness or a new energy argument. -/
theorem single_mem_range_valueInclusion [DecidableEq V] (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (v : V) (a : ℝ) :
    lp.single 2 v a ∈ (valueInclusion G m).range := by
  classical
  let u : ValueSpace V := lp.single 2 v a
  have hE : G.HasFiniteEnergy (unweight m u) := by
    apply G.hasFiniteEnergy_of_support_subset {v}
    intro w hw
    have hwv : w ≠ v := by simpa using hw
    simp [unweight, u, lp.single_apply, hwv]
  refine ⟨inHilbertDomain G m hm (unweight m u) (hasSpeedL2_unweight m hm u) hE, ?_⟩
  change weightedValue m (unweight m u) (hasSpeedL2_unweight m hm u) = u
  exact weightedValue_unweight m hm u

/-- The full form is densely defined in the speed-L² space. The approximation
is only in the L² topology, as required for a densely defined Dirichlet form. -/
theorem denseRange_valueInclusion (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    DenseRange (valueInclusion G m) := by
  classical
  intro u
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) u)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  exact (valueInclusion G m).range.sum_mem fun v _ =>
    single_mem_range_valueInclusion G m hm v (u v)

end ReflectedGMS.FullNetworkForm
