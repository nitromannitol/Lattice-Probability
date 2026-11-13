/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTargetL2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTargetOrthogonality
import LatticeProb.Bonanno.ReflectedWalk.FiniteApproximation
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupConservation
import LatticeProb.Bonanno.ReflectedWalk.HarmonicMeasure
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Finite-target approximation in the full speed-L2 form domain

For summable positive speed, every bounded function lies in the weighted vertex
`L²` space.  The maximum principle gives the same uniform bound for its actual
full-network finite-target harmonic extensions.  Pointwise eventual equality and
dominated convergence then upgrade the existing residual-energy convergence to
convergence in both coordinates of the full form domain.

The summability hypothesis is essential: bounded nonzero functions need not lie
in speed `L²` when the total speed is infinite.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open scoped ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- A uniformly bounded function is in speed `L²` when the positive speed is summable. -/
theorem hasSpeedL2_of_abs_le {m : V → ℝ} (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} {C : ℝ} (hf : ∀ v, |f v| ≤ C) :
    HasSpeedL2 m f := by
  have hconst := hasSpeedL2_const hm hmsum C
  apply hconst.mono'
  intro v
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((hf v).trans (le_abs_self C)) (abs_nonneg _)

end ReflectedGMS.FullNetworkForm
