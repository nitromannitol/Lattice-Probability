/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CompactCoreAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactVertexSpace
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedEnergyAlgebra
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexTest
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Uniform density of the continuous full-energy algebra

The supplied bounded finite-energy features and all vertex indicators extend
continuously to their compact evaluation closure. Their real algebra separates
points, so the existing Stone-Weierstrass theorem gives uniform density. Only the
original feature list must be countable for metrizability: products are continuous
functions of existing coordinates and require no extra coordinate generators.
Full form-norm density of the feature list is a separate obligation.
-/

set_option autoImplicit false

open Set

namespace ReflectedGMS.CompactVertexSpace

variable {V I : Type*} (feature : I → V → ℝ) (bound : I → ℝ)
  (hbound : ∀ i x, |feature i x| ≤ bound i)

noncomputable def indicatorCoordinate (x : V) : C(Space feature bound hbound, ℝ) where
  toFun z := z.1.1 x
  continuous_toFun := continuous_subtype_val.comp ((continuous_apply x).comp
    (continuous_fst.comp continuous_subtype_val))

variable (G : ReflectedWalk.ConductanceGraph V)

end ReflectedGMS.CompactVertexSpace
