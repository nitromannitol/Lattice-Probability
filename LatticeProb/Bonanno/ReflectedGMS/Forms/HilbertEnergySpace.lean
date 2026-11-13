/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.HilbertEnergySpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullNetworkForm
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The full energy domain with its actual Hilbert graph norm. We transport
the existing closed compatibility graph through mathlib's L² product wrapper;
the domain and its closure proof are reused. -/
set_option autoImplicit false

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

abbrev EnergyAmbient (V : Type*) := WithLp 2 (ValueSpace V × GradientSpace V)

/-- The same full graph domain in the L² product inner product space. -/
noncomputable def hilbertDomain (m : V → ℝ) : Submodule ℝ (EnergyAmbient V) :=
  (graphSubmodule G m).comap
    (WithLp.linearEquiv 2 ℝ (ValueSpace V × GradientSpace V)).toLinearMap

theorem isClosed_hilbertDomain (m : V → ℝ) :
    IsClosed (hilbertDomain G m : Set (EnergyAmbient V)) :=
  (isClosed_graphSubmodule G m).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ (ValueSpace V) (GradientSpace V)).continuous

instance hilbertDomain.instCompleteSpace (m : V → ℝ) :
    CompleteSpace (hilbertDomain G m) :=
  (isClosed_hilbertDomain G m).isComplete.completeSpace_coe

/-- Every function of finite energy and finite speed-L² norm enters the space. -/
noncomputable def inHilbertDomain (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (hL2 : HasSpeedL2 m f) (hE : G.HasFiniteEnergy f) :
    hilbertDomain G m :=
  ⟨WithLp.toLp 2 (weightedValue m f hL2, weightedGradient G f hE),
    weightedPair_mem G m hm f hL2 hE⟩

noncomputable example (m : V → ℝ) : InnerProductSpace ℝ (hilbertDomain G m) := inferInstance

end ReflectedGMS.FullNetworkForm
