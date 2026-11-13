/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Graph.Restriction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Basic

set_option autoImplicit false

namespace ReflectedGMS

variable {V : Type*}

/-- Restrict the original conductances to any vertex set, with no finiteness assumption. -/
def restrictGraph (G : ReflectedWalk.ConductanceGraph V) (A : Set V) :
    ReflectedWalk.ConductanceGraph A where
  c x y := G.c x.1 y.1
  c_symm x y := G.c_symm x.1 y.1
  c_nonneg x y := G.c_nonneg x.1 y.1
  c_self x := G.c_self x.1
  summable_c x := (G.summable_c x.1).subtype (fun y => y ∈ A)

/-- The conductance restriction has exactly the induced adjacency relation. -/
theorem restrictGraph_toSimpleGraph (G : ReflectedWalk.ConductanceGraph V) (A : Set V) :
    (restrictGraph G A).toSimpleGraph = G.toSimpleGraph.induce A := by
  ext x y
  rfl

end ReflectedGMS
