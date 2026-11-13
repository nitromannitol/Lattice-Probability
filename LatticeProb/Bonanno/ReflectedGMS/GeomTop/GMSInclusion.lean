/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.GMSInclusion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.Statement
import Mathlib.Util.AssertNoSorry

/-!
# The GMS configuration space inside `C_sing`

Every GMS cell configuration (GMS Definition 1.15, `GMS.CellConfig.IsCellConfiguration`) satisfies
the geometric clauses (i)–(iii) of Definition 1.1 of the geometric-topology revision, with empty
singular-set witness.  `toSing : GMSSpace → SingSpace` is the resulting inclusion; it does not change
the underlying unmarked configuration.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace ReflectedGMS.GeomTop

open GMS

/-- The empty singular-set witness of a GMS cell configuration. -/
def emptyWitness {H : CellConfig} (hH : H.IsCellConfiguration) : SingularWitness H where
  sing := ∅
  isClosed_sing := isClosed_empty
  hausdorff_sing := measure_empty
  cover := by rw [compl_empty, hH.iUnion_eq_univ]
  locallyFinite := fun z _ => hH.locallyFinite z

/-- A GMS cell configuration is in `C_sing`. -/
theorem isSingConfiguration_of_isCellConfiguration {H : CellConfig} (hH : H.IsCellConfiguration) :
    IsSingConfiguration H where
  isConnected := hH.isConnected
  interior_nonempty := hH.interior_nonempty
  volume_inter := hH.volume_inter
  witness := ⟨emptyWitness hH⟩
  c_nonneg := hH.c_nonneg
  c_symm := hH.c_symm
  adj_mem := hH.adj_mem
  adj_ne := hH.adj_ne
  adj_inter := hH.adj_inter

/-- The inclusion `C_GMS → C_sing`. -/
def toSing (H : GMSSpace) : SingSpace := ⟨H.1, isSingConfiguration_of_isCellConfiguration H.2⟩

@[simp] theorem toSing_val (H : GMSSpace) : (toSing H).1 = H.1 := rfl

theorem toSing_injective : Function.Injective toSing := by
  intro H H' h
  have h' : (toSing H).1 = (toSing H').1 := congrArg Subtype.val h
  exact Subtype.ext h'

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.toSing_injective
