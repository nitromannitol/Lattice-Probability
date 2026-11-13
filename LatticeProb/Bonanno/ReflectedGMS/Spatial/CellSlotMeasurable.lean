/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.CellSlotMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Code
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measurability of cell membership and of code slots

These are the joint-measurability facts about the Hausdorff Borel structure on cells and about
reading a code slot.  They were originally proved inside `Spatial/NullBoundaryRoots.lean`; they are
collected here, **unchanged and in the same namespace**, so that the two mass-transport arguments
that need them — the frontier transport of `NullBoundaryRoots` and the uncovered transport of
`Spatial/UncoveredRootTransport.lean` — can both use them without one file importing the other.

Moving a declaration to an earlier file in the same namespace is invisible to consumers: every
fully-qualified name is unchanged, and `NullBoundaryRoots` imports this file.
-/

set_option autoImplicit false
-- `isClosed_cellMem` elaborates the joint continuity of `Metric.infDist` on `NonemptyCompacts`,
-- which exceeds the default budget; this is the limit the original host module used.
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace

namespace ReflectedGMS.Spatial

open Code

/-! ### Joint measurability of cell membership -/

/-- Cell membership is a closed condition in the pair (cell, point), because the
distance to a nonempty compact set is jointly continuous. -/
theorem isClosed_cellMem :
    IsClosed {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} := by
  have hswap : Continuous fun p : CompactCell × Plane => (p.2, p.1) :=
    continuous_snd.prodMk continuous_fst
  have hlip : Continuous fun p : Plane × CompactCell => Metric.infDist p.1 (p.2 : Set Plane) :=
    (NonemptyCompacts.lipschitz_infDist (α := Plane)).continuous
  have hcont : Continuous fun p : CompactCell × Plane =>
      Metric.infDist p.2 (p.1 : Set Plane) := hlip.comp hswap
  have hset : {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)}
      = (fun p : CompactCell × Plane => Metric.infDist p.2 (p.1 : Set Plane)) ⁻¹' {0} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
    exact p.1.isCompact.isClosed.mem_iff_infDist_zero p.1.nonempty
  rw [hset]
  exact isClosed_singleton.preimage hcont

theorem measurableSet_cellMem :
    MeasurableSet {p : CompactCell × Plane | p.2 ∈ (p.1 : Set Plane)} :=
  isClosed_cellMem.measurableSet

/-! ### Reading a code slot measurably -/

/-- A fixed reference cell, used only to read a present code slot measurably. -/
def referenceCell : CompactCell :=
  ⟨⟨{0}, isCompact_singleton⟩, singleton_nonempty 0⟩

theorem continuous_slotCell :
    Continuous fun o : Option CompactCell => o.getD referenceCell := by
  have hEq : (fun o : Option CompactCell => o.getD referenceCell)
      = (Sum.elim id fun _ : PUnit.{1} => referenceCell) ∘ slotEquiv := by
    funext o
    cases o <;> rfl
  rw [hEq]
  exact (Continuous.sumElim continuous_id continuous_const).comp continuous_induced_dom

theorem continuous_slotIsSome :
    Continuous fun o : Option CompactCell => o.isSome := by
  have hEq : (fun o : Option CompactCell => o.isSome)
      = (Sum.elim (fun _ : CompactCell => true) fun _ : PUnit.{1} => false) ∘ slotEquiv := by
    funext o
    cases o <;> rfl
  rw [hEq]
  exact (Continuous.sumElim continuous_const continuous_const).comp continuous_induced_dom

theorem measurableSet_slotIsSome :
    MeasurableSet {o : Option CompactCell | o.isSome} := by
  have hpre : {o : Option CompactCell | o.isSome}
      = (fun o : Option CompactCell => o.isSome) ⁻¹' {true} := by
    ext o
    simp
  have hopen : IsOpen {o : Option CompactCell | o.isSome} := by
    rw [hpre]
    exact (isOpen_discrete _).preimage continuous_slotIsSome
  exact hopen.measurableSet

theorem measurable_slotCell :
    Measurable fun o : Option CompactCell => (o.getD referenceCell : CompactCell) :=
  continuous_slotCell.measurable

end ReflectedGMS.Spatial
