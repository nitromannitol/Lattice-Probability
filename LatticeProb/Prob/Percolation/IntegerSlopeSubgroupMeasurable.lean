import LatticeProb.Prob.Percolation.IntegerSlopeSubgroup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Fixed-slope integer-gradient events

For countably many edges with measurable real coefficient fields, the event that a fixed
slope has integer linear gradients is measurable. This gives no selection of a random slope
and makes no assertion about hitting an uncountable compact set of slopes.
-/

namespace LatticeProb.Prob.Percolation

open scoped BigOperators

variable {Ω ι : Type*} {d : ℕ}

/-- The event that a fixed slope has integer evaluations on every indexed edge. -/
def integerSlopeEvent (g : Ω → ι → Fin d → ℝ) (p : Fin d → ℝ) : Set Ω :=
  {ω | p ∈ integerSlopeSubgroup (g ω)}

/-- The fixed-slope event retains every integer linear-gradient constraint. -/
@[simp] theorem mem_integerSlopeEvent (g : Ω → ι → Fin d → ℝ) (p : Fin d → ℝ) (ω : Ω) :
    ω ∈ integerSlopeEvent g p ↔ ∀ e, ∃ z : ℤ, ∑ j, p j * g ω e j = (z : ℝ) :=
  Iff.rfl

/-- Coordinatewise measurability suffices for the countable fixed-slope event. -/
theorem measurableSet_integerSlopeEvent_of_coordinates [MeasurableSpace Ω] [Countable ι]
    (g : Ω → ι → Fin d → ℝ) (hg : ∀ e j, Measurable (fun ω => g ω e j))
    (p : Fin d → ℝ) : MeasurableSet (integerSlopeEvent g p) := by
  have hedge (e : ι) :
      MeasurableSet {ω | ∃ z : ℤ, ∑ j, p j * g ω e j = (z : ℝ)} := by
    have heval : Measurable (fun ω => ∑ j, p j * g ω e j) :=
      Finset.measurable_sum _ fun j _ => measurable_const.mul (hg e j)
    have hclosed := Int.isClosedEmbedding_coe_real.isClosed_range
    convert hclosed.measurableSet.preimage heval using 1
    ext ω
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  change MeasurableSet {ω | ∀ e, ∃ z : ℤ, ∑ j, p j * g ω e j = (z : ℝ)}
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter hedge

/-- A measurable coefficient field gives a measurable integer-gradient event at each fixed slope. -/
theorem measurableSet_integerSlopeEvent [MeasurableSpace Ω] [Countable ι]
    (g : Ω → ι → Fin d → ℝ)
    (hg : Measurable g) (p : Fin d → ℝ) : MeasurableSet (integerSlopeEvent g p) :=
  measurableSet_integerSlopeEvent_of_coordinates g (fun _ _ => hg.eval.eval) p

/-- Zero random coefficients give the whole sample space for every fixed slope. -/
@[simp] theorem integerSlopeEvent_zero (p : Fin d → ℝ) :
    integerSlopeEvent (fun (_ : Ω) (_ : ι) (_ : Fin d) => (0 : ℝ)) p = Set.univ := by
  ext ω
  simp only [integerSlopeEvent, Set.mem_setOf_eq, integerSlopeSubgroup_zero,
    AddSubgroup.mem_top, Set.mem_univ]

end LatticeProb.Prob.Percolation
