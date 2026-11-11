import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Parameter space of circle averages

The circle average `circleAvg h r z` of a whole-plane Gaussian free field is indexed by a radius `r > 0`
and a centre `z ∈ ℂ` (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, 2011, Section 3; Bonanno's
continuous circle-average construction). `CircleParameter` is the parameter space `(0, ∞) × ℂ` of this family,
with the product topology and the Borel σ-algebra. A continuous version of the family is a continuous map
`CircleParameter → ℝ`, i.e. an element of `C(CircleParameter, ℝ)`.
-/

namespace LatticeProb

open MeasureTheory

noncomputable section

/-- The parameter space `(0, ∞) × ℂ` of the circle averages `(r, z) ↦ circleAvg h r z`. -/
abbrev CircleParameter := Set.Ioi (0 : ℝ) × ℂ

/-- `(0, ∞)` is locally compact, being an open subset of `ℝ`. -/
instance : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

-- The Borel σ-algebra of the parameter space is the product of the Borel σ-algebras.
example : MeasurableSpace CircleParameter := inferInstance

example : BorelSpace CircleParameter := inferInstance

end

end LatticeProb
