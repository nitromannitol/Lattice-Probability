/-
Independent, identically distributed fields on the lattice, and the law of a
site-indexed family of instruction stacks.
-/
import LatticeProb.Site

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- The law of an i.i.d. field on `ℤ^d` with one-site law `μ`. -/
noncomputable def iidLaw (d : ℕ) {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Measure (Site d → α) :=
  Measure.infinitePi fun _ : Site d => μ

/-- One instruction at `y`: a uniformly chosen neighbour. -/
noncomputable def instructionLaw {d : ℕ} (y : Site d) : Measure (Site d) :=
  ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum fun i : Fin d =>
    Measure.dirac (y + unit i) + Measure.dirac (y - unit i)

/-- The law of independent instruction stacks, one at each site. -/
noncomputable def stackLaw (d : ℕ) : Measure (Site d × ℕ → Site d) :=
  Measure.infinitePi fun p : Site d × ℕ => instructionLaw p.1

/-- `I_{y,x}(m)`: how many of the first `m` instructions at `y` point at `x`. -/
def arrivals {d : ℕ} (stack : Site d × ℕ → Site d) (y x : Site d) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun j => stack (y, j) = x).card

end LatticeProb
