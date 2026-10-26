import LatticeProb.Prob.BernoulliFiniteFlip
import LatticeProb.Prob.Percolation.LatticeBondProbability

/-!
# Conull events stable under finite bond flips

For the canonical Bernoulli law on genuine unordered nearest-neighbor bonds, every
measurable conull event contains a measurable conull event stable under finite flips.
The stable event is the literal intersection over all finite sets of bonds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory

variable {d : ℕ}

/-- Flip precisely a finite set of genuine unordered lattice bonds. -/
noncomputable abbrev finiteBondFlip (F : Finset (Bond d)) (ω : Configuration d) :
    Configuration d := BernoulliFiniteFlip.flip F ω

/-- Configurations all of whose finite bond flips belong to the given event. -/
def allFiniteBondFlipsEvent (A : Set (Configuration d)) : Set (Configuration d) :=
  {ω | ∀ F : Finset (Bond d), finiteBondFlip F ω ∈ A}

/-- The literal simultaneous finite-bond-flip event is measurable. -/
theorem measurableSet_allFiniteBondFlipsEvent {A : Set (Configuration d)}
    (hA : MeasurableSet A) : MeasurableSet (allFiniteBondFlipsEvent A) :=
  BernoulliFiniteFlip.measurableSet_all_flips hA

/-- Every measurable conull event holds after all finite flips under the actual bond law. -/
theorem latticeBondLaw_allFiniteBondFlipsEvent (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {A : Set (Configuration d)} (hA : MeasurableSet A) (hfull : latticeBondLaw d p A = 1) :
    latticeBondLaw d p (allFiniteBondFlipsEvent A) = 1 :=
  BernoulliFiniteFlip.full_product_all_flips p hp0 hp1 hA hfull

/-- The simultaneous event is stable under every finite bond flip at every point. -/
theorem finiteBondFlip_mem_allFiniteBondFlipsEvent {A : Set (Configuration d)}
    {ω : Configuration d} (hω : ω ∈ allFiniteBondFlipsEvent A) (F : Finset (Bond d)) :
    finiteBondFlip F ω ∈ allFiniteBondFlipsEvent A :=
  BernoulliFiniteFlip.all_flips_stable hω F

/-- The simultaneous finite-flip event is contained in the original event. -/
theorem allFiniteBondFlipsEvent_subset (A : Set (Configuration d)) :
    allFiniteBondFlipsEvent A ⊆ A :=
  BernoulliFiniteFlip.all_flips_subset A

end LatticeProb.Percolation
