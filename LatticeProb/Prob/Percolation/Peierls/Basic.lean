/-
# Bernoulli site percolation

The site law and infinite-cluster vocabulary of Exploding-Sandpiles,
`Exploding/Support/Percolation.lean`, together with bridges to the Bernoulli
product law and the measurable lattice component event.  See also Mathieu,
*Quenched invariance principles for random walks with random conductances*,
Section 5.1 (arXiv:math/0611613), for the site percolation convention.
-/
import LatticeProb.Prob.Percolation.InfiniteClusterZeroOne
import LatticeProb.Prob.Percolation.LSSThinComplement

open MeasureTheory

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- The law of one Bernoulli bit with real parameter `q`. -/
noncomputable def bitLaw (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

/-- Independent Bernoulli site percolation on `ℤ^d`. -/
noncomputable def sitePercolation (d : ℕ) (q : ℝ) : Measure (Site d → Bool) :=
  Measure.infinitePi fun _ : Site d => bitLaw q

/-- The open sites of a configuration. -/
def openSites (ω : Site d → Bool) : Set (Site d) := {x | ω x = true}

/-- An infinite nearest-neighbour component of the open sites. -/
def IsInfiniteOpenCluster (ω : Site d → Bool) (C : Set (Site d)) : Prop :=
  C.Infinite ∧ ∃ i ∈ C, C = componentIn (openSites ω) i

/-- The independent Bernoulli product law indexed by `S`. -/
noncomputable def bernoulliProduct (S : Type) (q : ℝ) : Measure (S → Bool) :=
  Measure.infinitePi fun _ : S => bitLaw q

@[simp] theorem bitLaw_true (q : ℝ) : bitLaw q {true} = ENNReal.ofReal q := by
  simp [bitLaw]

@[simp] theorem bitLaw_false (q : ℝ) : bitLaw q {false} = ENNReal.ofReal (1 - q) := by
  simp [bitLaw]

set_option linter.deprecated false in
/-- The source bit law is LP's Bernoulli law at a valid parameter. -/
theorem bitLaw_eq_bernoulli (p : NNReal) (hp : p ≤ 1) :
    bitLaw p = bernoulli p hp := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [bernoulli, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.bernoulli_apply hp]
  cases b with
  | false =>
      simp only [Bool.cond_false, bitLaw_false]
      rw [ENNReal.ofReal_sub (1 : ℝ) (NNReal.coe_nonneg p), ENNReal.ofReal_one]
      simp
  | true => simp

/-- The real-parameter product law agrees with LP's Bernoulli field. -/
theorem bernoulliProduct_eq_bitProduct (S : Type) (p : NNReal) (hp : p ≤ 1) :
    bernoulliProduct S p = bitProduct p hp S := by
  unfold bernoulliProduct bitProduct
  congr 1
  funext _
  exact bitLaw_eq_bernoulli p hp

@[simp] theorem sitePercolation_eq_bernoulliProduct (d : ℕ) (q : ℝ) :
    sitePercolation d q = bernoulliProduct (Site d) q := rfl

/-- Bernoulli site percolation on the planar lattice at a valid parameter. -/
noncomputable def sitePercolationLaw (p : NNReal) (hp : p ≤ 1) :
    Measure (Site 2 → Bool) :=
  Measure.infinitePi fun _ : Site 2 => bernoulli p hp

/-- The planar law agrees with the real-parameter site law. -/
theorem sitePercolation_eq_sitePercolationLaw (p : NNReal) (hp : p ≤ 1) :
    sitePercolation 2 p = sitePercolationLaw p hp := by
  rw [sitePercolation_eq_bernoulliProduct, bernoulliProduct_eq_bitProduct (Site 2) p hp]
  rfl

/-- The source cluster event is the lattice infinite-component event. -/
theorem exists_infiniteOpenCluster_iff (ω : Site d → Bool) :
    (∃ C, IsInfiniteOpenCluster ω C) ↔ HasInfiniteComponent (openSites ω) := by
  constructor
  · rintro ⟨C, hC, i, hi, rfl⟩
    obtain ⟨hiopen, _, _⟩ := hi
    exact ⟨i, hiopen, hC⟩
  · rintro ⟨i, hi, hinf⟩
    exact ⟨componentIn (openSites ω) i, hinf, i, ⟨hi, hi, SimpleGraph.Reachable.rfl⟩, rfl⟩

/-- The event that some open cluster is infinite is measurable. -/
theorem measurableSet_exists_infiniteOpenCluster (d : ℕ) :
    MeasurableSet {ω : Site d → Bool | ∃ C, IsInfiniteOpenCluster ω C} := by
  have heq : {ω : Site d → Bool | ∃ C, IsInfiniteOpenCluster ω C} =
      {ω : Site d → Bool | HasInfiniteComponent {v | ω v = true}} := by
    ext ω
    exact exists_infiniteOpenCluster_iff ω
  rw [heq]
  exact GraphPercolation.measurableSet_hasInfiniteComponent d

end LatticeProb.Percolation
