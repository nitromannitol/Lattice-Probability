import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Weighted graphs and heat densities

Edge weights induce the vertex measure. Kernel powers are formed with nonnegative extended
real sums, so divergent sums never acquire the default real value zero.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

noncomputable section

variable {X : Type*}

/-- Nonnegative symmetric weights supported exactly on the edges of a simple graph. -/
structure WeightedGraph (X : Type*) where
  graph : SimpleGraph X
  locallyFinite : graph.LocallyFinite
  weight : X → X → ℝ≥0
  symmetric : ∀ x y, weight x y = weight y x
  positive_iff : ∀ x y, 0 < weight x y ↔ graph.Adj x y

attribute [instance] WeightedGraph.locallyFinite

/-- The induced vertex mass, with each incident edge counted once. -/
def WeightedGraph.mass (G : WeightedGraph X) (x : X) : ℝ≥0 :=
  ∑ y ∈ G.graph.neighborFinset x, G.weight x y

/-- The closed graph-distance ball; connectedness rules out the disconnected-distance value. -/
def WeightedGraph.ball (G : WeightedGraph X) (x : X) (r : ℝ) : Set X :=
  {y | (G.graph.dist x y : ℝ) ≤ r}

/-- Closed-ball volume with the induced vertex masses. -/
def WeightedGraph.volume (G : WeightedGraph X) (x : X) (r : ℝ) : ℝ≥0∞ :=
  by
    classical
    exact ∑' y, if y ∈ G.ball x r then (G.mass y : ℝ≥0∞) else 0

/-- A density is Markov when its integral in the destination variable is one. -/
def IsMarkovDensity (m : X → ℝ≥0) (k : X → X → ℝ≥0∞) : Prop :=
  ∀ x, ∑' y, k x y * (m y : ℝ≥0∞) = 1

/-- The density of the identity operator with respect to vertex mass. -/
def identityDensity (m : X → ℝ≥0) (x y : X) : ℝ≥0∞ :=
  by
    classical
    exact if x = y then (m y : ℝ≥0∞)⁻¹ else 0

/-- Iterated densities use convolution against the same vertex measure at every step. -/
def densityPower (m : X → ℝ≥0) (k : X → X → ℝ≥0∞) : ℕ → X → X → ℝ≥0∞
  | 0 => identityDensity m
  | n + 1 => fun x y => ∑' z, k x z * densityPower m k n z y * (m z : ℝ≥0∞)

/-- The reference nearest-neighbour density is `P(x,y) / μ(y)`. -/
def WeightedGraph.referenceDensity (G : WeightedGraph X) (x y : X) : ℝ≥0∞ :=
  (G.weight x y : ℝ≥0∞) / ((G.mass x : ℝ≥0∞) * (G.mass y : ℝ≥0∞))

/-- The natural density is symmetric for the induced measure. -/
theorem WeightedGraph.referenceDensity_symmetric (G : WeightedGraph X) (x y : X) :
    G.referenceDensity x y = G.referenceDensity y x := by
  unfold WeightedGraph.referenceDensity
  rw [G.symmetric x y, mul_comm]

/-- A connected graph with more than one vertex has strictly positive induced masses. -/
theorem WeightedGraph.mass_pos [Nontrivial X] (G : WeightedGraph X)
    (hconn : G.graph.Connected) (x : X) : 0 < G.mass x := by
  classical
  obtain ⟨y, hy⟩ := exists_ne x
  obtain ⟨z, hz⟩ := (hconn x y).nonempty_neighborSet_left hy.symm
  have hzmem : z ∈ G.graph.neighborFinset x := (G.graph.mem_neighborFinset x z).mpr hz
  exact lt_of_lt_of_le ((G.positive_iff x z).mpr hz)
    (Finset.single_le_sum (fun _ _ => zero_le) hzmem)

/-- The natural walk's time-`n` heat density. -/
def WeightedGraph.heat (G : WeightedGraph X) : ℕ → X → X → ℝ≥0∞ :=
  densityPower G.mass G.referenceDensity

/-- The actual supremum of the even-time diagonal heat density, including time zero. -/
def evenKernelSup (m : X → ℝ≥0) (k : X → X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, densityPower m k (2 * n) x x

/-- The identity density has total mass one whenever every vertex mass is positive. -/
theorem identityDensity_isMarkov (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0) :
    IsMarkovDensity m (identityDensity m) := by
  classical
  intro x
  simp only [identityDensity, ite_mul, zero_mul, tsum_ite_eq']
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hm x) ENNReal.coe_ne_top

/-- At time zero, a positive-mass vertex has diagonal density exactly its inverse mass. -/
theorem densityPower_zero_self (m : X → ℝ≥0) (k : X → X → ℝ≥0∞) (x : X) :
    densityPower m k 0 x x = (m x : ℝ≥0∞)⁻¹ := by
  simp only [densityPower, identityDensity, ite_true]

/-- Convolution powers preserve the Markov normalization against the same vertex masses. -/
theorem densityPower_isMarkov (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (k : X → X → ℝ≥0∞) (hk : IsMarkovDensity m k) (n : ℕ) :
    IsMarkovDensity m (densityPower m k n) := by
  induction n with
  | zero => exact identityDensity_isMarkov m hm
  | succ n ih =>
    intro x
    calc
      (∑' y, densityPower m k (n + 1) x y * (m y : ℝ≥0∞)) =
          ∑' y, ∑' z, (k x z * (m z : ℝ≥0∞)) *
            (densityPower m k n z y * (m y : ℝ≥0∞)) := by
        apply tsum_congr
        intro y
        rw [densityPower, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro z
        ac_rfl
      _ = ∑' z, (k x z * (m z : ℝ≥0∞)) *
          ∑' y, densityPower m k n z y * (m y : ℝ≥0∞) := by
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro z
        exact ENNReal.tsum_mul_left
      _ = 1 := by
        have hrow : ∀ z, ∑' y, densityPower m k n z y * (m y : ℝ≥0∞) = 1 := ih
        simpa only [hrow, mul_one] using hk x

/-- Each Markov density entry is finite at a positive-mass destination. -/
theorem IsMarkovDensity.entry_lt_top {m : X → ℝ≥0} {k : X → X → ℝ≥0∞}
    (hk : IsMarkovDensity m k) (x y : X) (hy : m y ≠ 0) : k x y < ⊤ := by
  have hterm : k x y * (m y : ℝ≥0∞) ≤ 1 := by
    have h := ENNReal.le_tsum (f := fun z => k x z * (m z : ℝ≥0∞)) y
    rwa [hk x] at h
  by_contra h
  have htop : k x y = ⊤ := not_lt_top_iff.mp h
  have hm : (m y : ℝ≥0∞) ≠ 0 := by exact_mod_cast hy
  rw [htop, ENNReal.top_mul hm] at hterm
  exact (not_le_of_gt (by simp : (1 : ℝ≥0∞) < ⊤)) hterm

end

end LatticeProb.Graph.LongRangeKernel
