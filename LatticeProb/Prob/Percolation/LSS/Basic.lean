import LatticeProb.Site
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Bernoulli percolation: vocabulary

The vocabulary of Bernoulli site and bond percolation on `ℤ^d`: the product law of
the occupation variables, open clusters, bond percolation and its critical
probability, increasing events, finite-range dependence of a field of bits on
`ℤ^d`, and fields of bits indexed by the vertices of a graph with a given
dependence graph.
-/

namespace LatticeProb.Percolation.LSS

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The law of one Bernoulli(`q`) bit: `true` with probability `q` and `false`
with probability `1 - q`. -/
noncomputable def bitLaw (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

/-- Bernoulli site percolation of density `q` on `ℤ^d`: the product law of
independent bits, each `true` (the site is open) with probability `q`. -/
noncomputable def sitePercolation (d : ℕ) (q : ℝ) : Measure (Site d → Bool) :=
  Measure.infinitePi fun _ : Site d => bitLaw q

/-- The open sites of a configuration of bits. -/
def openSites (ω : Site d → Bool) : Set (Site d) := {x | ω x = true}

/-- `C` is an infinite open cluster of `ω`: an infinite nearest-neighbour
component of the open sites. -/
def IsInfiniteOpenCluster (ω : Site d → Bool) (C : Set (Site d)) : Prop :=
  C.Infinite ∧ ∃ i ∈ C, C = componentIn (openSites ω) i

/-- A set of configurations of bits is increasing: opening more sites keeps a
configuration in it. -/
def IsIncreasingEvent (A : Set (Site d → Bool)) : Prop :=
  ∀ ω ω' : Site d → Bool, ω ∈ A → (∀ z, ω z = true → ω' z = true) → ω' ∈ A

/-- The field of bits with law `μ` is `k`-dependent: its restrictions to two
finite sets of sites at `ℓ^∞`-distance more than `k` from each other are
independent. -/
def KDependent (k : ℕ) (μ : Measure (Site d → Bool)) : Prop :=
  ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, ∃ l, (k : ℤ) < |a l - b l|) →
    ProbabilityTheory.IndepFun (fun ω : Site d → Bool => fun i : I => ω i)
      (fun ω : Site d → Bool => fun j : J => ω j) μ

/-! ### Bond percolation -/

/-- Bernoulli bond percolation of density `q` on `ℤ^d`: the bond joining `x` and
`x + e_i` is open when the bit indexed by `(x, i)` is `true`, independently with
probability `q`. -/
noncomputable def bondPercolation (d : ℕ) (q : ℝ) : Measure (Site d × Fin d → Bool) :=
  Measure.infinitePi fun _ : Site d × Fin d => bitLaw q

/-- The graph on `ℤ^d` of the open bonds of a configuration. -/
def openBondGraph (ω : Site d × Fin d → Bool) : SimpleGraph (Site d) :=
  SimpleGraph.fromRel fun x y => ∃ i : Fin d, y = x + unit i ∧ ω (x, i) = true

/-- The percolation probability `θ(q)`: the probability that the open cluster of
the origin is infinite. -/
noncomputable def bondTheta (d : ℕ) (q : ℝ) : ENNReal :=
  bondPercolation d q {ω | {x : Site d | (openBondGraph ω).Reachable 0 x}.Infinite}

/-- The critical probability of bond percolation, `p_c = sup {q : θ(q) = 0}`,
the supremum taken over `0 ≤ q ≤ 1`. -/
noncomputable def bondCritical (d : ℕ) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ bondTheta d q = 0}

/-! ### Fields of bits on a graph -/

/-- The product law of independent Bernoulli(`q`) bits indexed by `S`. -/
noncomputable def bernoulliProduct (S : Type) (q : ℝ) : Measure (S → Bool) :=
  Measure.infinitePi fun _ : S => bitLaw q

/-- A set of configurations of bits indexed by `S` is increasing: turning more
bits on keeps a configuration in it. -/
def IsIncreasingSet {S : Type} (A : Set (S → Bool)) : Prop :=
  ∀ ω ω' : S → Bool, ω ∈ A → (∀ s, ω s = true → ω' s = true) → ω' ∈ A

/-- The law `μ` of a field of bits indexed by the vertices of `G` has dependence
graph `G`: its restrictions to two disjoint finite sets of vertices with no edge
of `G` between them are independent. -/
def HasDependenceGraph {S : Type} (G : SimpleGraph S) (μ : Measure (S → Bool)) : Prop :=
  ∀ I J : Finset S, Disjoint I J → (∀ a ∈ I, ∀ b ∈ J, ¬ G.Adj a b) →
    ProbabilityTheory.IndepFun (fun ω : S → Bool => fun i : I => ω i)
      (fun ω : S → Bool => fun j : J => ω j) μ

end LatticeProb.Percolation.LSS
