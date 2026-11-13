import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# Domination by product measures: statements

The two domination statements of T. M. Liggett, R. H. Schonmann and A. M. Stacey,
*Domination by product measures*, Ann. Probab. 25 (1997), stated over the
vocabulary of `LatticeProb.Percolation.LSS.Basic`:

* `LiggettSchonmannStacey`: Theorem 0.0 (i) and (ii) for fields of bits on `ℤ^d`
  with finite-range dependence.
* `LiggettSchonmannStaceyBoundedDegree`: Corollary 1.4 together with Theorem 1.3
  for fields of bits whose dependence graph has bounded degree.

Both are stated as propositions. They are not proved in this file.
-/

namespace LatticeProb.Percolation.LSS

open LatticeProb MeasureTheory

/-- **Theorem 0.0 (i) and (ii)** of Liggett, Schonmann and Stacey, *Domination by
product measures*, Ann. Probab. 25 (1997).

For each `d` and `k`, when `p` is large enough every `k`-dependent field of bits on
`ℤ^d` whose one-site probabilities are at least `p` is dominated from below by the
product field of some density `ρ(d, k, p)`, and `ρ(d, k, p)` can be made arbitrarily
close to `1` by taking `p` large enough.

Domination from below is stated through increasing events: every measurable
increasing event has no larger probability under the product field than under the
given field. -/
def LiggettSchonmannStacey : Prop :=
  ∀ d k : ℕ, 1 ≤ d → ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
    ∃ p : ℝ, p < 1 ∧ ∀ μ : Measure (Site d → Bool), IsProbabilityMeasure μ →
      KDependent k μ → (∀ s : Site d, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
      ∀ A : Set (Site d → Bool), MeasurableSet A → IsIncreasingEvent A →
        sitePercolation d ρ A ≤ μ A

/-- **Corollary 1.4** of Liggett, Schonmann and Stacey, *Domination by product
measures*, Ann. Probab. 25 (1997), with Theorem 1.3 of the same paper.

Let `G` be a graph with a countable vertex set `S` in which every vertex has degree
at most `Δ ≥ 1`, and in which every finite connected component contains a vertex of
degree strictly less than `Δ`. Let `G(p)` be the class of laws of fields of bits on
`S` with dependence graph `G` whose one-site probabilities are at least `p`, and let
`σ_G(p)` be the supremum of the densities `ρ` such that every law in `G(p)`
dominates the product law of density `ρ`. Then `σ_G(p) → 1` as `p → 1`.

The limit is stated in the form it is used: for every `ρ < 1` there is `p < 1` such
that every law in `G(p)` dominates the product law of density `ρ`. Domination is
stated through increasing events: every measurable increasing event has no larger
probability under the product law than under the given law. The dependence graph is
stated through finite sets of vertices, which determine the independence of the
generated `σ`-algebras. -/
def LiggettSchonmannStaceyBoundedDegree : Prop :=
  ∀ (S : Type) [Countable S] (G : SimpleGraph S) (Δ : ℕ), 1 ≤ Δ →
    (∀ s : S, (G.neighborSet s).Finite ∧ (G.neighborSet s).ncard ≤ Δ) →
    (∀ s : S, (G.connectedComponentMk s).supp.Finite →
      ∃ t ∈ (G.connectedComponentMk s).supp, (G.neighborSet t).ncard < Δ) →
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∃ p : ℝ, p < 1 ∧ ∀ μ : Measure (S → Bool), IsProbabilityMeasure μ →
        HasDependenceGraph G μ → (∀ s : S, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
        ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A →
          bernoulliProduct S ρ A ≤ μ A

end LatticeProb.Percolation.LSS
