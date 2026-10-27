import LatticeProb.Prob.Percolation.ContinuumGreen
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeBondCritical

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal Classical

namespace LatticeProb.External

/-- The value estimates for the infinite-cluster Green function of Dario and Gu,
with an existential positive conductivity. -/
def SupercriticalBondGreenQuantitative : Prop :=
  ∀ (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ κ : ℝ, ∃ hκ : 0 < κ,
      (d = 2 →
        ∃ K : Vertex d → Configuration d → ℝ,
          (∀ y, Measurable (K y)) ∧
          ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
            ∀ y : Vertex d,
              (∀ R : ℝ, 0 ≤ R →
                latticeBondLaw d p {ω | R ≤ |K y ω|} ≤
                  ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
              ∃ M : Configuration d → ℝ,
                Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
                (∀ R : ℝ, 0 ≤ R →
                  latticeBondLaw d p {ω | R ≤ M ω} ≤
                    ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
                ∀ᵐ ω ∂latticeBondLaw d p,
                  ∀ h : HasUniqueInfiniteOpenComponent ω,
                    ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                      ∀ g : uniqueInfiniteComponent h → ℝ,
                        IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                        (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
                          ∀ x : uniqueInfiniteComponent h,
                            ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                              z.val = latticeEuclideanEmbedding x.val -
                                latticeEuclideanEmbedding y →
                              R ≤ ‖latticeEuclideanEmbedding x.val‖ →
                              |g x - continuumGreen d hd ⟨κ, hκ⟩ z - K y ω| ≤ ε) ∧
                        ∀ x : uniqueInfiniteComponent h,
                          ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                            z.val = latticeEuclideanEmbedding x.val -
                              latticeEuclideanEmbedding y →
                            M ω ≤ ‖z.val‖ →
                            |g x - continuumGreen d hd ⟨κ, hκ⟩ z - K y ω| ≤
                              C / Real.rpow ‖z.val‖ (1 - δ)) ∧
      (3 ≤ d →
        ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
          ∀ y : Vertex d, ∃ M : Configuration d → ℝ,
            Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
            (∀ R : ℝ, 0 ≤ R →
              latticeBondLaw d p {ω | R ≤ M ω} ≤
                ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
            ∀ᵐ ω ∂latticeBondLaw d p,
              ∀ h : HasUniqueInfiniteOpenComponent ω,
                ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                  ∀ g : uniqueInfiniteComponent h → ℝ,
                    IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                    ∀ x : uniqueInfiniteComponent h,
                      ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                        z.val = latticeEuclideanEmbedding x.val -
                          latticeEuclideanEmbedding y →
                        M ω ≤ ‖z.val‖ →
                        |g x - continuumGreen d hd ⟨κ, hκ⟩ z| ≤
                          C / (Real.rpow ‖z.val‖ (1 - δ) *
                            ‖z.val‖ ^ (d - 2)))

end LatticeProb.External
