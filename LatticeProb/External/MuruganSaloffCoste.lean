import LatticeProb.Graph.LongRangeKernel.WeightedGraph
import LatticeProb.Graph.LongRangeKernel.Scale

/-!
# The Murugan–Saloff-Coste on-diagonal estimate

This module defines a proposition and does not assert it. The density and induced measure
normalizations are those of the cited discrete-time theorem.
-/

open scoped NNReal ENNReal

namespace LatticeProb.External

open LatticeProb.Graph.LongRangeKernel

/-- **Murugan–Saloff-Coste on-diagonal estimate** (M. Murugan and L. Saloff-Coste, *Anomalous
threshold behavior of long range random walks*, Electron. J. Probab. 20 (2015), no. 74,
Theorem 1.1, estimate (10); standing assumptions (1)–(3), (5)–(7) and (J_φ)).  On an infinite
connected locally finite weighted graph, every symmetric Markov kernel `k` satisfying `(J_φ)`
has `ψ_K(n) = sup_x k_{2n}(x,x) ≍ 1/V(ζ(n))` for every continuous nondecreasing asymptotic
inverse `ζ ≥ 1` of `t^γ / ∫₀^t s^{γ-1}/φ(s) ds`.  The constant is chosen after `ζ` and `k`. -/
def MuruganSaloffCoste : Prop :=
  ∀ (X : Type) (G : WeightedGraph X), Infinite X → G.graph.Connected →
    ∀ (V φ : ℝ → ℝ) (γ : ℝ) (k : X → X → ℝ≥0∞),
    (∃ C_μ : ℝ, 1 ≤ C_μ ∧ ∀ x,
      C_μ⁻¹ ≤ (G.mass x : ℝ) ∧ (G.mass x : ℝ) ≤ C_μ) →
    IsVolumeProfile V →
    (∃ C_h : ℝ, 1 < C_h ∧ ∀ x r, 0 < r →
      ENNReal.ofReal (C_h⁻¹ * V r) ≤ G.volume x r ∧
      G.volume x r ≤ ENNReal.ofReal (C_h * V r)) →
    (∃ p₀ : ℝ, 0 < p₀ ∧ ∀ x y, G.graph.Adj x y →
      p₀ ≤ (G.weight x y : ℝ) / (G.mass x : ℝ)) →
    1 < γ →
    (∃ C : ℝ, 0 < C ∧ ∀ x y (n : ℕ), 1 ≤ n →
      G.heat n x y ≤ ENNReal.ofReal
        (C / V ((n : ℝ) ^ (1 / γ)) *
          Real.exp (-(((G.graph.dist x y : ℝ) ^ γ / (C * n)) ^ (1 / (γ - 1)))))) →
    (∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n → G.graph.dist x y ≤ n →
      ENNReal.ofReal (c / V ((n : ℝ) ^ (1 / γ)) *
        Real.exp (-(((G.graph.dist x y : ℝ) ^ γ / (c * n)) ^ (1 / (γ - 1))))) ≤
          G.heat n x y + G.heat (n + 1) x y) →
    IsJumpScale φ → IsMarkovDensity G.mass k →
    (∀ x y, k x y = k y x) →
    (∃ C_φ : ℝ, 0 < C_φ ∧ ∀ x y,
      ENNReal.ofReal (C_φ⁻¹ / (V (G.graph.dist x y) * φ (G.graph.dist x y))) ≤ k x y ∧
      k x y ≤ ENNReal.ofReal (C_φ / (V (G.graph.dist x y) * φ (G.graph.dist x y)))) →
    ∀ ζ : ℝ → ℝ, IsInverseScale γ φ ζ →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ENNReal.ofReal (C⁻¹ / V (ζ n)) ≤ evenKernelSup G.mass k n ∧
      evenKernelSup G.mass k n ≤ ENNReal.ofReal (C / V (ζ n))

end LatticeProb.External
