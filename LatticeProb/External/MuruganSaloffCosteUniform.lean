import LatticeProb.External.MuruganSaloffCoste
import LatticeProb.Graph.LongRangeKernel.LatticeDistance
import LatticeProb.Graph.LongRangeKernel.LatticeGaussianLower
import LatticeProb.Graph.LongRangeKernel.CriticalAsymptotics

/-!
# Uniform constants in the Murugan–Saloff-Coste estimate

This module formulates a cited input as a proposition and proves its implication to the
literal input and its application to the normalized lattice. The estimate's constant is
chosen after the common jump comparison constant and before the admissible kernels.
-/

open scoped NNReal ENNReal

namespace LatticeProb.External

open LatticeProb LatticeProb.Graph.LongRangeKernel

/-- M. Murugan and L. Saloff-Coste, *Anomalous threshold behavior of long range random walks*,
Electron. J. Probab. 20 (2015), no. 74, Theorem 1.1, with constant dependence traced in its proof.
The standing assumptions are (1)–(3), (5)–(7), and the kernel comparison is `(J_φ)`.
For fixed graph, profiles, exponent, inverse scale and comparison constant `C_φ`, one constant
bounds the even-time diagonal supremum for every admissible kernel, including at time zero.
This proposition is an assumption formulation; this module does not prove the cited input. -/
def MuruganSaloffCosteUniform : Prop :=
  ∀ (X : Type) (G : WeightedGraph X), Infinite X → G.graph.Connected →
    ∀ (V φ : ℝ → ℝ) (γ : ℝ),
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
    IsJumpScale φ →
    ∀ ζ : ℝ → ℝ, IsInverseScale γ φ ζ →
    ∀ C_φ : ℝ, 0 < C_φ →
    ∃ C : ℝ, 0 < C ∧ ∀ k : X → X → ℝ≥0∞, IsMarkovDensity G.mass k →
      (∀ x y, k x y = k y x) →
      (∀ x y,
        ENNReal.ofReal (C_φ⁻¹ / (V (G.graph.dist x y) * φ (G.graph.dist x y))) ≤ k x y ∧
        k x y ≤ ENNReal.ofReal (C_φ / (V (G.graph.dist x y) * φ (G.graph.dist x y)))) →
      ∀ n : ℕ,
        ENNReal.ofReal (C⁻¹ / V (ζ n)) ≤ evenKernelSup G.mass k n ∧
        evenKernelSup G.mass k n ≤ ENNReal.ofReal (C / V (ζ n))

/-- The uniform cited input implies the literal input by choosing a kernel's comparison
constant before applying the uniform estimate. -/
theorem uniform_implies_literal (h : MuruganSaloffCosteUniform) : MuruganSaloffCoste := by
  intro X G hinf hconn V φ γ k hμ hV hh hp hγ hup hlow hφ hk hsymm hJ ζ hζ
  obtain ⟨C_φ, hCφ, hJ'⟩ := hJ
  obtain ⟨C, hC, hbound⟩ :=
    h X G hinf hconn V φ γ hμ hV hh hp hγ hup hlow hφ ζ hζ C_φ hCφ
  exact ⟨C, hC, hbound k hk hsymm hJ'⟩

/-- On the normalized lattice, the proved volume and Gaussian estimates discharge every
reference-graph antecedent, leaving the cited input and the kernel's source conditions. -/
theorem lattice_uniform_estimate (h : MuruganSaloffCosteUniform) {d : ℕ} (hd : 0 < d)
    (C_φ : ℝ) (hC_φ : 0 < C_φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Site d → Site d → ℝ≥0∞,
      IsMarkovDensity (weightedLattice d hd).mass k → (∀ x y, k x y = k y x) →
      (∀ x y,
        ENNReal.ofReal (C_φ⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
          quadraticScale ((lattice d).dist x y))) ≤ k x y ∧
        k x y ≤ ENNReal.ofReal (C_φ / (latticeVolumeProfile d ((lattice d).dist x y) *
          quadraticScale ((lattice d).dist x y)))) →
      ∀ n : ℕ,
        ENNReal.ofReal (C⁻¹ / latticeVolumeProfile d (criticalInverse n)) ≤
          evenKernelSup (weightedLattice d hd).mass k n ∧
        evenKernelSup (weightedLattice d hd).mass k n ≤
          ENNReal.ofReal (C / latticeVolumeProfile d (criticalInverse n)) :=
  h (Site d) (weightedLattice d hd) (weightedLattice_infinite hd) (weightedLattice_connected hd)
    (latticeVolumeProfile d) quadraticScale 2 (weightedLattice_counting hd)
    (latticeVolumeProfile_isVolumeProfile hd) (weightedLattice_volume_comparable hd)
    (weightedLattice_edge_lower hd) (by norm_num) (weightedLattice_gaussian_upper hd)
    (weightedLattice_gaussian_lower hd) quadraticScale_isJumpScale
    criticalInverse criticalInverse_isInverseScale C_φ hC_φ

/-- At time zero the lattice supremum is exactly one for every kernel, since the induced
vertex measure is counting measure. -/
theorem lattice_evenKernelSup_zero {d : ℕ} (hd : 0 < d)
    (k : Site d → Site d → ℝ≥0∞) :
    evenKernelSup (weightedLattice d hd).mass k 0 = 1 := by
  simp only [evenKernelSup, mul_zero, densityPower_zero_self, weightedLattice_mass,
    ENNReal.coe_one, inv_one, ciSup_const]

end LatticeProb.External
