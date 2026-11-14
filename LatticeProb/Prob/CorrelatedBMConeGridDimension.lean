import LatticeProb.Analysis.FactorialGridNeighborhoods
import LatticeProb.Prob.CorrelatedBMConeGridEvents
import LatticeProb.Prob.PointwiseSelectedHausdorffDimension

/-!
# Cone-vector dimension from factorial-grid estimates

A uniform expected covering cost at each reciprocal horizon bounds the
Hausdorff dimension of separated Brownian cone vectors.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A finite expected covering cost at every horizon bounds the separated
cone-vector set. The finite bound may depend on the horizon. -/
theorem ae_dimH_backwardConeVectors_le_of_grid_cost
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C d q direction : ℝ) (hC : 0 < C) (hd : 0 < d) (hq : 0 < q)
    (hdir : direction = 1 ∨ direction = -1)
    (hcost : ∀ k : ℕ, ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n : ℕ,
      (∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
          μ (factorialConeGridEvent direction C α k n ij.1 ij.2)) ≤ K) :
    ∀ᵐ ω ∂μ,
      dimH {p : ℝ × ℝ |
        let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
        let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
        p ∈ backwardConeVectors X Y ∧ 0 < p.1 ∧ p.2 < 1 ∧
          d < p.2 - p.1 ∧ q < p.2 - coneFirstExitBackward X Y p.2} ≤ β := by
  classical
  let S : Path2 → Set (ℝ × ℝ) := fun ω => {p |
    let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
    let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
    p ∈ backwardConeVectors X Y ∧ 0 < p.1 ∧ p.2 < 1 ∧
      d < p.2 - p.1 ∧ q < p.2 - coneFirstExitBackward X Y p.2}
  let A : ℕ → Set Path2 := fun k => {ω | ∀ p ∈ S ω, ∀ᶠ n : ℕ in atTop,
    ∃ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
      p ∈ factorialGridNeighborhood n ij.1 ij.2 ∧
      ω ∈ factorialConeGridEvent direction C α k n ij.1 ij.2}
  have hdim : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ A k → dimH (S ω) ≤ β := by
    intro k
    obtain ⟨K, hK, hcostk⟩ := hcost k
    apply ae_dimH_le_of_pointwise_selected_finite_cover
      (ι := fun n => Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6))
      (μ := μ) (K := K) β hβ S (A k)
      (fun n ij => factorialGridNeighborhood n ij.1 ij.2)
      (fun n ij => factorialConeGridEvent direction C α k n ij.1 ij.2)
      (fun n ij => measurableSet_factorialConeGridEvent direction C α k n ij.1 ij.2)
      (fun n => ENNReal.ofReal (2 * factorialGridMesh n))
      tendsto_factorialGridNeighborhood_diameter
      (fun n ij => ediam_factorialGridNeighborhood_le n ij.1 ij.2)
    · intro ω hω p hp
      filter_upwards [hω p hp] with n hn
      obtain ⟨ij, hpij, hevent⟩ := hn
      exact mem_iUnion.2 ⟨ij, by simpa only [hevent, ite_true] using hpij⟩
    · exact hK
    · exact hcostk
  filter_upwards [ae_all_iff.2 hdim, ae_factorial_backwardConeVector_grid_events hμ] with ω hdimω hgrid
  obtain ⟨k, hk⟩ := hgrid α hα C d q hC hd hq direction hdir
  apply hdimω k
  intro p hp
  obtain ⟨hv, ha, hs, hsep, hgap⟩ := hp
  filter_upwards [hk p.1 p.2 hv ha hs hsep hgap] with n hn
  obtain ⟨i, j, _, _, _, ha', hs', hevent⟩ := hn
  refine ⟨(i, j), ?_, hevent⟩
  apply mem_factorialGridNeighborhood n i j p.1 p.2
  · simpa only [factorialGridMesh, abs_sub_comm] using ha'
  · simpa only [factorialGridMesh, abs_sub_comm] using hs'

end LatticeProb.CorrelatedBM
