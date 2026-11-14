import LatticeProb.Prob.CorrelatedBMForwardConeGridEvents
import LatticeProb.Prob.CorrelatedBMConeSeparatedGridDimension
import LatticeProb.Prob.PointwiseSelectedHausdorffDimension

/-!
# Forward cone-vector dimension from separated factorial-grid estimates

A uniform expected covering cost over separated grid pairs at each reciprocal
horizon bounds the Hausdorff dimension of reflected separated forward Brownian cone vectors.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A finite expected separated-pair covering cost at every horizon bounds the separated
reflected forward cone-vector set. The finite bound may depend on the horizon. -/
theorem ae_dimH_reflected_forwardConeVectors_le_of_separated_grid_cost
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C d direction : ℝ) (hC : 0 < C) (hd : 0 < d)
    (hdir : direction = 1 ∨ direction = -1)
    (hcost : ∀ k : ℕ, ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n : ℕ,
      (∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        if d < (ij.2.val : ℝ) / (n.factorial ^ 6 : ℕ) -
            (ij.1.val : ℝ) / (n.factorial ^ 6 : ℕ) then
          Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
            μ (factorialConeGridEvent (-direction) C α k n ij.1 ij.2)
        else 0) ≤ K) :
    ∀ᵐ ω ∂μ,
      dimH {p : ℝ × ℝ |
        let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
        let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
        (-p.1, -p.2) ∈ forwardConeVectors X Y ∧ 0 < p.1 ∧ p.2 < 1 ∧
          d < p.2 - p.1} ≤ β := by
  classical
  let S : Path2 → Set (ℝ × ℝ) := fun ω => {p |
    let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
    let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
    (-p.1, -p.2) ∈ forwardConeVectors X Y ∧ 0 < p.1 ∧ p.2 < 1 ∧
      d < p.2 - p.1}
  let A : ℕ → Set Path2 := fun k => {ω | ∀ p ∈ S ω, ∀ᶠ n : ℕ in atTop,
    ∃ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
      p ∈ factorialGridNeighborhood n ij.1 ij.2 ∧
      ω ∈ separatedFactorialConeGridEvent (-direction) C α d k n ij.1 ij.2}
  have hdim : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ A k → dimH (S ω) ≤ β := by
    intro k
    obtain ⟨K, hK, hcostk⟩ := hcost k
    apply ae_dimH_le_of_pointwise_selected_finite_cover
      (ι := fun n => Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6))
      (μ := μ) (K := K) β hβ S (A k)
      (fun n ij => factorialGridNeighborhood n ij.1 ij.2)
      (fun n ij => separatedFactorialConeGridEvent (-direction) C α d k n ij.1 ij.2)
      (fun n ij => by
        unfold separatedFactorialConeGridEvent
        split
        · exact measurableSet_factorialConeGridEvent (-direction) C α k n ij.1 ij.2
        · exact MeasurableSet.empty)
      (fun n => ENNReal.ofReal (2 * factorialGridMesh n))
      tendsto_factorialGridNeighborhood_diameter
      (fun n ij => ediam_factorialGridNeighborhood_le n ij.1 ij.2)
    · intro ω hω p hp
      filter_upwards [hω p hp] with n hn
      obtain ⟨ij, hpij, hevent⟩ := hn
      exact mem_iUnion.2 ⟨ij, by simpa only [hevent, ite_true] using hpij⟩
    · exact hK
    · simpa only [separatedFactorialConeGridEvent, apply_ite, measure_empty,
        mul_ite, mul_zero] using hcostk
  filter_upwards [ae_all_iff.2 hdim, ae_factorial_forwardConeVector_reflected_grid_events hμ] with ω hdimω hgrid
  obtain ⟨k, hk⟩ := hgrid α hα C d hC hd direction hdir
  apply hdimω k
  intro p hp
  obtain ⟨hv, ha, hs, hsep⟩ := hp
  filter_upwards [hk (-p.1) (-p.2) hv (by simpa using ha) (by simpa using hs)
      (by simpa using hsep)] with n hn
  obtain ⟨i, j, _, _, hsep', ha', hs', hevent⟩ := hn
  refine ⟨(i, j), ?_, ?_⟩
  · apply mem_factorialGridNeighborhood n i j p.1 p.2
    · simpa only [factorialGridMesh, abs_sub_comm, neg_neg] using ha'
    · simpa only [factorialGridMesh, abs_sub_comm, neg_neg] using hs'
  · simpa only [separatedFactorialConeGridEvent, hsep', ite_true] using hevent

end LatticeProb.CorrelatedBM
