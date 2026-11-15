import LatticeProb.Prob.UnitCubeTVApproximation

/-! Transfer of uniform-cube convergence through total variation approximation. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Uniform-cube convergence passes from finite approximating measures to their
finite total-variation limit, even when the measurable maps vary along a filter. -/
theorem tendsto_tvDist_map_prod_unitCube_of_approx {E X ι τ : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [Fintype ι]
    (μ : Measure (E × X)) [IsFiniteMeasure μ]
    (ν : ℕ → Measure (E × X)) [∀ j, IsFiniteMeasure (ν j)]
    {l : Filter τ} (g : τ → E × X → E × (ι → ℝ))
    (hg : ∀ t, Measurable (g t))
    (happrox : Tendsto (fun j => QuantumZipper.TV.tvDist μ (ν j)) atTop (𝓝 0))
    (hν : ∀ j, Tendsto (fun t => QuantumZipper.TV.tvDist
      ((ν j).map (g t)) (((ν j).map Prod.fst).prod (unitCubeMeasure ι))) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (g t)) ((μ.map Prod.fst).prod (unitCubeMeasure ι))) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by simp)
  have hquarter : 0 < (ε / 2) / 2 := ENNReal.div_pos hhalf.ne' (by simp)
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.1 happrox _ hquarter).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hν j) _ hhalf] with t ht
  calc
    _ ≤ QuantumZipper.TV.tvDist ((ν j).map (g t))
        (((ν j).map Prod.fst).prod (unitCubeMeasure ι)) +
        (QuantumZipper.TV.tvDist μ (ν j) + QuantumZipper.TV.tvDist μ (ν j)) :=
      tvDist_map_prod_unitCube_le_of_approx μ (ν j) (hg t)
    _ ≤ ε / 2 + ((ε / 2) / 2 + (ε / 2) / 2) :=
      add_le_add ht (add_le_add hj hj)
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

end LatticeProb
