import LatticeProb.Prob.CountablePhaseFiber
import LatticeProb.Prob.CountablePhaseLimit
import LatticeProb.Prob.MapKernelTVCountablePartition

/-! Total variation convergence of phases on countably many fibers. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal Topology

namespace LatticeProb

/-- Fiberwise absolute continuity implies asymptotic uniformity of all phases. -/
theorem tendsto_tvDist_countablePhaseMap
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (μ : Measure (CountablePhaseSpace E)) [IsFiniteMeasure μ]
    (hμ : ∀ n : ℕ,
      let ν := μ.comap (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)
      ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin n → ℝ)))
    (a : τ → ℝ) (ha : Tendsto a l atTop)
    (θ : τ → ∀ k, E → (Fin k → ℝ)) (hθ : ∀ t k, Measurable (θ t k)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (countablePhaseMap (a t) (θ t)))
      (countableUniformPhaseKernel ∘ₘ μ)) l (𝓝 0) := by
  let A : ℕ → Set (CountablePhaseSpace E) := fun n => {x | x.1 = n}
  have hA : ∀ n, MeasurableSet (A n) := measurableSet_countablePhase_count
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij (hx.symm.trans hy)
  have hcover : (⋃ n, A n) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨x.1, rfl⟩
  apply tendsto_tvDist_map_comp_of_countable_partition μ A hA hd hcover
    (fun t => countablePhaseMap (a t) (θ t))
    (fun t => measurable_countablePhaseMap (a t) (θ t) (hθ t))
    (fun _ => countableUniformPhaseKernel) (fun _ => inferInstance)
  intro n
  have h := tendsto_tvDist_countablePhaseMap_fixedCount n
    (μ.comap (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)) (hμ n) a ha θ hθ
  rw [countablePhase_map_comap] at h
  exact h

end LatticeProb
