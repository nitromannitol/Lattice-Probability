import LatticeProb.Topology.RandomShiftedCellFrontierArc

/-! # Measurability of adjacency between shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open scoped unitInterval

namespace LatticeProb

/-- The indicator matrix of distinct shifted cells sharing an injective frontier path
is almost-everywhere measurable for any finite law. -/
theorem aemeasurable_shifted_cell_frontier_adjacency
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (B : ι → Set ℂ)
    (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (hopen : ∀ i, IsOpen (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    AEMeasurable (fun ω (k l : ℤ) =>
      ({ω : Ω | shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
          shiftedCompactCell (η ω) (ε ω) (θ ω) l ∧
        ∃ γ : C(unitInterval, ℂ), Function.Injective γ ∧
          (∀ t, γ t ∈ frontier (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ)) ∧
          (∀ t, γ t ∈ frontier (shiftedCompactCell (η ω) (ε ω) (θ ω) l : Set ℂ))}.indicator
        (fun _ => (1 : ℕ))) ω) μ := by
  classical
  let : MeasurableSpace (NonemptyCompacts ℂ) := borel _
  let : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩
  have hc (k : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) k) :=
    (measurable_shiftedCompactCell k).comp (hη.prodMk (hε.prodMk hθ))
  apply AEMeasurable.of_eval
  intro k
  apply AEMeasurable.of_eval
  intro l
  apply AEMeasurable.indicator₀ aemeasurable_const
  exact (measurableSet_eq_fun (hc k) (hc l)).compl.nullMeasurableSet.inter
    (nullMeasurableSet_exists_injective_path_in_random_shifted_cell_frontiers B η ε θ k l
      hη hε hθ hopen hbasis μ)

end LatticeProb
