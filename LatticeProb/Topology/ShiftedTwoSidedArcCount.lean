import LatticeProb.Topology.ShiftedCellAdjacencyMeasurable
import LatticeProb.Topology.RandomParametrizedArc

/-! # Measurability of two-sided arc counts for shifted cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open scoped unitInterval

namespace LatticeProb

/-- Given measurable parametrizations of two pairs of sides for each pair of labels,
count the first shared arc and a second shared arc whenever both pairs share one.
The second count is retained for consecutive labels. The distinct-cell guard and
the resulting full count matrix are measurable modulo any finite law. The
parametrizations are arbitrary; no geometric identification of the sides is asserted. -/
theorem aemeasurable_shifted_two_sided_arc_count
    {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (α β γ δ : ℤ → ℤ → Ω → C(unitInterval, ℂ))
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (hα : ∀ k l, Measurable (α k l)) (hβ : ∀ k l, Measurable (β k l))
    (hγ : ∀ k l, Measurable (γ k l)) (hδ : ∀ k l, Measurable (δ k l))
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    let L := fun (k l : ℤ) (ω : Ω) => ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
      (∀ t, ∃ x, p t = α k l ω x) ∧ (∀ t, ∃ x, p t = β k l ω x)
    let R := fun (k l : ℤ) (ω : Ω) => ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
      (∀ t, ∃ x, p t = γ k l ω x) ∧ (∀ t, ∃ x, p t = δ k l ω x)
    AEMeasurable (fun ω (k l : ℤ) =>
      ({ω : Ω | k ≠ l ∧ shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
          shiftedCompactCell (η ω) (ε ω) (θ ω) l ∧ (L k l ω ∨ R k l ω)}.indicator
        (fun _ => (1 : ℕ))) ω +
      ({ω : Ω | k ≠ l ∧ shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
          shiftedCompactCell (η ω) (ε ω) (θ ω) l ∧ L k l ω ∧ R k l ω}.indicator
        (fun _ => (1 : ℕ))) ω) μ := by
  classical
  dsimp only
  let : MeasurableSpace (NonemptyCompacts ℂ) := borel _
  let : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩
  have hc (k : ℤ) : Measurable (fun ω => shiftedCompactCell (η ω) (ε ω) (θ ω) k) :=
    (measurable_shiftedCompactCell k).comp (hη.prodMk (hε.prodMk hθ))
  apply AEMeasurable.of_eval
  intro k
  apply AEMeasurable.of_eval
  intro l
  have hL := nullMeasurableSet_exists_injective_path_in_random_curve_ranges
    (α k l) (β k l) (hα k l) (hβ k l) μ
  have hR := nullMeasurableSet_exists_injective_path_in_random_curve_ranges
    (γ k l) (δ k l) (hγ k l) (hδ k l) μ
  have hkl : MeasurableSet {ω : Ω | k ≠ l} := by
    by_cases h : k ≠ l <;> simp [h]
  have hD : NullMeasurableSet {ω : Ω | k ≠ l ∧
      shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
        shiftedCompactCell (η ω) (ε ω) (θ ω) l} μ :=
    (hkl.inter (measurableSet_eq_fun (hc k) (hc l)).compl).nullMeasurableSet
  apply AEMeasurable.add
  · apply AEMeasurable.indicator₀ aemeasurable_const
    simpa only [Set.ofPred_and, Set.ofPred_or, inter_assoc] using hD.inter (hL.union hR)
  · apply AEMeasurable.indicator₀ aemeasurable_const
    simpa only [Set.ofPred_and, inter_assoc] using
      ((hD.inter hL).inter hR)

end LatticeProb
