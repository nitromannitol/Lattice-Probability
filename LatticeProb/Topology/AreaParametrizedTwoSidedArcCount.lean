import LatticeProb.Topology.ShiftedTwoSidedArcCount
import LatticeProb.Topology.ShiftedAreaCellInjective

/-! # Two-sided arc counts for area-parametrized shifted cells -/

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

namespace LatticeProb

/-- For positive-mesh area-parametrized cells, the distinct-cell guard in the
two-sided arc count is redundant almost everywhere. The side curves are arbitrary. -/
theorem ae_shifted_two_sided_arc_count_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (α β γ δ : ℤ → ℤ → Ω → C(unitInterval, ℂ)) (P : Measure Ω)
    (harea : ∀ᵐ ω ∂P, 0 < ε ω ∧ ∃ ν : Measure ℂ, ∀ a b, a < b →
      ν (η ω '' Icc a b) = ENNReal.ofReal (b - a)) :
    let L := fun (k l : ℤ) (ω : Ω) => ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
      (∀ t, ∃ x, p t = α k l ω x) ∧ (∀ t, ∃ x, p t = β k l ω x)
    let R := fun (k l : ℤ) (ω : Ω) => ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
      (∀ t, ∃ x, p t = γ k l ω x) ∧ (∀ t, ∃ x, p t = δ k l ω x)
    ∀ᵐ ω ∂P, (fun (k l : ℤ) =>
      ({ω : Ω | k ≠ l ∧ shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
          shiftedCompactCell (η ω) (ε ω) (θ ω) l ∧ (L k l ω ∨ R k l ω)}.indicator
        (fun _ => (1 : ℕ))) ω +
      ({ω : Ω | k ≠ l ∧ shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
          shiftedCompactCell (η ω) (ε ω) (θ ω) l ∧ L k l ω ∧ R k l ω}.indicator (fun _ => (1 : ℕ))) ω) =
      (fun (k l : ℤ) =>
      ({ω : Ω | k ≠ l ∧ (L k l ω ∨ R k l ω)}.indicator (fun _ => (1 : ℕ))) ω +
      ({ω : Ω | k ≠ l ∧ L k l ω ∧ R k l ω}.indicator (fun _ => (1 : ℕ))) ω) := by
  classical
  dsimp only
  filter_upwards [harea] with ω hω
  obtain ⟨hε, ν, hν⟩ := hω
  have hinj := shiftedCompactCell_injective_of_areaParametrized (η ω) hε (θ ω) hν
  funext k l
  by_cases hkl : k = l
  · subst l
    simp [Set.indicator]
  · have hne : shiftedCompactCell (η ω) (ε ω) (θ ω) k ≠
        shiftedCompactCell (η ω) (ε ω) (θ ω) l := hinj.ne hkl
    simp [Set.indicator, hkl, hne]

/-- The unguarded two-sided arc count is almost everywhere measurable under the
same assumptions, including measurable parametrizations of all four sides. -/
theorem aemeasurable_areaParametrized_two_sided_arc_count
    {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (α β γ δ : ℤ → ℤ → Ω → C(unitInterval, ℂ))
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (hα : ∀ k l, Measurable (α k l)) (hβ : ∀ k l, Measurable (β k l))
    (hγ : ∀ k l, Measurable (γ k l)) (hδ : ∀ k l, Measurable (δ k l))
    (P : Measure Ω) [IsFiniteMeasure P]
    (harea : ∀ᵐ ω ∂P, 0 < ε ω ∧ ∃ ν : Measure ℂ, ∀ a b, a < b →
      ν (η ω '' Icc a b) = ENNReal.ofReal (b - a)) :
    let L := fun (k l : ℤ) (ω : Ω) => ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
      (∀ t, ∃ x, p t = α k l ω x) ∧ (∀ t, ∃ x, p t = β k l ω x)
    let R := fun (k l : ℤ) (ω : Ω) => ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
      (∀ t, ∃ x, p t = γ k l ω x) ∧ (∀ t, ∃ x, p t = δ k l ω x)
    AEMeasurable (fun ω (k l : ℤ) =>
      ({ω : Ω | k ≠ l ∧ (L k l ω ∨ R k l ω)}.indicator (fun _ => (1 : ℕ))) ω +
      ({ω : Ω | k ≠ l ∧ L k l ω ∧ R k l ω}.indicator (fun _ => (1 : ℕ))) ω) P := by
  exact (aemeasurable_shifted_two_sided_arc_count η ε θ α β γ δ hη hε hθ
    hα hβ hγ hδ P).congr (ae_shifted_two_sided_arc_count_eq η ε θ α β γ δ P harea)

end LatticeProb
