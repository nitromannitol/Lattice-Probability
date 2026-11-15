import LatticeProb.Topology.RandomShiftedCellExtendedComponentCount

/-! # Agreement of shifted-cell component counts -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- For any almost everywhere measurable array of finite counts, simultaneous
agreement with the extended component counts of distinct shifted cells is null
measurable. This does not assert that agreement occurs. -/
theorem nullMeasurableSet_shifted_cell_count_agreement
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (N : Ω → ℤ → ℤ → ℕ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
    (hN : AEMeasurable N μ) :
    NullMeasurableSet {ω | ∀ j k : ℤ, j ≠ k →
      (nonSingletonComponents ((shiftedCompactCell (η ω) (ε ω) (θ ω) j : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) k)).encard = (N ω j k : ℕ∞)} μ := by
  have hC := aemeasurable_shifted_cell_component_encard_array η ε θ μ hη hε hθ
  have hcast : Measurable (fun n : ℕ => (n : ℕ∞)) := measurable_of_countable _
  have hpair (j k : ℤ) : NullMeasurableSet {ω |
      (nonSingletonComponents ((shiftedCompactCell (η ω) (ε ω) (θ ω) j : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) k)).encard = (N ω j k : ℕ∞)} μ :=
    nullMeasurableSet_eq_fun ((hC.eval j).eval k) (hcast.comp_aemeasurable ((hN.eval j).eval k))
  have hall : NullMeasurableSet (⋂ j : ℤ, ⋂ k : ℤ,
      if j ≠ k then {ω | (nonSingletonComponents
        ((shiftedCompactCell (η ω) (ε ω) (θ ω) j : Set ℂ) ∩
          shiftedCompactCell (η ω) (ε ω) (θ ω) k)).encard = (N ω j k : ℕ∞)}
      else univ) μ := by
    apply NullMeasurableSet.iInter
    intro j
    apply NullMeasurableSet.iInter
    intro k
    by_cases h : j ≠ k
    · simpa [h] using hpair j k
    · simp only [h, ite_false]
      exact MeasurableSet.univ.nullMeasurableSet
  convert hall using 1
  ext ω
  simp

/-- Matching a finite count with the extended count proves both finiteness and
equality with the natural component count. -/
theorem shifted_cell_count_agreement_at
    (η : C(ℝ, ℂ)) (ε θ : ℝ) (j k : ℤ) (n : ℕ)
    (h : (nonSingletonComponents ((shiftedCompactCell η ε θ j : Set ℂ) ∩
      shiftedCompactCell η ε θ k)).encard = (n : ℕ∞)) :
    (nonSingletonComponents ((shiftedCompactCell η ε θ j : Set ℂ) ∩
      shiftedCompactCell η ε θ k)).Finite ∧
    (nonSingletonComponents ((shiftedCompactCell η ε θ j : Set ℂ) ∩
      shiftedCompactCell η ε θ k)).ncard = n := by
  constructor
  · exact Set.finite_of_encard_eq_coe h
  · simpa only [Set.ncard, ENat.toNat_natCast] using congrArg ENat.toNat h

end LatticeProb
