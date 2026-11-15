import LatticeProb.Topology.RandomShiftedCellTwoComponentsEvent
import LatticeProb.Topology.RandomShiftedCellThreeComponentsEvent

/-! # Exactly two components in random shifted cell intersections -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- The event that the intersection of two random shifted cells has exactly two
non-singleton components is null measurable for every finite measure. -/
theorem nullMeasurableSet_random_shifted_cell_inter_exactly_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      let S : Set ℂ := (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l
      ∃ x ∈ S, ∃ y ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ∀ z ∈ S, ¬ (connectedComponentIn S z).Subsingleton →
          connectedComponentIn S z = connectedComponentIn S x ∨
            connectedComponentIn S z = connectedComponentIn S y} μ := by
  classical
  let S : Ω → Set ℂ := fun ω => (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
    shiftedCompactCell (η ω) (ε ω) (θ ω) l
  let A : Set Ω := {ω | ∃ x ∈ S ω, ∃ y ∈ S ω,
    connectedComponentIn (S ω) x ≠ connectedComponentIn (S ω) y ∧
    ¬ (connectedComponentIn (S ω) x).Subsingleton ∧
    ¬ (connectedComponentIn (S ω) y).Subsingleton}
  let B : Set Ω := {ω | ∃ x ∈ S ω, ∃ y ∈ S ω, ∃ z ∈ S ω,
    connectedComponentIn (S ω) x ≠ connectedComponentIn (S ω) y ∧
    connectedComponentIn (S ω) x ≠ connectedComponentIn (S ω) z ∧
    connectedComponentIn (S ω) y ≠ connectedComponentIn (S ω) z ∧
    ¬ (connectedComponentIn (S ω) x).Subsingleton ∧
    ¬ (connectedComponentIn (S ω) y).Subsingleton ∧
    ¬ (connectedComponentIn (S ω) z).Subsingleton}
  have hA : NullMeasurableSet A μ :=
    nullMeasurableSet_random_shifted_cell_inter_two_components η ε θ k l hη hε hθ μ
  have hB : NullMeasurableSet B μ :=
    nullMeasurableSet_random_shifted_cell_inter_three_components η ε θ k l hη hε hθ μ
  have heq : {ω : Ω | ∃ x ∈ S ω, ∃ y ∈ S ω,
      connectedComponentIn (S ω) x ≠ connectedComponentIn (S ω) y ∧
      ¬ (connectedComponentIn (S ω) x).Subsingleton ∧
      ¬ (connectedComponentIn (S ω) y).Subsingleton ∧
      ∀ z ∈ S ω, ¬ (connectedComponentIn (S ω) z).Subsingleton →
        connectedComponentIn (S ω) z = connectedComponentIn (S ω) x ∨
          connectedComponentIn (S ω) z = connectedComponentIn (S ω) y} = A ∩ Bᶜ := by
    ext ω
    constructor
    · rintro ⟨x, hx, y, hy, hxy, hxns, hyns, hall⟩
      refine ⟨⟨x, hx, y, hy, hxy, hxns, hyns⟩, ?_⟩
      rintro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hans, hbns, hcns⟩
      rcases hall a ha hans with hax | hay <;>
        rcases hall b hb hbns with hbx | hby <;>
        rcases hall c hc hcns with hcx | hcy
      all_goals first
        | exact hab (hax.trans hbx.symm)
        | exact hab (hay.trans hby.symm)
        | exact hac (hax.trans hcx.symm)
        | exact hac (hay.trans hcy.symm)
        | exact hbc (hbx.trans hcx.symm)
        | exact hbc (hby.trans hcy.symm)
    · rintro ⟨⟨x, hx, y, hy, hxy, hxns, hyns⟩, hBω⟩
      refine ⟨x, hx, y, hy, hxy, hxns, hyns, ?_⟩
      intro z hz hzns
      by_contra hn
      have hz' : connectedComponentIn (S ω) z ≠ connectedComponentIn (S ω) x ∧
          connectedComponentIn (S ω) z ≠ connectedComponentIn (S ω) y := by
        simpa only [not_or] using hn
      exact hBω ⟨x, hx, y, hy, z, hz, hxy, Ne.symm hz'.1, Ne.symm hz'.2,
        hxns, hyns, hzns⟩
  exact heq ▸ hA.inter hB.compl

/-- The exactly-two-component event expressed using curve segment images. -/
theorem nullMeasurableSet_random_shifted_segment_inter_exactly_two_components
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ) (k l : ℤ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet {ω : Ω |
      let S : Set ℂ :=
        (η ω '' uIcc (ε ω * ((k : ℝ) - 1 + θ ω)) (ε ω * ((k : ℝ) + θ ω))) ∩
        (η ω '' uIcc (ε ω * ((l : ℝ) - 1 + θ ω)) (ε ω * ((l : ℝ) + θ ω)))
      ∃ x ∈ S, ∃ y ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ∀ z ∈ S, ¬ (connectedComponentIn S z).Subsingleton →
          connectedComponentIn S z = connectedComponentIn S x ∨
            connectedComponentIn S z = connectedComponentIn S y} μ := by
  simpa only [coe_shiftedCompactCell] using
    nullMeasurableSet_random_shifted_cell_inter_exactly_two_components η ε θ k l hη hε hθ μ

end LatticeProb
