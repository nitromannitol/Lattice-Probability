import LatticeProb.Topology.ComplexCompactComponentCount

/-! # Extended component counts of random shifted cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- The extended cardinalities of the non-singleton components of all shifted
cell intersections form an almost everywhere measurable array. Infinite
component families are recorded as infinity. -/
theorem aemeasurable_shifted_cell_component_encard_array
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hη : AEMeasurable η μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ) :
    AEMeasurable (fun ω (k l : ℤ) => (nonSingletonComponents
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)).encard) μ := by
  let η' := hη.mk η
  let ε' := hε.mk ε
  let θ' := hθ.mk θ
  have hc (j : ℤ) : Measurable (fun ω => shiftedCompactCell (η' ω) (ε' ω) (θ' ω) j) :=
    (measurable_shiftedCompactCell j).comp
      (hη.measurable_mk.prodMk (hε.measurable_mk.prodMk hθ.measurable_mk))
  have ha : AEMeasurable (fun ω (k l : ℤ) => (nonSingletonComponents
      ((shiftedCompactCell (η' ω) (ε' ω) (θ' ω) k : Set ℂ) ∩
        shiftedCompactCell (η' ω) (ε' ω) (θ' ω) l)).encard) μ := by
    apply AEMeasurable.of_eval
    intro k
    apply AEMeasurable.of_eval
    intro l
    exact aemeasurable_random_complex_compact_inter_component_encard _ _ (hc k) (hc l) μ
  apply ha.congr
  filter_upwards [hη.ae_eq_mk, hε.ae_eq_mk, hθ.ae_eq_mk] with ω hηω hεω hθω
  simp only [η', ε', θ', ← hηω, ← hεω, ← hθω]

end LatticeProb
