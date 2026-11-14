/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiTriangle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiPathComparison

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_heat_phi_bad_event_subset
    {Ω : Type} (K : Set ℂ) (X Y Φ : ℂ → Ω → ℝ) (a b : ℝ) :
    {ω | ∃ z ∈ K, a + b < |X z ω - Φ z ω|} ⊆
      {ω | ∃ z ∈ K, a < |X z ω - Y z ω|} ∪
      {ω | ∃ z ∈ K, b < |Y z ω - Φ z ω|} := by
  rintro ω ⟨z, hz, hbad⟩
  by_contra hno
  simp only [mem_union, mem_setOf_eq, not_or, not_exists, not_and, not_lt] at hno
  have htri : |X z ω - Φ z ω| ≤
      |X z ω - Y z ω| + |Y z ω - Φ z ω| := by
    have heq : X z ω - Φ z ω = (X z ω - Y z ω) + (Y z ω - Φ z ω) := by ring
    rw [heq]
    exact abs_add_le _ _
  have h1 := hno.1 z hz
  have h2 := hno.2 z hz
  linarith

 

theorem dg20_heat_phi_bad_event_measure_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (K : Set ℂ)
    (X Y Φ : ℂ → Ω → ℝ) (a b : ℝ) :
    P {ω | ∃ z ∈ K, a + b < |X z ω - Φ z ω|} ≤
      P {ω | ∃ z ∈ K, a < |X z ω - Y z ω|} +
      P {ω | ∃ z ∈ K, b < |Y z ω - Φ z ω|} :=
  (measure_mono (dg20_heat_phi_bad_event_subset K X Y Φ a b)).trans
    (measure_union_le _ _)

end SupercriticalLQGUniqueness.B2.DG20Pt
