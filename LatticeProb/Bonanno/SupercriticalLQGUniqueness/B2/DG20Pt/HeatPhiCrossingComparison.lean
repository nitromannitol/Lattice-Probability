/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCrossingComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiWholePlaneCompact

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_heat_phi_crossLen_compare_on_compact
    (ξ : ℝ) (X Φ : ℂ → ℝ) (K U A B : Set ℂ) (M : ℝ)
    (hUK : U ⊆ K) (hfield : ∀ z ∈ K, |X z - Φ z| ≤ M) :
    crossLenIn ξ X U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * crossLenIn ξ Φ U A B ∧
      crossLenIn ξ Φ U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * crossLenIn ξ X U A B := by
  constructor
  · exact crossLenIn_le_of_abs_sub_le (fun z hz => hfield z (hUK hz))
  · exact crossLenIn_le_of_abs_sub_le (fun z hz => by
      rw [abs_sub_comm]
      exact hfield z (hUK hz))

 

theorem dg20_heat_phi_crossLen_bad_subset_sup_bad
    {Ω : Type*} (ξ : ℝ) (X Φ : ℂ → Ω → ℝ)
    (K U A B : Set ℂ) (M : ℝ) (hUK : U ⊆ K) :
    {ω | ¬ (
      crossLenIn ξ (fun z => X z ω) U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          crossLenIn ξ (fun z => Φ z ω) U A B ∧
      crossLenIn ξ (fun z => Φ z ω) U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          crossLenIn ξ (fun z => X z ω) U A B)} ⊆
      {ω | ∃ z ∈ K, M < |X z ω - Φ z ω|} := by
  intro ω hbad
  by_contra hno
  exact hbad (dg20_heat_phi_crossLen_compare_on_compact ξ
    (fun z => X z ω) (fun z => Φ z ω) K U A B M hUK
    (by intro z hz; exact le_of_not_gt (fun hgt => hno ⟨z, hz, hgt⟩)))

end SupercriticalLQGUniqueness.B2.DG20Pt
