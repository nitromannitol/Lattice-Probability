/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.TranslatedCostBadEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TranslatedPointCost
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.RealRandomTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_translated_cost_bad_event
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ℝ) (F G : Ω → C(ℂ, ℝ)) (c : Ω → ℝ)
    (U : Set ℂ) (z w a : ℂ) (b : ℝ≥0∞) (M ζ : ℝ)
    (hM : 0 ≤ M)
    (hFG : ∀ᵐ ω ∂P, ∀ x, G ω x = F ω (x + a) - c ω)
    (hc : P {ω | M < |c ω|} ≤ ENNReal.ofReal ζ) :
    let A : Ω → ℝ≥0∞ := fun ω => b *
      crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a}
    let B : Ω → ℝ≥0∞ := fun ω => b *
      crossLenIn ξ (G ω) U {z} {w}
    P {ω | ¬ (A ω ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * B ω ∧
      B ω ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * A ω)} ≤ ENNReal.ofReal ζ := by
  dsimp
  let E : Ω → Prop := fun ω => ∀ x, G ω x = F ω (x + a) - c ω
  have hnull : P {ω | ¬ E ω} = 0 := ae_iff.mp hFG
  have hsub :
      {ω | ¬ (b * crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a} ≤
          ENNReal.ofReal (Real.exp (|ξ| * M)) *
            (b * crossLenIn ξ (G ω) U {z} {w}) ∧
        b * crossLenIn ξ (G ω) U {z} {w} ≤
          ENNReal.ofReal (Real.exp (|ξ| * M)) *
            (b * crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a}))} ⊆
      {ω | M < |c ω|} ∪ {ω | ¬ E ω} := by
    intro ω hbad
    by_cases hω : E ω
    · by_cases hcm : |c ω| ≤ M
      · have hcc : ENNReal.ofReal (Real.exp |ξ * c ω|) ≤
            ENNReal.ofReal (Real.exp (|ξ| * M)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [abs_mul]
          exact Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left hcm (abs_nonneg ξ))
        have hraw := dg20_translated_point_cost_compare ξ (F ω) (G ω)
          U z w a (c ω) hω
        have hAB : b * crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a} ≤
            ENNReal.ofReal (Real.exp (|ξ| * M)) *
              (b * crossLenIn ξ (G ω) U {z} {w}) := by
          calc
            _ ≤ b * (ENNReal.ofReal (Real.exp |ξ * c ω|) *
                crossLenIn ξ (G ω) U {z} {w}) :=
              mul_le_mul_of_nonneg_left hraw.1 bot_le
            _ ≤ b * (ENNReal.ofReal (Real.exp (|ξ| * M)) *
                crossLenIn ξ (G ω) U {z} {w}) := by
              gcongr
            _ = _ := by ac_rfl
        have hBA : b * crossLenIn ξ (G ω) U {z} {w} ≤
            ENNReal.ofReal (Real.exp (|ξ| * M)) *
              (b * crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a}) := by
          calc
            _ ≤ b * (ENNReal.ofReal (Real.exp |ξ * c ω|) *
                crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a}) :=
              mul_le_mul_of_nonneg_left hraw.2 bot_le
            _ ≤ b * (ENNReal.ofReal (Real.exp (|ξ| * M)) *
                crossLenIn ξ (F ω) ((· + a) '' U) {z + a} {w + a}) := by
              gcongr
            _ = _ := by ac_rfl
        exact False.elim (hbad ⟨hAB, hBA⟩)
      · exact Or.inl (lt_of_not_ge hcm)
    · exact Or.inr hω
  calc
    _ ≤ P ({ω | M < |c ω|} ∪ {ω | ¬ E ω}) := measure_mono hsub
    _ ≤ P {ω | M < |c ω|} + P {ω | ¬ E ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ζ := by rw [hnull, add_zero]; exact hc

end SupercriticalLQGUniqueness.B2.DG20Pt
