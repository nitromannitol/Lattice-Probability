/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2DyadicSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB2

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneA2_dyadic_lower_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W)
    {k n : ℕ} (hkn : k ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (M x : ℝ) :
    P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω <
        Real.exp (-(|ξ| * M)) * x} ≤
      P {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 k z ω|} +
      P {ω | lenObs ξ (phiMN W P k n) (rectAB a b) ω < x} := by
  have h0k := isPhiVersion_phiMN hW (Nat.zero_le k)
  have h0n := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hkn' := isPhiVersion_phiMN hW hkn
  have hE : {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω <
      Real.exp (-(|ξ| * M)) * x} ≤ᵐ[P]
      ({ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 k z ω|} ∪
        {ω | lenObs ξ (phiMN W P k n) (rectAB a b) ω < x} : Set Ω) := by
    filter_upwards [ae_phiMN_add hW hkn] with ω hω hωE
    by_cases hB : M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 k z ω|
    · exact Or.inl hB
    right
    have hB' := not_lt.1 hB
    have hbd : ∀ z ∈ (rectAB a b).toSet, |phiMN W P 0 k z ω| ≤ M := by
      intro z hz
      exact (le_ciSup (SupTail.bddAbove_abs_of_compact (MarkedRect.isCompact_toSet _)
        (h0k.cont ω)) (⟨z, hz⟩ : (rectAB a b).toSet)).trans hB'
    have hcmp := (LQGMetric.DDDF.S6AB.len_cmp_AB
      (ξ := ξ) ha hb (h0n.cont ω) (hkn'.cont ω) hω hbd).1
    have hωE' : lenObs ξ (phiMN W P 0 n) (rectAB a b) ω <
        Real.exp (-(|ξ| * M)) * x := hωE
    exact lt_of_mul_lt_mul_left (hcmp.trans_lt hωE') (Real.exp_pos _).le
  calc
    _ ≤ P ({ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 k z ω|} ∪
          {ω | lenObs ξ (phiMN W P k n) (rectAB a b) ω < x}) := measure_mono_ae hE
    _ ≤ _ := measure_union_le _ _

end SupercriticalLQGUniqueness.B2.DG20Conc
