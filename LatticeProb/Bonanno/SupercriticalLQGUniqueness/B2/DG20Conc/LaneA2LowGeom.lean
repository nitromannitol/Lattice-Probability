/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowSup

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

theorem laneA2_short_length_of_sup
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W)
    (m : ℕ) (ω : Ω) (M : ℝ)
    (hM : (⨆ z : (rectAB (1/8) (3/8)).toSet,
      |phiMN W P 0 m z ω|) ≤ M) :
    (1/8) * Real.exp (-(|ξ| * M)) ≤
      lenObs ξ (phiMN W P 0 m) (rectAB (1/8) (3/8)) ω := by
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le m)).cont
  have hb : ∀ x ∈ (rectAB (1/8) (3/8)).toSet,
      |phiMN W P 0 m x ω| ≤ M := by
    intro x hx
    have hba := LQGMetric.SupTail.bddAbove_abs_of_compact
      (rectAB (1/8) (3/8)).isCompact_toSet (hc ω)
    exact (le_ciSup hba (⟨x, hx⟩ : (rectAB (1/8) (3/8)).toSet)).trans hM
  have h := exp_neg_le_lenObs (ξ := ξ) hc (rectAB (1/8) (3/8))
    (by norm_num [rectAB]) (by norm_num [rectAB]) hb
  simpa [rectAB, MarkedRect.crossWidth, mul_comm] using h

theorem laneA2_long_length_of_sup
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W)
    (m : ℕ) (ω : Ω) (M : ℝ)
    (hM : (⨆ z : (rectAB (3/8) (1/8)).toSet,
      |phiMN W P 0 m z ω|) ≤ M) :
    lenObs ξ (phiMN W P 0 m) (rectAB (3/8) (1/8)) ω ≤
      (3/8) * Real.exp (|ξ| * M) := by
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le m)).cont
  have hb : ∀ x ∈ (rectAB (3/8) (1/8)).toSet,
      |phiMN W P 0 m x ω| ≤ M := by
    intro x hx
    have hba := LQGMetric.SupTail.bddAbove_abs_of_compact
      (rectAB (3/8) (1/8)).isCompact_toSet (hc ω)
    exact (le_ciSup hba (⟨x, hx⟩ : (rectAB (3/8) (1/8)).toSet)).trans hM
  have h := lenObs_le_exp (ξ := ξ) (rectAB (3/8) (1/8))
    (by norm_num [rectAB]) (by norm_num [rectAB]) hb
  simpa [rectAB, MarkedRect.crossWidth, mul_comm] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
