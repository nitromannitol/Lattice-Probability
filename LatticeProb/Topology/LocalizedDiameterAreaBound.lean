import LatticeProb.Topology.LocalizedSegmentRatio
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Localized

/-! # Localized diameter-to-area estimates -/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- Quantitative lower bounds on the two first-exit trace areas, at every
relevant scale, bound the localized diameter-to-area supremum. -/
theorem locDA_le_of_first_exit_bounds
    (η : ℝ → ℂ) (hη : Continuous η)
    (z : ℂ) {ε t₀ L U C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (hleft : ¬ η '' Icc (t₀ - ε / 2) t₀ ⊆ ball z L)
    (hright : ¬ η '' Icc t₀ (t₀ + ε / 2) ⊆ ball z L)
    (hwindow : η '' Icc (t₀ - ε) (t₀ + ε) ⊆ closedBall z U)
    (htrace : ∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log U →
      ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / C) ≤
        min (volume (η '' Icc (sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ ball z (Real.exp k)}) t₀))
          (volume (η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z (Real.exp k)})))) :
    locDA ε η t₀ ≤ ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * C) := by
  unfold locDA
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  exact LatticeProb.localized_segment_ratio_le_of_first_exit_bounds
    volume η hη z hL hC hleft hright hwindow htrace s hs

end MatedCRTHarmonic.GMS4b
