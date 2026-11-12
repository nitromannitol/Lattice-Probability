/-
# The truncation identity for the real band projection, as a named input

`BandProjHighFreq` states the truncation identity
`sobolevNormSq d s (φ - P_Λ φ) ≤ sobolevNormSqHigh d s Λ φ` for the real projection
`P_Λ φ = bandProj d Λ …`; it follows from `fourier_bandProj` (`FejerLimit.lean`) and the support
of `1 - bandCut`.
-/
import LatticeProb.Analysis.Sobolev.Additivity
import LatticeProb.Analysis.Sobolev.FejerLimit
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The truncation identity.**  The `H^s` error of the real projection `P_Λ φ` is controlled by
the high-frequency part of `φ`. -/
def BandProjHighFreq : Prop :=
  ∀ (d : ℕ) (s : ℝ) (Λ : ℝ) (hΛ : 0 < Λ),
    ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ),
      sobolevNormSq d s (fun x => φ x - bandProj d Λ hΛ.ne' φ hcont hcs x)
        ≤ sobolevNormSqHigh d s Λ φ

end LatticeProb.Sobolev
