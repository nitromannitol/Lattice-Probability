/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockCrossLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossScaleLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusOsc

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

def j1BlockInner (i : Bool) (v : ℂ) (K : ℕ) : Set ℂ :=
  (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) ''
    laneCUnitInner i

def j1BlockOuter (i : Bool) (v : ℂ) (K : ℕ) : Set ℂ :=
  (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) ''
    laneCUnitOuter i

theorem j1_block_cross_scale_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ) (i : Bool) (v : ℂ)
    (t : ℝ≥0∞) :
    P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (laneBBlockAnnulus i v K) (j1BlockInner i v K) (j1BlockOuter i v K) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * t} =
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - K) z ω)
      (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) < t} := by
  let c : ℂ := v - (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * (⟨1 / 2, 1 / 2⟩ : ℂ)
  have hF : (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) =
      (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) := by
    funext z
    simp only [c, Complex.real_smul]
    ring
  simpa only [hF, laneBBlockAnnulus, j1BlockInner, j1BlockOuter] using
    j1_cross_scale_law P W hW hKn ξ i c t

end SupercriticalLQGUniqueness.B2.DG20Conc
