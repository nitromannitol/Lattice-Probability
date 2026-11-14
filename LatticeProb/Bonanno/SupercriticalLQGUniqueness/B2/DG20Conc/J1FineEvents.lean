/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FineEvents at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FineStart

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

def j1SmallFineLowerEvent {Ω : Type u} [MeasurableSpace Ω] (ξ : ℝ)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n : ℕ) (i : Bool) (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (laneBBlockAnnulus i (T20.dyCenter K b) K)
      (j1BlockInner i (T20.dyCenter K b) K)
      (j1BlockOuter i (T20.dyCenter K b) K) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * ENNReal.ofReal (T⁻¹ * L)}

def j1SmallFineUpperEvent {Ω : Type u} [MeasurableSpace Ω] (ξ : ℝ)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (hW : IsWhiteNoise P W) (K n : ℕ) (hKn : K ≤ n)
    (i : Bool) (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * ENNReal.ofReal (T * L) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (laneBBlockAround i (T20.dyCenter K b) K)
        (j1BlockInner i (T20.dyCenter K b) K)
        (j1BlockOuter i (T20.dyCenter K b) K)}

def j1RoundFineLowerEvent {Ω : Type u} [MeasurableSpace Ω] (ξ : ℝ)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n m : ℕ) (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (j1SourceCross K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * ENNReal.ofReal (T⁻¹ * L)}

def j1RoundFineUpperEvent {Ω : Type u} [MeasurableSpace Ω] (ξ : ℝ)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (hW : IsWhiteNoise P W) (K n m : ℕ) (hKn : K ≤ n)
    (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * ENNReal.ofReal (T * L) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)}

theorem j1_fine_prob_scale_eq (K : ℕ) (C f : ℝ) :
    ENNReal.ofReal ((5 : ℝ)^K) * ENNReal.ofReal (C * f) =
      ENNReal.ofReal (C * (5 : ℝ)^K * f) := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (5 : ℝ)^K)]
  congr 1
  ring

end SupercriticalLQGUniqueness.B2.DG20Conc
