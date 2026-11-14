/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceFull at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallFullUpperRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceNumeric

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

def j1SmallFullLowerEvent {Ω : Type u} [MeasurableSpace Ω] (ξ : ℝ)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n : ℕ) (i : Bool) (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | ENNReal.ofReal
      (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
      crossLenIn ξ (fun z => phiMN W P 0 n z ω)
        (laneBBlockAnnulus i (T20.dyCenter K b) K)
        (j1BlockInner i (T20.dyCenter K b) K)
        (j1BlockOuter i (T20.dyCenter K b) K) <
      ENNReal.ofReal (T⁻¹ * ((2 : ℝ)⁻¹ ^ K * L))}

def j1SmallFullUpperEvent {Ω : Type u} [MeasurableSpace Ω]
    (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (hW : IsWhiteNoise P W) (K n : ℕ) (i : Bool)
    (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | ENNReal.ofReal (T * ((2 : ℝ)⁻¹ ^ K * L)) <
      ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
          ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (laneBBlockAround i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K)}

end SupercriticalLQGUniqueness.B2.DG20Conc
