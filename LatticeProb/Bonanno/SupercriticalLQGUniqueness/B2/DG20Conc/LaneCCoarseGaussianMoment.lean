/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCoarseGaussianMoment at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxLogMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundMeas
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Mul
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BMom
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPowerRate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMain
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.MeasurableIntegral
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Straight
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L9Tail

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneC_coarse_phi_exp_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (K : ℕ) (b : ℤ × ℤ) (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (a * phiMN W P 0 K (T20.dyCenter K b) ω)) ∂P ≤
        ENNReal.ofReal
          (Real.exp (((K : ℝ) * Real.log 2) * a ^ 2 / 2)) := by
  obtain ⟨v, hv, hX⟩ := hasLaw_phiMN hW K (T20.dyCenter K b)
  have hV : 0 ≤ (K : ℝ) * Real.log 2 := by positivity
  have hv' : (v : ℝ) ≤ (Real.sqrt ((K : ℝ) * Real.log 2)) ^ 2 := by
    rw [Real.sq_sqrt hV]
    exact hv.le
  convert lintegral_exp_gauss_le hX hv' a using 1
  rw [Real.sq_sqrt hV]

end SupercriticalLQGUniqueness.B2.DG20Conc
