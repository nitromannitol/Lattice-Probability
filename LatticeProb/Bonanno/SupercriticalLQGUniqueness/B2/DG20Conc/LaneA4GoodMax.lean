/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4GoodMax at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Gaussian
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondIndepMoment
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsiBlock
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_good_conditional_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (κ : Measure Ω) (F E H : Set Ω)
    (X Y : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hH : MeasurableSet H) (hX : Measurable X)
    (hhit : F ∩ E ⊆ H)
    (hregular : ∀ ω ∈ E, Y ω ≤ c * X ω) :
    (∫⁻ ω, (F ∩ E).indicator Y ω ∂κ) ≤
      c * (∫⁻ ω, H.indicator X ω ∂κ) := by
  have hpoint : ∀ ω,
      (F ∩ E).indicator Y ω ≤ c * H.indicator X ω := by
    intro ω
    by_cases hω : ω ∈ F ∩ E
    · have hHω : ω ∈ H := hhit hω
      simpa only [Set.indicator_of_mem hω, Set.indicator_of_mem hHω] using
        hregular ω hω.2
    · simp only [Set.indicator_of_notMem hω]
      exact bot_le
  calc
    _ ≤ ∫⁻ ω, c * H.indicator X ω ∂κ := lintegral_mono hpoint
    _ = c * (∫⁻ ω, H.indicator X ω ∂κ) :=
      lintegral_const_mul c (hX.indicator hH)

 


end SupercriticalLQGUniqueness.B2.DG20Conc
