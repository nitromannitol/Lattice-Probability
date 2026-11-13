/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FiniteDensityMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.GaussianTilt
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3B
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLimit

/-!
# Measurability of the finite circle Wick density

The finite circle Wick density is jointly measurable in the field sample and its centre. The
random increment is jointly measurable by the existing mollified-circle-average measurability
lemma. Its deterministic variance term is measurable by identifying it with the integral of
the square of that increment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The finite mollified increment, as a jointly measurable function of the sample and centre. -/
private lemma measurable_finiteCircleIncrement (hh : IsNormalizedWPGFF h P) (n : ℕ) (ε : ℝ) :
    Measurable fun p : Ω × ℂ =>
      mollAvg (h p.1) n p.2 ε - mollAvg (h p.1) n 0 1 := by
  have hleft : Measurable fun p : Ω × ℂ => mollAvg (h p.1) n p.2 ε := by
    exact MatedCRTHarmonic.MoTPort.ConeArea3.measurable_mollAvg n ε |>.comp
      ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)
  have hright : Measurable fun p : Ω × ℂ => mollAvg (h p.1) n 0 1 := by
    exact MatedCRTHarmonic.MoTPort.ConeArea3.measurable_mollAvg n 1 |>.comp
      ((hh.1.measurable.comp measurable_fst).prodMk (measurable_const (a := (0 : ℂ))))
  exact hleft.sub hright

/-- The variance of the finite circle increment is measurable in its centre. -/
private lemma measurable_finiteCircleVariance (hh : IsNormalizedWPGFF h P) (n : ℕ)
    (ε : ℝ) : Measurable fun z : ℂ =>
      logCov (finiteCircleIndex n z ε).1 (finiteCircleIndex n z ε).1 := by
  letI := hh.1.gaussian.isProbabilityMeasure
  let inc : Ω × ℂ → ℝ := fun p =>
    mollAvg (h p.1) n p.2 ε - mollAvg (h p.1) n 0 1
  have hinc : Measurable inc := measurable_finiteCircleIncrement hh n ε
  have hswap : Measurable fun p : ℂ × Ω => inc (p.2, p.1) :=
    hinc.comp measurable_swap
  have hsq : Measurable fun p : ℂ × Ω => inc (p.2, p.1) ^ 2 :=
    (continuous_pow 2).measurable.comp hswap
  have hInt : Measurable fun z : ℂ => ∫ ω, inc (ω, z) ^ 2 ∂P := by
    exact (hsq.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have heq : (fun z : ℂ => ∫ ω, inc (ω, z) ^ 2 ∂P) =
      fun z => logCov (finiteCircleIndex n z ε).1 (finiteCircleIndex n z ε).1 := by
    funext z
    dsimp [inc]
    exact integral_sq_mollAvg_sub hh.1 n z ε n 0 1
  rw [← heq]
  exact hInt

/-- The Wick density for a finite circle regularization is jointly measurable on `Ω × ℂ`. -/
theorem measurable_finiteCircleDensity (hh : IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ)
    (ε : ℝ) :
    Measurable fun p : Ω × ℂ =>
      finiteCircleDensity (h := h) γ n p.2 ε p.1 := by
  have hinc := measurable_finiteCircleIncrement hh n ε
  have hvar := measurable_finiteCircleVariance hh n ε
  exact ENNReal.measurable_ofReal.comp <| Real.measurable_exp.comp <|
    (measurable_const.mul hinc).sub
      ((measurable_const.mul (hvar.comp measurable_snd)).div_const 2)

end MatedCRTHarmonic.ConeLemmaA10

