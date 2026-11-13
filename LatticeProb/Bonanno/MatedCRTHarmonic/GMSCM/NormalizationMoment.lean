/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.NormalizationMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.RandomMixture
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.GaussianSq
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc

/-!
# The random normalization difference has a small exponential-square moment

For a whole-plane GFF, the difference between circle averages on two fixed
circles is a centred Gaussian. Its square therefore has an exponential moment
at some positive rate. This is the integrability input for the random cutoff
coefficient in continuation c1.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory LQGMetric LQGMetric.CircleAvg
open scoped NNReal

namespace MatedCRTHarmonic.GMSCM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The random scalar `h_R(z₀) - h_1(0)` has `E exp(t c²) < ∞` for
some `t > 0`, for any two fixed positive radii. -/
theorem exists_normalization_increment_exp_sq (hh : IsWholePlaneGFF h P)
    {R : ℝ} (hR : 0 < R) (z₀ : ℂ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun ω => Real.exp (t * (cInc h R z₀ 1 0 ω) ^ 2)) P := by
  let v : ℝ≥0 := (incCov z₀ R 0 1 z₀ R 0 1).toNNReal
  have hmap : P.map (cInc h R z₀ 1 0) = ProbabilityTheory.gaussianReal 0 v :=
    (map_cInc hh hR (by norm_num) z₀ 0).1
  let t : ℝ := 1 / (4 * ((v : ℝ) + 1))
  have hv0 : 0 ≤ (v : ℝ) := v.2
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht : 2 * t * (v : ℝ) < 1 := by
    dsimp [t]
    have hden : 0 < 4 * ((v : ℝ) + 1) := by positivity
    rw [show 2 * (1 / (4 * ((v : ℝ) + 1))) * (v : ℝ) =
      (2 * (v : ℝ)) / (4 * ((v : ℝ) + 1)) by ring]
    exact (div_lt_iff₀ hden).2 (by linarith)
  refine ⟨t, htpos, ?_⟩
  have hi : Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (P.map (cInc h R z₀ 1 0)) := by
    rw [hmap]
    exact GMSAppA.integrable_exp_mul_sq_gaussianReal ht
  exact hi.comp_measurable (measurable_cInc hh R z₀ 1 0)

end MatedCRTHarmonic.GMSCM
