import LatticeProb.Prob.CorrelatedBMIndependentHalves
import LatticeProb.Prob.CorrelatedBMWhitening
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatDens

/-! # Planar Brownian motion from an uncorrelated two-sided pair -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MatedCRTHarmonic.MatedCRT LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- Regard the nonnegative half of a two-coordinate path as a complex path. -/
noncomputable def forwardPlanarPath (t : ℝ≥0) (ω : Path2) : ℂ :=
  (lrCoord 0 t ω : ℂ) + (lrCoord 1 t ω : ℂ) * Complex.I

private def coordIndex : Bool → Fin 2
  | false => 0
  | true => 1

private theorem coordProc_forward (p : Bool × ℝ≥0) :
    coordProc forwardPlanarPath p = lrCoord (coordIndex p.1) p.2 := by
  rcases p with ⟨b, t⟩
  cases b <;> ext ω <;> simp [coordProc, forwardPlanarPath, coordIndex]

/-- An uncorrelated two-sided Brownian pair restricts to planar Brownian motion. -/
theorem isPlanarBM_forwardPlanarPath {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) : IsPlanarBM forwardPlanarPath μ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ae_of_all _ fun ω => by
      unfold forwardPlanarPath
      exact ((Complex.continuous_ofReal.comp ((continuous_lrCoord_time 0 ω).comp
        NNReal.continuous_coe)).add ((Complex.continuous_ofReal.comp
        ((continuous_lrCoord_time 1 ω).comp NNReal.continuous_coe)).mul continuous_const))
  · have h := hμ.isGaussianProcess.comp_right (fun p : Bool × ℝ≥0 =>
        (coordIndex p.1, (p.2 : ℝ)))
    convert h using 1
    funext p
    exact coordProc_forward p
  · intro p
    rw [coordProc_forward]
    exact hμ.integral_eq_zero _ _
  · intro p q
    rw [coordProc_forward, coordProc_forward, hμ.covariance_eq]
    rcases p with ⟨b, s⟩
    rcases q with ⟨c, t⟩
    set_option linter.unusedSimpArgs false in
      cases b <;> cases c <;>
      simp [coordIndex, lrCov, twoSidedMin, max_eq_left (NNReal.coe_nonneg _),
        max_eq_right (neg_nonpos.mpr (NNReal.coe_nonneg _)), ← NNReal.coe_min,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        show Real.pi * 2 / 4 = Real.pi / 2 by ring]

/-- Whitening produces a planar Brownian motion on nonnegative times. -/
theorem isPlanarBM_forward_whitened {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hμ : IsCorrelatedBM2 γ μ) (q : ℝ) :
    IsPlanarBM forwardPlanarPath (μ.map (whitenAt γ q)) :=
  isPlanarBM_forwardPlanarPath (isCorrelatedBM2_map_whitenAt hγ0 hγ2 q hμ)

end LatticeProb.CorrelatedBM
