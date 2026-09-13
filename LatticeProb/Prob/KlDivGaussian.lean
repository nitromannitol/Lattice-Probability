/-
The relative entropy between two Gaussians of a common variance.

Mathlib has `InformationTheory.klDiv` and the Gaussian density, but no relative
entropy between two Gaussians.  The one-dimensional value is `m²/(2v)` for means
`0` and `m` and variance `v`; the finite product form is in
`LatticeProb/Prob/KlDivGaussianPi.lean`.
-/
import LatticeProb.Prob.KlDivGaussianAux

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- The relative entropy between two Gaussians of the same variance `v` and means
`0` and `m` is `m²/(2v)`. -/
theorem klDiv_gaussianReal_shift {v : ℝ≥0} (hv : v ≠ 0) (m : ℝ) :
    InformationTheory.klDiv (ProbabilityTheory.gaussianReal 0 v)
        (ProbabilityTheory.gaussianReal m v)
      = ENNReal.ofReal (m ^ 2 / (2 * v)) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : ℝ≥0) < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    exact_mod_cast h
  have hac : ProbabilityTheory.gaussianReal 0 v ≪ ProbabilityTheory.gaussianReal m v :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 hv).trans
      (ProbabilityTheory.gaussianReal_absolutelyContinuous' m hv)
  have hae : MeasureTheory.llr (ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal m v)
      =ᵐ[ProbabilityTheory.gaussianReal 0 v] fun x => (m ^ 2 - 2 * m * x) / (2 * v) := by
    have h1 := llr_gaussianReal_eq hv m
    have h2 : (fun x => Real.log (ProbabilityTheory.gaussianPDFReal 0 v x /
        ProbabilityTheory.gaussianPDFReal m v x))
        = fun x => (m ^ 2 - 2 * m * x) / (2 * v) := by
      funext x; exact log_gaussianPDFReal_div hv m x
    rw [h2] at h1
    exact h1.filter_mono (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 hv).ae_le
  have hint : Integrable (MeasureTheory.llr (ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal m v)) (ProbabilityTheory.gaussianReal 0 v) := by
    have hbase : Integrable (fun x : ℝ => (m ^ 2) / (2 * v) - (2 * m / (2 * v)) * x)
        (ProbabilityTheory.gaussianReal 0 v) :=
      (integrable_const (μ := ProbabilityTheory.gaussianReal 0 v) (c := (m ^ 2) / (2 * v))).sub
        ((ProbabilityTheory.IsGaussian.integrable_id
          (μ := ProbabilityTheory.gaussianReal 0 v)).const_mul (2 * m / (2 * v)))
    refine Integrable.congr hbase ?_
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
  rw [integral_congr_ae hae]
  rw [integral_llr_gaussianReal hv m]
  simp

end LatticeProb
