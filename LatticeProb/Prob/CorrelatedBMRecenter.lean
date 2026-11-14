import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.Prob.CorrelatedBMConeTimes

/-! # Recentring and time reversal of correlated Brownian paths -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Recenter a continuous path at `c` and run time with speed `e`. -/
def recenterPath (c e : ℝ) (ω : Path2) : Path2 :=
  ⟨fun t => ω (c + e * t) - ω c, by fun_prop⟩

/-- Recentring is continuous for the compact-open topology. -/
theorem continuous_recenterPath (c e : ℝ) : Continuous (recenterPath c e) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous (fun p : Path2 × ℝ => p.1 (c + e * p.2) - p.1 c)
  fun_prop

/-- A translated or time-reversed correlated Brownian pair has the same
correlated Brownian covariance and jointly Gaussian coordinate process. -/
theorem isCorrelatedBM2_map_recenterPath {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (c e : ℝ) (he : |e| = 1) :
    IsCorrelatedBM2 γ (μ.map (recenterPath c e)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hΦ : Measurable (recenterPath c e) := (continuous_recenterPath c e).measurable
  have hm : ∀ i t, Measurable (lrCoord i t) := by
    intro i t
    unfold lrCoord
    split_ifs
    · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
    · exact measurable_snd.comp (ContinuousMap.measurable_eval t)
  have hcoord : ∀ i t ω, lrCoord i t (recenterPath c e ω) =
      coneIncr i (c + e * t) c ω := by
    intro i t ω
    fin_cases i <;> rfl
  have hG : IsGaussianProcess
      (fun (p : Fin 2 × ℝ) ω => lrCoord p.1 p.2 (recenterPath c e ω)) μ := by
    apply GaussIndep.isGaussianProcess_of_mem_span hμ.isGaussianProcess
    intro p
    have hfun : (fun ω => lrCoord p.1 p.2 (recenterPath c e ω)) =
        coneIncr p.1 (c + e * p.2) c := funext (hcoord p.1 p.2)
    rw [hfun]
    exact coneIncr_mem_span _ _ _
  have hgm : ∀ I : Finset (Fin 2 × ℝ),
      Measurable fun ω : Path2 => I.restrict (fun p : Fin 2 × ℝ => lrCoord p.1 p.2 ω) :=
    fun I => measurable_pi_iff.2 fun j => hm j.1.1 j.1.2
  refine
    { isProbabilityMeasure := (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 inferInstance
      isGaussianProcess := ⟨fun I => ⟨(hgm I).aemeasurable, ?_⟩⟩
      integral_eq_zero := fun i t => ?_
      covariance_eq := fun i j s t => ?_ }
  · rw [Measure.map_map (hgm I) hΦ]
    exact (hG.hasGaussianLaw I).isGaussian_map
  · rw [integral_map hΦ.aemeasurable (hm i t).aestronglyMeasurable]
    simp_rw [hcoord, coneIncr]
    rw [integral_sub ((hμ.isGaussianProcess.hasGaussianLaw_eval (i, c + e * t)).memLp_two.integrable (by norm_num))
      ((hμ.isGaussianProcess.hasGaussianLaw_eval (i, c)).memLp_two.integrable (by norm_num)),
      hμ.integral_eq_zero, hμ.integral_eq_zero, sub_self]
  · rw [covariance_map_fun (hm i s).aestronglyMeasurable (hm j t).aestronglyMeasurable hΦ.aemeasurable]
    simp_rw [hcoord]
    rw [cov_coneIncr hμ, twoSidedMin_eq_abs]
    congr 1
    have hs : c + e * s - c = e * s := by ring
    have ht : c + e * t - c = e * t := by ring
    have hst : c + e * s - (c + e * t) = e * (s - t) := by ring
    rw [hs, ht, hst, abs_mul, abs_mul, abs_mul, he]
    simp

end LatticeProb.CorrelatedBM
