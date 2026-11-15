import LatticeProb.Prob.CorrelatedBMWedgeExit
import LatticeProb.Prob.CorrelatedBMPlanarHeatBridge
import LatticeProb.Prob.CorrelatedBMStart

/-! # Killed heat density for a symmetric Brownian wedge -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- The complex form of the symmetric open wedge. -/
def complexSymmetricWedge (a b : ℝ) : Set ℂ :=
  {z | |b * z.im| < a * z.re}

/-- The complex symmetric wedge is open. -/
theorem isOpen_complexSymmetricWedge (a b : ℝ) : IsOpen (complexSymmetricWedge a b) := by
  apply isOpen_lt <;> fun_prop

/-- The strict wedge survival probability is the total killed heat mass. -/
theorem measure_openSymmetricWedgeBarrier_eq_lintegral_killedHeat
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ)
    (a b q : ℝ) (ha : a ≠ 0) (T : ℝ≥0) (hT : T ≠ 0) :
    μ (openSymmetricWedgeBarrier a b q T) =
      ∫⁻ w, ENNReal.ofReal (killedHeat (complexSymmetricWedge a b) T (q / a : ℝ) w) := by
  have hk := lintegral_killedHeat_eq (isOpen_complexSymmetricWedge a b) hT
    (isPlanarBM_forwardPlanarPath hμ) (q / a : ℝ) MeasurableSet.univ
  simp only [Measure.restrict_univ, mem_univ, true_and] at hk
  rw [hk]
  apply measure_congr
  filter_upwards [ae_forall_lrCoord_zero_eq_zero hμ] with ω hω
  have h0 := hω 0
  have h1 := hω 1
  apply propext
  constructor
  · intro h s hs
    have ht := h s ⟨NNReal.coe_nonneg _, by exact_mod_cast hs⟩
    simpa [complexSymmetricWedge, openSymmetricWedge, forwardPlanarPath, wedgeStartedPath, coneIncr, h0, h1,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] using
      (mem_openSymmetricWedge_iff a b q ha s ω).2 ht
  · intro h t ht
    let s : ℝ≥0 := ⟨t, ht.1⟩
    have hs : s ≤ T := by exact_mod_cast ht.2
    have hm := h s hs
    apply (mem_openSymmetricWedge_iff a b q ha s ω).1
    simpa [complexSymmetricWedge, openSymmetricWedge, forwardPlanarPath, wedgeStartedPath, coneIncr,
      h0, h1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] using hm

/-- The same identity applies to a whitened correlated Brownian pair. -/
theorem measure_openSymmetricWedgeBarrier_whitened_eq_lintegral_killedHeat
    {γ : ℝ} {μ : Measure Path2} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsCorrelatedBM2 γ μ) (r a b q : ℝ) (ha : a ≠ 0)
    (T : ℝ≥0) (hT : T ≠ 0) :
    (μ.map (whitenAt γ r)) (openSymmetricWedgeBarrier a b q T) =
      ∫⁻ w, ENNReal.ofReal (killedHeat (complexSymmetricWedge a b) T (q / a : ℝ) w) :=
  measure_openSymmetricWedgeBarrier_eq_lintegral_killedHeat
    (isCorrelatedBM2_map_whitenAt hγ0 hγ2 r hμ) a b q ha T hT

end LatticeProb.CorrelatedBM
