import LatticeProb.Prob.GaussianFreezing

/-! # Independent barriers and Gaussian windows

A Gaussian increment independent of two independent barrier events satisfies a
uniform window estimate even when the window center depends on both barriers.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Independent barriers and a Gaussian window with a random center have
probability at most the product of the barrier probabilities and the uniform
Gaussian interval bound. -/
theorem measure_inter_inter_abs_add_le {Ω : Type*} {𝓕 mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝓕 : 𝓕 ≤ mΩ) {A B : Set Ω}
    (hA : MeasurableSet[𝓕] A) (hB : MeasurableSet[𝓕] B) (hAB : IndepSet A B P)
    {Y Z : Ω → ℝ} (hY : Measurable[𝓕] Y) (hZmeas : Measurable Z)
    {v : ℝ≥0} (hv : v ≠ 0) (hZ : P.map Z = gaussianReal 0 v)
    (hind : Indep 𝓕 (MeasurableSpace.comap Z inferInstance) P) {r : ℝ} (hr : 0 ≤ r) :
    P ((A ∩ B) ∩ {ω | |Y ω + Z ω| ≤ r}) ≤
      P A * P B * ENNReal.ofReal (2 * r / √(2 * Real.pi * v)) := by
  have h := measure_inter_add_mem_Icc_le (P := P) h𝓕 (hA.inter hB) hY hZmeas hv hZ hind
    (a := -r) (b := r) (by linarith)
  have hset : {ω | |Y ω + Z ω| ≤ r} = {ω | Y ω + Z ω ∈ Set.Icc (-r) r} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  rw [hAB.measure_inter_eq_mul] at h
  rw [hset]
  convert h using 1; congr 2; ring

end LatticeProb
