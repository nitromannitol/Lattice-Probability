import LatticeProb.Topology.LocalizedSegmentScale

/-! # Diameter-to-measure bounds for localized curve segments -/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- Simultaneous first-exit measure bounds control the diameter-to-measure
ratio of every localized segment. The scale may depend on the segment. -/
theorem localized_segment_ratio_le_of_first_exit_bounds
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (η : ℝ → X) (hη : Continuous η)
    (z : X) {ε t₀ L U C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (hleft : ¬ η '' Icc (t₀ - ε / 2) t₀ ⊆ ball z L)
    (hright : ¬ η '' Icc t₀ (t₀ + ε / 2) ⊆ ball z L)
    (hwindow : η '' Icc (t₀ - ε) (t₀ + ε) ⊆ closedBall z U)
    (htrace : ∀ k : ℤ, Real.log L - 1 < (k : ℝ) → (k : ℝ) ≤ Real.log U →
      ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / C) ≤
        min (μ (η '' Icc (sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ ball z (Real.exp k)}) t₀))
          (μ (η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z (Real.exp k)})))) :
    ∀ s ∈ Icc t₀ (t₀ + ε),
      ENNReal.ofReal (diam (η '' Icc (s - ε) s) ^ 2) /
        μ (η '' Icc (s - ε) s) ≤ ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * C) := by
  intro s hs
  obtain ⟨k, _, _, hdiam, hmass⟩ :=
    localized_segment_scale_and_measure μ η hη z hL hleft hright hwindow
      (fun k => ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / C)) htrace s hs
  have hdnonneg : 0 ≤ diam (η '' Icc (s - ε) s) := diam_nonneg
  have hd : diam (η '' Icc (s - ε) s) ^ 2 ≤
      (2 * Real.exp 1) ^ 2 * Real.exp (k : ℝ) ^ 2 := by
    have hsquare : diam (η '' Icc (s - ε) s) ^ 2 ≤
        (2 * Real.exp ((k : ℝ) + 1)) ^ 2 := by nlinarith [Real.exp_pos ((k : ℝ) + 1)]
    rw [Real.exp_add] at hsquare
    nlinarith [sq_nonneg (Real.exp (k : ℝ) * Real.exp 1)]
  apply ENNReal.div_le_of_le_mul
  calc
    ENNReal.ofReal (diam (η '' Icc (s - ε) s) ^ 2) ≤
        ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * Real.exp (k : ℝ) ^ 2) :=
      ENNReal.ofReal_le_ofReal hd
    _ = ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * C) *
        ENNReal.ofReal (Real.exp (k : ℝ) ^ 2 / C) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * C) *
        μ (η '' Icc (s - ε) s) := by gcongr

end LatticeProb
