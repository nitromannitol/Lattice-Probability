import LatticeProb.Prob.CorrelatedBMForwardPositive
import LatticeProb.Prob.CorrelatedBMOpenWedgeBridge

/-! # Closed forward barriers for correlated Brownian motion -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A subcritical open-wedge estimate bounds the closed joint barrier after
whitening, when the wedge coefficients have the indicated angle. -/
theorem jointZeroBarrier_le_of_wedge_angle {γ θ p r : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hr : 0 < r) (hrp : r < p)
    (hpθ : p * θ < Real.pi)
    (ha : Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 = Real.sin (θ / 2))
    (hb : Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2 = Real.cos (θ / 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {μ : Measure Path2}, IsCorrelatedBM2 γ μ →
      ∀ (q : ℝ) (T : ℝ≥0), 0 < q → 0 < (T : ℝ) →
        μ (jointZeroBarrier q T) ≤ ENNReal.ofReal
          (K * (((2 * q) / (Real.sin (θ / 2) * Real.sqrt 2)) /
            Real.sqrt (T : ℝ)) ^ r) := by
  obtain ⟨K, hK, hbound⟩ :=
    forward_wedge_barrier_subcritical_positive hθ0 hθπ hr hrp hpθ
  refine ⟨K, hK, ?_⟩
  intro μ hμ q T hq hT
  have hw := isCorrelatedBM2_map_whitenAt hγ0 hγ2 0 hμ
  let : IsProbabilityMeasure (μ.map (whitenAt γ 0)) := hw.isProbabilityMeasure
  have hreal := hbound hw (2 * q) T (by positivity) hT
  have henn := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_measureReal (measure_ne_top _ _)] at henn
  have hsubset := measure_jointZeroBarrier_le_open_wedge (μ := μ) hγ0 hγ2 q T q hq
  rw [ha, hb, show q + q = 2 * q by ring] at hsubset
  exact hsubset.trans henn

end LatticeProb.CorrelatedBM
