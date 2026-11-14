import LatticeProb.Prob.FiniteCurveRawEventTransfer

/-! # Outer-measure bounds for almost surely finite stopped curves -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- The finite-prefix law bound also applies to extended clocks that are finite almost surely.
The original ray is retained on the exceptional event of an infinite clock. -/
theorem measure_extendedStoppedRay_le_of_levyProkhorovEDist_lt
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    (f : Ω → C(ℝ≥0, ℂ)) (g : Ξ → C(ℝ≥0, ℂ))
    (T : Ω → ℝ≥0∞) (U : Ξ → ℝ≥0∞)
    (hT : ∀ᵐ x ∂μ, T x ≠ ⊤) (hU : ∀ᵐ y ∂ν, U y ≠ ⊤)
    (hf : Measurable (fun x => normalizedPrefixCurve
      (ReparamDistanceIsometry.complexToEuclideanPath (f x)) (T x).toNNReal))
    (hg : Measurable (fun y => normalizedPrefixCurve
      (ReparamDistanceIsometry.complexToEuclideanPath (g y)) (U y).toNNReal))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : levyProkhorovEDist
      (μ.map (fun x => normalizedPrefixCurve
        (ReparamDistanceIsometry.complexToEuclideanPath (f x)) (T x).toNNReal))
      (ν.map (fun y => normalizedPrefixCurve
        (ReparamDistanceIsometry.complexToEuclideanPath (g y)) (U y).toNNReal)) <
      ENNReal.ofReal δ) (A : Set (ℝ≥0 → ℂ)) :
    μ {x | (fun t => f x (if T x = ⊤ then t else min t (T x).toNNReal)) ∈ A} ≤
      ν {y | ∃ p ∈ A, ReparamEDist.reparamEDist
        (fun t => g y (if U y = ⊤ then t else min t (U y).toNNReal)) p <
          ENNReal.ofReal (δ + ε)} + ENNReal.ofReal δ := by
  calc
    μ {x | (fun t => f x (if T x = ⊤ then t else min t (T x).toNNReal)) ∈ A} =
        μ {x | (fun t => f x (min t (T x).toNNReal)) ∈ A} := by
          apply measure_congr
          filter_upwards [hT] with x hx
          simp only [ite_eq_right hx]
    _ ≤ ν {y | ∃ p ∈ A, ReparamEDist.reparamEDist
        (fun t => g y (min t (U y).toNNReal)) p < ENNReal.ofReal (δ + ε)} +
        ENNReal.ofReal δ :=
      measure_stoppedRay_le_of_levyProkhorovEDist_lt μ ν f g
        (fun x => (T x).toNNReal) (fun y => (U y).toNNReal) hf hg hδ hε h A
    _ = ν {y | ∃ p ∈ A, ReparamEDist.reparamEDist
        (fun t => g y (if U y = ⊤ then t else min t (U y).toNNReal)) p <
          ENNReal.ofReal (δ + ε)} + ENNReal.ofReal δ := by
      congr 1
      apply measure_congr
      filter_upwards [hU] with y hy
      simp only [ite_eq_right hy]

end LatticeProb
