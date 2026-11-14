import LatticeProb.Prob.LevyProkhorovSampleTransfer
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Outer-measure bounds for finite stopped curves -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A bound between finite-prefix curve laws gives an outer-measure bound for every set of
constant-tail complex rays. The clocks are finite, including zero, and the set need not be
measurable. -/
theorem measure_stoppedRay_le_of_levyProkhorovEDist_lt
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    (f : Ω → C(ℝ≥0, ℂ)) (g : Ξ → C(ℝ≥0, ℂ))
    (T : Ω → ℝ≥0) (U : Ξ → ℝ≥0)
    (hf : Measurable (fun x => normalizedPrefixCurve
      (ReparamDistanceIsometry.complexToEuclideanPath (f x)) (T x)))
    (hg : Measurable (fun y => normalizedPrefixCurve
      (ReparamDistanceIsometry.complexToEuclideanPath (g y)) (U y)))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : levyProkhorovEDist
      (μ.map (fun x => normalizedPrefixCurve
        (ReparamDistanceIsometry.complexToEuclideanPath (f x)) (T x)))
      (ν.map (fun y => normalizedPrefixCurve
        (ReparamDistanceIsometry.complexToEuclideanPath (g y)) (U y))) <
      ENNReal.ofReal δ) (A : Set (ℝ≥0 → ℂ)) :
    μ {x | (fun t => f x (min t (T x))) ∈ A} ≤
      ν {y | ∃ p ∈ A, ReparamEDist.reparamEDist
        (fun t => g y (min t (U y))) p < ENNReal.ofReal (δ + ε)} +
        ENNReal.ofReal δ := by
  refine (measure_le_exists_edist_lt_of_levyProkhorovEDist_lt μ ν _ _ hf hg hδ hε h
    {x | (fun t => f x (min t (T x))) ∈ A}).trans ?_
  apply add_le_add ?_ le_rfl
  apply measure_mono
  rintro y ⟨x, hx, hxy⟩
  refine ⟨(fun t => f x (min t (T x))), hx, ?_⟩
  rw [ReparamDistanceIsometry.complex_stoppedRay_eq_normalizedPrefixCurve]
  exact hxy

end LatticeProb
