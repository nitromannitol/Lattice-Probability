import LatticeProb.Topology.ClippedPrefixClock
import LatticeProb.Topology.CurveClockCost
import LatticeProb.Prob.NormalizedPrefixCurve

/-! # Comparing prefixes along clipped clocks -/

set_option autoImplicit false
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- The distance between positive finite prefixes is bounded by their pointwise distance
along continuous nondecreasing clocks that reach both terminal times. -/
theorem normalizedPrefixCurve_edist_le_iSup_clipped {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T U : ℝ≥0)
    (hT : 0 < T) (hU : 0 < U) (h k : C(unitInterval, ℝ≥0))
    (hh : Monotone h) (hh0 : h 0 = 0) (hh1 : T ≤ h 1)
    (hk : Monotone k) (hk0 : k 0 = 0) (hk1 : U ≤ k 1) :
    edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g U) ≤
      ⨆ t : unitInterval, edist (f (min (h t) T)) (g (min (k t) U)) := by
  have H := curveSpace_edist_le_iSup_of_monotone_clocks
    (normalizedPathPrefix f T) (normalizedPathPrefix g U)
    (clippedPrefixClock h T hT) (clippedPrefixClock k U hU)
    (clippedPrefixClock_monotone h T hT hh) (clippedPrefixClock_zero h T hT hh0)
    (clippedPrefixClock_one h T hT hh1)
    (clippedPrefixClock_monotone k U hU hk) (clippedPrefixClock_zero k U hU hk0)
    (clippedPrefixClock_one k U hU hk1)
  refine H.trans ?_
  apply iSup_le
  intro t
  apply le_iSup_of_le t
  have hf : normalizedPathPrefix f T (clippedPrefixClock h T hT t) =
      f (min (h t) T) := by
    apply congrArg f
    apply Subtype.ext
    change (clippedPrefixClock h T hT t : ℝ) * (T : ℝ) = (min (h t) T : ℝ)
    rw [mul_comm, mul_clippedPrefixClock]
  have hg : normalizedPathPrefix g U (clippedPrefixClock k U hU t) =
      g (min (k t) U) := by
    apply congrArg g
    apply Subtype.ext
    change (clippedPrefixClock k U hU t : ℝ) * (U : ℝ) = (min (k t) U : ℝ)
    rw [mul_comm, mul_clippedPrefixClock]
  rw [hf, hg]

end LatticeProb
