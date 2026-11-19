import LatticeProb.Prob.LimitAfterPositiveTimesShift

/-!
# The limit after positive times as a pointwise limit

For a sequence of functions `a k : ℝ≥0 → ℝ`, `limitAfterPositiveTimes a` is defined through the
limits of the increments `a k t - a k s` for positive `s`. When the functions are continuous, vanish
at time `0` and are uniformly Cauchy on every compact interval `[0, N]`, the sequence converges
pointwise and the limit after positive times is this pointwise limit.

## Main statement

* `tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn`.
-/

open Filter Topology Set
open scoped NNReal

namespace LatticeProb

/-- **The limit after positive times as a pointwise limit.** If continuous functions `a k` vanishing
at `0` are uniformly Cauchy on every `[0, N]`, then `a k t` converges to the limit after positive
times at every time `t`. -/
theorem tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn {a : ℕ → ℝ≥0 → ℝ}
    (hcont : ∀ k, Continuous (a k)) (h0 : ∀ k, a k 0 = 0)
    (hU : ∀ N : ℕ, UniformCauchySeqOn a atTop (Icc 0 (N : ℝ≥0))) (t : ℝ≥0) :
    Tendsto (fun k => a k t) atTop (𝓝 (limitAfterPositiveTimes a t)) := by
  have hcs : ∀ t : ℝ≥0, CauchySeq fun k => a k t := fun t =>
    (hU ⌈(t : ℝ≥0)⌉₊).cauchySeq ⟨zero_le, Nat.le_ceil t⟩
  choose G hG using fun t => cauchySeq_tendsto_of_complete (hcs t)
  have hG0 : G 0 = 0 := tendsto_nhds_unique (hG 0) (by simp [h0])
  have hU1 : UniformCauchySeqOn a atTop (Icc 0 1) := by simpa using hU 1
  have hunif : TendstoUniformlyOn a G atTop (Icc 0 1) :=
    hU1.tendstoUniformlyOn_of_tendsto fun x _ => hG x
  have hGc : ContinuousOn G (Icc 0 1) :=
    hunif.continuousOn (Eventually.of_forall fun k => (hcont k).continuousOn).frequently
  have hnhds : Icc (0 : ℝ≥0) 1 ∈ 𝓝 (0 : ℝ≥0) :=
    mem_of_superset (Iio_mem_nhds zero_lt_one) fun x hx => ⟨zero_le, le_of_lt hx⟩
  rw [limitAfterPositiveTimes_eq_sub_of_tendsto hG
    (hGc.continuousAt hnhds).continuousWithinAt t, hG0, sub_zero]
  exact hG t

end LatticeProb
