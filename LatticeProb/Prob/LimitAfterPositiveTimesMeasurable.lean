import LatticeProb.Prob.UniformLimitAfterPositiveTimes

/-!
# Measurability of the limit after positive times

Let `a ω k t` (`ω` in a measurable space, `k : ℕ`, `t : ℝ≥0`) be measurable in `ω` for every
`k` and `t`. Then at every fixed time the limit increments `incrementLimitAfter (a ω) m t` and the
limit after positive times `limitAfterPositiveTimes (a ω) t` are measurable in `ω`
(`measurable_incrementLimitAfter`, `measurable_limitAfterPositiveTimes`), and so are the events on
which the limits defining them exist (`measurableSet_exists_tendsto_sub_invSuccTime`,
`measurableSet_exists_tendsto_incrementLimitAfter`). The proofs use the measurability of `limUnder`
of a sequence of measurable functions with values in a Polish space
(`MeasureTheory.StronglyMeasurable.limUnder`), which needs no convergence assumption.
-/

open Filter Topology MeasureTheory
open scoped NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {a : Ω → ℕ → ℝ≥0 → ℝ}

theorem measurable_incrementLimitAfter (ha : ∀ k t, Measurable fun ω => a ω k t)
    (m : ℕ) (t : ℝ≥0) : Measurable fun ω => incrementLimitAfter (a ω) m t :=
  (StronglyMeasurable.limUnder (l := atTop)
    (f := fun k ω => a ω k t - a ω k (invSuccTime m))
    fun k => ((ha k t).sub (ha k (invSuccTime m))).stronglyMeasurable).measurable

theorem measurable_limitAfterPositiveTimes (ha : ∀ k t, Measurable fun ω => a ω k t)
    (t : ℝ≥0) : Measurable fun ω => limitAfterPositiveTimes (a ω) t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  simp only [limitAfterPositiveTimes_of_ne_zero _ ht]
  exact (StronglyMeasurable.limUnder (l := atTop)
    (f := fun m ω => incrementLimitAfter (a ω) m t)
    fun m => (measurable_incrementLimitAfter ha m t).stronglyMeasurable).measurable

/-- The event that the increments after the time `δ m` converge at the time `t`. -/
theorem measurableSet_exists_tendsto_sub_invSuccTime (ha : ∀ k t, Measurable fun ω => a ω k t)
    (m : ℕ) (t : ℝ≥0) :
    MeasurableSet {ω | ∃ L, Tendsto (fun k => a ω k t - a ω k (invSuccTime m)) atTop (𝓝 L)} :=
  StronglyMeasurable.measurableSet_exists_tendsto (l := atTop)
    (f := fun k ω => a ω k t - a ω k (invSuccTime m))
    fun k => ((ha k t).sub (ha k (invSuccTime m))).stronglyMeasurable

/-- The event that the limits over `m` defining the limit after positive times exist at the
time `t`. -/
theorem measurableSet_exists_tendsto_incrementLimitAfter
    (ha : ∀ k t, Measurable fun ω => a ω k t) (t : ℝ≥0) :
    MeasurableSet {ω | ∃ L, Tendsto (fun m => incrementLimitAfter (a ω) m t) atTop (𝓝 L)} :=
  StronglyMeasurable.measurableSet_exists_tendsto (l := atTop)
    (f := fun m ω => incrementLimitAfter (a ω) m t)
    fun m => (measurable_incrementLimitAfter ha m t).stronglyMeasurable

end LatticeProb
