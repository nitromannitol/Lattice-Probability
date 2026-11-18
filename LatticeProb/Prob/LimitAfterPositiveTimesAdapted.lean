import LatticeProb.Prob.UniformLimitAfterPositiveTimes

/-!
# Adaptedness of the limit after positive times

The limit after positive times `limitAfterPositiveTimes a t = lim_m lim_k (a k t - a k (δ m))`,
`δ m = (m + 1)⁻¹`, at a time `t > 0` only depends on the approximants `a k` at the times `v ≤ t`:
the outer limit over `m` does not change when finitely many indices are dropped, and `δ m ≤ t` for
all large `m` (`limitAfterPositiveTimes_eq_limUnder_add`). Consequently, if the approximants
`a ω k v` at all times `v ≤ t` are measurable for a σ-algebra, so is the limit after positive times
at `t` (`measurable_limitAfterPositiveTimes_of_le`), and the limit of approximants adapted to a
filtration is adapted to it (`measurable_limitAfterPositiveTimes_filtration`).

## Main statements

* `limitAfterPositiveTimes_eq_limUnder_add`;
* `measurable_limitAfterPositiveTimes_of_le`;
* `measurable_limitAfterPositiveTimes_filtration`.
-/

open Filter Topology MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- Dropping the first `N` terms of a sequence does not change its `limUnder` along `atTop`. -/
theorem limUnder_atTop_comp_add {α : Type*} [TopologicalSpace α] [Nonempty α] (f : ℕ → α)
    (N : ℕ) : limUnder atTop (fun m => f (m + N)) = limUnder atTop f := by
  unfold limUnder
  rw [show (fun m => f (m + N)) = f ∘ fun m => m + N from rfl, ← Filter.map_map,
    Filter.map_add_atTop_eq_nat]

/-- At a positive time, the limit after positive times is the limit of the increments after the
times `δ (m + N)`, for any `N`. -/
theorem limitAfterPositiveTimes_eq_limUnder_add (a : ℕ → ℝ≥0 → ℝ) {t : ℝ≥0} (ht : t ≠ 0)
    (N : ℕ) :
    limitAfterPositiveTimes a t = limUnder atTop fun m => incrementLimitAfter a (m + N) t := by
  rw [limitAfterPositiveTimes_of_ne_zero a ht]
  exact (limUnder_atTop_comp_add (fun m => incrementLimitAfter a m t) N).symm

variable {Ω : Type*} {a : Ω → ℕ → ℝ≥0 → ℝ}

/-- **The limit after positive times at `t` only uses the approximants up to `t`.** If at a time
`t > 0` the approximants `a ω k v` at all times `v ≤ t` are measurable for a σ-algebra `m`, then
the limit after positive times `limitAfterPositiveTimes (a ω) t` is `m`-measurable. -/
theorem measurable_limitAfterPositiveTimes_of_le {m : MeasurableSpace Ω} {t : ℝ≥0} (ht : 0 < t)
    (ha : ∀ k v, v ≤ t → Measurable[m] fun ω => a ω k v) :
    Measurable[m] fun ω => limitAfterPositiveTimes (a ω) t := by
  obtain ⟨N, hN⟩ := exists_invSuccTime_le ht
  have hinc : ∀ j, Measurable[m] fun ω => incrementLimitAfter (a ω) (j + N) t := by
    intro j
    have hle : invSuccTime (j + N) ≤ t :=
      (invSuccTime_antitone (Nat.le_add_left N j)).trans hN
    exact (StronglyMeasurable.limUnder (l := atTop)
      (f := fun k ω => a ω k t - a ω k (invSuccTime (j + N)))
      fun k => ((ha k t le_rfl).sub (ha k _ hle)).stronglyMeasurable).measurable
  have heq : (fun ω => limitAfterPositiveTimes (a ω) t) =
      fun ω => limUnder atTop fun j => incrementLimitAfter (a ω) (j + N) t :=
    funext fun ω => limitAfterPositiveTimes_eq_limUnder_add (a ω) ht.ne' N
  rw [heq]
  exact (StronglyMeasurable.limUnder (l := atTop)
    (f := fun j ω => incrementLimitAfter (a ω) (j + N) t)
    fun j => (hinc j).stronglyMeasurable).measurable

/-- **Adaptedness of the limit after positive times.** If the approximants `a ω k` are adapted to a
filtration `𝓕` indexed by `ℝ≥0`, so is the limit after positive times: at every time `t`, the
function `ω ↦ limitAfterPositiveTimes (a ω) t` is `𝓕 t`-measurable. -/
theorem measurable_limitAfterPositiveTimes_filtration {m₀ : MeasurableSpace Ω}
    (𝓕 : Filtration ℝ≥0 m₀) (ha : ∀ k v, Measurable[𝓕 v] fun ω => a ω k v) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => limitAfterPositiveTimes (a ω) t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [limitAfterPositiveTimes_zero]
    exact measurable_const
  exact measurable_limitAfterPositiveTimes_of_le (pos_iff_ne_zero.2 ht)
    fun k v hv => (ha k v).mono (𝓕.mono hv) le_rfl

end LatticeProb
