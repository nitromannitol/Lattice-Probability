import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Last-time decomposition along a decreasing sequence of σ-algebras

Let `G : ℕ → MeasurableSpace Ω` be an antitone sequence of sub-σ-algebras (a reverse
filtration) and let `Y m` be `G m`-measurable events. For `n ≤ m ≤ N`, the event
`Y m \ ⋃_{m < j ≤ N} Y j` ("`m` is the last index in `[n, N]` at which `Y` occurs") is again
`G m`-measurable, because every `Y j` with `j ≥ m` is `G j ⊆ G m`-measurable; so the last index
is a reverse stopping time. Suppose that each `G m`-measurable event `A ⊆ Y m` satisfies
`μ A ≤ c * μ (A ∩ T m)` (on `Y m`, conditionally on `G m`, a second event `T m` has
probability at least `1 / c`). Summing over the disjoint last-time pieces gives
`μ (⋃_{m ∈ [n, N]} Y m) ≤ c * μ (⋃_{m ∈ [n, N]} T m)`, hence `μ (⋃_{m ≥ n} Y m) ≤
c * μ (⋃_{m ≥ n} T m)`; if the right side tends to `0`, then almost surely `Y m` occurs for only
finitely many `m`.

This is the probabilistic part of the descendant half of Lemma 2.8 in Gwynne, Miller and
Sheffield, *An invariance principle for ergodic scale-free random environments* (arXiv
1807.07515): there `G m` is the σ-algebra of the cell configuration and the dyadic system viewed
modulo translation within the `m`-th mass-capped origin square, `Y m` is the event that some
dyadic descendant of bounded depth of that square is bad, and `T m` is the event that the
origin-containing square of the chosen depth is bad, which by the dyadic re-sampling property has
conditional probability at least `4 ^ (-l)`. No measurability of `T m` is needed.

## Main statements

* `LatticeProb.ReverseLastTime.measure_biUnion_Icc_le_mul`: the finite-window bound.
* `measure_biUnion_ge_le_mul`: the bound for the tail union `⋃_{m ≥ n} Y m`.
* `ae_eventually_not_mem`: if `μ (⋃_{m ≥ n} T m) → 0` and `c ≠ ∞`, then almost surely
  `Y m` fails for all large `m`.
* `ae_eventually_not_mem_of_ae`: the same from "almost surely `T m` fails for all large `m`",
  for a finite measure and measurable `T m`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb.ReverseLastTime

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The last-time piece: `ω ∈ Y m` and `ω ∉ Y j` for every `j ∈ (m, N]`. -/
def lastPiece (Y : ℕ → Set Ω) (N m : ℕ) : Set Ω :=
  Y m \ ⋃ j ∈ Finset.Ioc m N, Y j

theorem lastPiece_subset (Y : ℕ → Set Ω) (N m : ℕ) : lastPiece Y N m ⊆ Y m :=
  sdiff_subset

/-- The last-time piece at `m` is `G m`-measurable when `G` is antitone and each `Y j` is
`G j`-measurable. -/
theorem measurableSet_lastPiece {G : ℕ → MeasurableSpace Ω} (hG : Antitone G) {Y : ℕ → Set Ω}
    (hY : ∀ m, MeasurableSet[G m] (Y m)) (N m : ℕ) : MeasurableSet[G m] (lastPiece Y N m) := by
  refine (hY m).diff ?_
  refine Finset.measurableSet_biUnion _ fun j hj => ?_
  exact hG (Finset.mem_Ioc.1 hj).1.le _ (hY j)

/-- Last-time pieces of distinct indices are disjoint. -/
theorem pairwiseDisjoint_lastPiece (Y : ℕ → Set Ω) (n N : ℕ) :
    PairwiseDisjoint (↑(Finset.Icc n N) : Set ℕ) (lastPiece Y N) := by
  intro m hm m' hm' hne
  rw [Finset.coe_Icc] at hm hm'
  rw [Function.onFun, Set.disjoint_left]
  intro ω hω hω'
  rcases lt_or_gt_of_ne hne with h | h
  · exact hω.2 (mem_biUnion (Finset.mem_Ioc.2 ⟨h, hm'.2⟩) hω'.1)
  · exact hω'.2 (mem_biUnion (Finset.mem_Ioc.2 ⟨h, hm.2⟩) hω.1)

/-- Every point of `⋃_{m ∈ [n, N]} Y m` lies in the last-time piece of the largest such index. -/
theorem biUnion_lastPiece (Y : ℕ → Set Ω) (n N : ℕ) :
    ⋃ m ∈ Finset.Icc n N, lastPiece Y N m = ⋃ m ∈ Finset.Icc n N, Y m := by
  refine Subset.antisymm (iUnion₂_mono fun m _ => lastPiece_subset Y N m) ?_
  intro ω hω
  simp only [mem_iUnion] at hω
  obtain ⟨m, hm, hωm⟩ := hω
  classical
  let s := (Finset.Icc n N).filter (fun j => ω ∈ Y j)
  have hne : s.Nonempty := ⟨m, Finset.mem_filter.2 ⟨hm, hωm⟩⟩
  have hmax : s.max' hne ∈ Finset.Icc n N ∧ ω ∈ Y (s.max' hne) :=
    Finset.mem_filter.1 (Finset.max'_mem s hne)
  refine mem_biUnion hmax.1 ⟨hmax.2, ?_⟩
  simp only [mem_iUnion, not_exists]
  intro j hj hωj
  have hjI : j ∈ Finset.Icc n N := by
    rw [Finset.mem_Icc] at hmax ⊢
    rw [Finset.mem_Ioc] at hj
    exact ⟨hmax.1.1.trans hj.1.le, hj.2⟩
  have hjs : j ∈ s := Finset.mem_filter.2 ⟨hjI, hωj⟩
  exact absurd (s.le_max' j hjs) (not_le.2 (Finset.mem_Ioc.1 hj).1)

/-- **Last-time decomposition, finite window.** For an antitone sequence of sub-σ-algebras `G`,
`G m`-measurable events `Y m`, and the conditional lower bound `μ A ≤ c * μ (A ∩ T m)` for every
`G m`-measurable `A ⊆ Y m`, the union of the `Y m` over `[n, N]` has measure at most `c` times the
measure of the union of the `T m`. -/
theorem measure_biUnion_Icc_le_mul {G : ℕ → MeasurableSpace Ω} (hG : Antitone G)
    (hle : ∀ m, G m ≤ m0) {Y T : ℕ → Set Ω} (hY : ∀ m, MeasurableSet[G m] (Y m)) {c : ℝ≥0∞}
    (hR : ∀ m (A : Set Ω), MeasurableSet[G m] A → A ⊆ Y m → μ A ≤ c * μ (A ∩ T m))
    (n N : ℕ) :
    μ (⋃ m ∈ Finset.Icc n N, Y m) ≤ c * μ (⋃ m ∈ Finset.Icc n N, T m) := by
  set T' := ⋃ m ∈ Finset.Icc n N, T m with hT'
  have hmeas : ∀ m, MeasurableSet (lastPiece Y N m) := fun m =>
    hle m _ (measurableSet_lastPiece hG hY N m)
  have hdisj := pairwiseDisjoint_lastPiece Y n N
  rw [← biUnion_lastPiece]
  calc μ (⋃ m ∈ Finset.Icc n N, lastPiece Y N m)
      = ∑ m ∈ Finset.Icc n N, μ (lastPiece Y N m) :=
        measure_biUnion_finset hdisj fun m _ => hmeas m
    _ ≤ ∑ m ∈ Finset.Icc n N, c * μ (lastPiece Y N m ∩ T m) :=
        Finset.sum_le_sum fun m _ =>
          hR m _ (measurableSet_lastPiece hG hY N m) (lastPiece_subset Y N m)
    _ ≤ ∑ m ∈ Finset.Icc n N, c * μ.restrict T' (lastPiece Y N m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Measure.restrict_apply (hmeas m)]
        gcongr
        exact subset_biUnion_of_mem (u := T) hm
    _ = c * μ.restrict T' (⋃ m ∈ Finset.Icc n N, lastPiece Y N m) := by
        rw [measure_biUnion_finset hdisj fun m _ => hmeas m, Finset.mul_sum]
    _ ≤ c * μ T' := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc μ.restrict T' (⋃ m ∈ Finset.Icc n N, lastPiece Y N m) ≤ μ.restrict T' univ :=
              measure_mono (subset_univ _)
          _ = μ T' := Measure.restrict_apply_univ T'

/-- **Last-time decomposition, tail union.** Under the hypotheses of
`measure_biUnion_Icc_le_mul`, `μ (⋃_{m ≥ n} Y m) ≤ c * μ (⋃_{m ≥ n} T m)`. -/
theorem measure_biUnion_ge_le_mul {G : ℕ → MeasurableSpace Ω} (hG : Antitone G)
    (hle : ∀ m, G m ≤ m0) {Y T : ℕ → Set Ω} (hY : ∀ m, MeasurableSet[G m] (Y m)) {c : ℝ≥0∞}
    (hR : ∀ m (A : Set Ω), MeasurableSet[G m] A → A ⊆ Y m → μ A ≤ c * μ (A ∩ T m))
    (n : ℕ) :
    μ (⋃ m ≥ n, Y m) ≤ c * μ (⋃ m ≥ n, T m) := by
  have hU : ⋃ m ≥ n, Y m = ⋃ N, ⋃ m ∈ Finset.Icc n N, Y m := by
    ext ω
    constructor
    · intro hω
      obtain ⟨m, hm, hωm⟩ := mem_iUnion₂.1 hω
      exact mem_iUnion.2 ⟨m, mem_iUnion₂.2 ⟨m, Finset.mem_Icc.2 ⟨hm, le_rfl⟩, hωm⟩⟩
    · intro hω
      obtain ⟨N, hN⟩ := mem_iUnion.1 hω
      obtain ⟨m, hm, hωm⟩ := mem_iUnion₂.1 hN
      exact mem_iUnion₂.2 ⟨m, (Finset.mem_Icc.1 hm).1, hωm⟩
  have hmono : Monotone fun N => ⋃ m ∈ Finset.Icc n N, Y m := by
    intro N N' hNN'
    exact biUnion_subset_biUnion_left (by
      intro m hm
      rw [Finset.coe_Icc] at hm ⊢
      exact ⟨hm.1, hm.2.trans hNN'⟩)
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun N => (measure_biUnion_Icc_le_mul hG hle hY hR n N).trans ?_
  refine mul_le_mul_of_nonneg_left (measure_mono fun ω hω => ?_) (by positivity)
  obtain ⟨m, hm, hωm⟩ := mem_iUnion₂.1 hω
  exact mem_iUnion₂.2 ⟨m, (Finset.mem_Icc.1 hm).1, hωm⟩

/-- **Almost surely finitely many `Y m`.** Under the hypotheses of `measure_biUnion_Icc_le_mul`
with `c ≠ ∞`, if `μ (⋃_{m ≥ n} T m) → 0`, then almost surely `Y m` fails for all large `m`. -/
theorem ae_eventually_not_mem {G : ℕ → MeasurableSpace Ω} (hG : Antitone G)
    (hle : ∀ m, G m ≤ m0) {Y T : ℕ → Set Ω} (hY : ∀ m, MeasurableSet[G m] (Y m)) {c : ℝ≥0∞}
    (hc : c ≠ ∞)
    (hR : ∀ m (A : Set Ω), MeasurableSet[G m] A → A ⊆ Y m → μ A ≤ c * μ (A ∩ T m))
    (hT : Tendsto (fun n => μ (⋃ m ≥ n, T m)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, ω ∉ Y m := by
  rw [ae_iff]
  have hsub : ∀ n, {ω | ¬∀ᶠ m in atTop, ω ∉ Y m} ⊆ ⋃ m ≥ n, Y m := by
    intro n ω hω
    have hω' : ¬∀ᶠ m in atTop, ω ∉ Y m := hω
    rw [not_eventually, frequently_atTop] at hω'
    obtain ⟨m, hm, hωm⟩ := hω' n
    exact mem_iUnion₂.2 ⟨m, hm, not_not.1 hωm⟩
  have hlim : Tendsto (fun n => c * μ (⋃ m ≥ n, T m)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hT (Or.inr hc)
  refine nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim fun n => ?_)
  exact (measure_mono (hsub n)).trans (measure_biUnion_ge_le_mul hG hle hY hR n)

/-- **Almost surely finitely many `Y m`, from an almost sure statement on `T`.** For a finite
measure, measurable `T m`, `c ≠ ∞` and the hypotheses of `measure_biUnion_Icc_le_mul`: if almost
surely `T m` fails for all large `m`, then almost surely `Y m` fails for all large `m`. -/
theorem ae_eventually_not_mem_of_ae [IsFiniteMeasure μ] {G : ℕ → MeasurableSpace Ω}
    (hG : Antitone G) (hle : ∀ m, G m ≤ m0) {Y T : ℕ → Set Ω}
    (hY : ∀ m, MeasurableSet[G m] (Y m)) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hR : ∀ m (A : Set Ω), MeasurableSet[G m] A → A ⊆ Y m → μ A ≤ c * μ (A ∩ T m))
    (hTm : ∀ m, MeasurableSet (T m)) (hT : ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, ω ∉ T m) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, ω ∉ Y m := by
  refine ae_eventually_not_mem hG hle hY hc hR ?_
  have hanti : Antitone fun n => ⋃ m ≥ n, T m := by
    intro n n' hnn' ω hω
    obtain ⟨m, hm, hωm⟩ := mem_iUnion₂.1 hω
    exact mem_iUnion₂.2 ⟨m, hnn'.trans hm, hωm⟩
  have hnull : ∀ n, NullMeasurableSet (⋃ m ≥ n, T m) μ := fun n =>
    (MeasurableSet.biUnion (to_countable _) fun m _ => hTm m).nullMeasurableSet
  have h0 : μ (⋂ n, ⋃ m ≥ n, T m) = 0 := by
    rw [ae_iff] at hT
    refine measure_mono_null (fun ω hω => ?_) hT
    rw [mem_iInter] at hω
    show ¬∀ᶠ m in atTop, ω ∉ T m
    rw [not_eventually, frequently_atTop]
    intro n
    obtain ⟨m, hm, hωm⟩ := mem_iUnion₂.1 (hω n)
    exact ⟨m, hm, not_not.2 hωm⟩
  have := tendsto_measure_iInter_atTop hnull hanti ⟨0, measure_ne_top μ _⟩
  rw [h0] at this
  exact this

end LatticeProb.ReverseLastTime
