import LatticeProb.Analysis.ExcursionCountSandwich

/-!
# Time reversal of the excursion count

The backward ladder set of `X` from `a` is the reflection of the forward ladder set of the time-reversed path
`s ↦ X (-s)` from `-a`, and the reflection `x ↦ -x` maps the complementary intervals of `K` in `[s, t]` bijectively
onto those of `-K` in `[-t, -s]`, preserving their lengths.

* `complementaryIntervals_neg`, `excursionCount_neg`: the excursion count is invariant under the reflection;
* `forwardLadderSet_comp_neg`: `forwardLadderSet (fun s => X (-s)) (-a) = -backwardLadderSet X a`;
* `tendsto_excursionCount_backwardLadderSet`: the backward form of the sandwich
  `tendsto_excursionCount_forwardLadderSet`. If `X` is continuous and unbounded below on `(-∞, a]`, and the
  normalized excursion count of the time-reversed path converges at its rational first-passage levels, then for every
  `t ≤ a` the normalized count of excursions of `X` above its running minimum backward from `a`, in `[t, a]`, tends to
  `X a - min_{[t, a]} X`.
-/

open Filter Set Topology
open scoped Pointwise

namespace LatticeProb.LadderSet

variable {X : ℝ → ℝ} {a t : ℝ}

theorem neg_Icc_diff (K : Set ℝ) (s t : ℝ) : Icc (-t) (-s) \ -K = -(Icc s t \ K) := by
  ext x
  simp only [Set.mem_sdiff, mem_Icc, Set.mem_neg]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem neg_connectedComponentIn {S : Set ℝ} {y : ℝ} (hy : y ∈ S) :
    -connectedComponentIn S y = connectedComponentIn (-S) (-y) := by
  have h := (Homeomorph.neg ℝ).image_connectedComponentIn hy
  simpa only [Homeomorph.coe_neg, image_neg_eq_neg] using h

/-- The reflection `x ↦ -x` maps the complementary intervals of `K` in `[s, t]` onto those of `-K` in `[-t, -s]`. -/
theorem complementaryIntervals_neg (K : Set ℝ) (s t : ℝ) :
    complementaryIntervals (-K) (-t) (-s) = (fun C => -C) '' complementaryIntervals K s t := by
  ext C
  simp only [complementaryIntervals, neg_Icc_diff, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨connectedComponentIn (Icc s t \ K) (-x), ⟨-x, Set.mem_neg.1 hx, rfl⟩, ?_⟩
    rw [neg_connectedComponentIn (Set.mem_neg.1 hx), neg_neg]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨-y, Set.neg_mem_neg.2 hy, (neg_connectedComponentIn hy).symm⟩

theorem diam_neg (C : Set ℝ) : Metric.diam (-C) = Metric.diam C := by
  rw [← image_neg_eq_neg]
  exact isometry_neg.diam_image C

/-- The excursion count is invariant under the reflection `x ↦ -x`. -/
theorem excursionCount_neg (K : Set ℝ) (s t ε : ℝ) :
    excursionCount (-K) (-t) (-s) ε = excursionCount K s t ε := by
  unfold excursionCount
  have h : {C ∈ complementaryIntervals (-K) (-t) (-s) | ε < Metric.diam C} =
      (fun C => -C) '' {C ∈ complementaryIntervals K s t | ε < Metric.diam C} := by
    rw [complementaryIntervals_neg]
    ext C
    simp only [Set.mem_sep_iff, mem_image]
    constructor
    · rintro ⟨⟨D, hD, rfl⟩, hε⟩
      exact ⟨D, ⟨hD, by rwa [diam_neg] at hε⟩, rfl⟩
    · rintro ⟨D, ⟨hD, hε⟩, rfl⟩
      exact ⟨⟨D, hD, rfl⟩, by rwa [diam_neg]⟩
  rw [h, Set.ncard_image_of_injective _ neg_injective]

/-- The forward ladder set of the time-reversed path from `-a` is the reflection of the backward ladder set from
`a`. -/
theorem forwardLadderSet_comp_neg (X : ℝ → ℝ) (a : ℝ) :
    forwardLadderSet (fun s => X (-s)) (-a) = -backwardLadderSet X a := by
  ext t
  rw [Set.mem_neg]
  change (-a ≤ t ∧ ∀ s ∈ Icc (-a) t, X (-t) ≤ X (-s)) ↔ (-t ≤ a ∧ ∀ s ∈ Icc (-t) a, X (-t) ≤ X s)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, fun s hs => ?_⟩
    have := h2 (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rwa [neg_neg] at this
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, fun s hs => h2 (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩⟩

theorem image_comp_neg_Icc (X : ℝ → ℝ) (t a : ℝ) :
    (fun s => X (-s)) '' Icc (-a) (-t) = X '' Icc t a := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp only [neg_neg]⟩

/-- **Backward sandwich.** If `X` is continuous and unbounded below on `(-∞, a]`, and the normalized excursion count
of the time-reversed path `s ↦ X (-s)` above its running minimum from `-a` converges to `b` at its first passage below
`X a - b`, for every rational `b > 0`, then for every `t ≤ a` the normalized count of excursions of `X` above its
running minimum backward from `a`, in `[t, a]`, tends to `X a - min_{[t, a]} X`. -/
theorem tendsto_excursionCount_backwardLadderSet (hX : Continuous X)
    (hunb : ∀ b : ℝ, ∃ s, s ≤ a ∧ X s < X a - b)
    (hlev : ∀ b : ℚ, 0 < b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet (fun s => X (-s)) (-a)) (-a)
        (firstPassageBelow (fun s => X (-s)) (-a) b) ε : ℝ)) (𝓝[>] 0) (𝓝 (b : ℝ)))
    (ht : t ≤ a) :
    Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X a) t a ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc t a))) := by
  have hunb' : ∀ b : ℝ, ∃ s, -a ≤ s ∧ X (-s) < X (-(-a)) - b := fun b => by
    obtain ⟨s, hs, hlt⟩ := hunb b
    exact ⟨-s, neg_le_neg hs, by simpa only [neg_neg] using hlt⟩
  have key := tendsto_excursionCount_forwardLadderSet (X := fun s => X (-s)) (a := -a) (t := -t)
    (hX.comp continuous_neg) hunb' hlev (neg_le_neg ht)
  rw [forwardLadderSet_comp_neg, image_comp_neg_Icc] at key
  simpa only [excursionCount_neg, neg_neg] using key

end LatticeProb.LadderSet
