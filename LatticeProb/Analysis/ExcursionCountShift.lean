import LatticeProb.Analysis.ExcursionCountRestart

/-!
# Translation of the excursion count and the count of a restarted path

Let `X : ℝ → ℝ` be continuous, `a, b ≥ 0`, and let `T` be the first passage of `X` below `X 0 - a`. If `Y` is the
path restarted at `T`, that is `Y u = X (T + u) + c` for every `u ≥ 0` (the values of `Y` at negative times play no
role), then the excursions of `X` above its running minimum that are completed between `T` and the first passage
below `X 0 - (a + b)` are the excursions of `Y` above its running minimum before its first passage below
`Y 0 - b`, translated by `T`. This file proves the corresponding identities:

* `excursionCount_add_image`: the excursion count is invariant under the translation `x ↦ T + x`;
* `excursionCount_congr_of_inter_Ici`: the excursion count in `[s, t]` only depends on `K ∩ [s, ∞)`;
* `forwardLadderSet_shift`, `firstPassageBelow_shift`: the ladder set and the first passage of the restarted path
  are those of `X` after `T`, translated by `-T`;
* `excursionCount_shift`: the excursion count of the restarted path is the excursion count of `X` from `T`;
* `excursionCount_firstPassageBelow_add_restart`: the count up to the first passage below `X 0 - (a + b)` is the
  count up to the first passage below `X 0 - a` plus the count of the restarted path up to its first passage below
  `Y 0 - b`.
-/

open Set Topology

namespace LatticeProb.LadderSet

variable {X Y : ℝ → ℝ} {a b c s T : ℝ}

theorem add_Icc_diff (T : ℝ) (K : Set ℝ) (s t : ℝ) :
    Icc (T + s) (T + t) \ (T + ·) '' K = (T + ·) '' (Icc s t \ K) := by
  ext x
  obtain ⟨y, rfl⟩ : ∃ y, x = T + y := ⟨x - T, by ring⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hyK⟩
    exact ⟨y, ⟨⟨by linarith, by linarith⟩, fun hK => hyK ⟨y, hK, rfl⟩⟩, rfl⟩
  · rintro ⟨z, ⟨⟨h1, h2⟩, hzK⟩, hzy⟩
    obtain rfl : z = y := add_left_cancel hzy
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact hzK ((add_left_cancel hwz) ▸ hw)

theorem add_connectedComponentIn (T : ℝ) {S : Set ℝ} {y : ℝ} (hy : y ∈ S) :
    (T + ·) '' connectedComponentIn S y = connectedComponentIn ((T + ·) '' S) (T + y) :=
  (Homeomorph.addLeft T).image_connectedComponentIn hy

/-- The translation `x ↦ T + x` maps the complementary intervals of `K` in `[s, t]` onto those of `T + K` in
`[T + s, T + t]`. -/
theorem complementaryIntervals_add (T : ℝ) (K : Set ℝ) (s t : ℝ) :
    complementaryIntervals ((T + ·) '' K) (T + s) (T + t) =
      (fun C => (T + ·) '' C) '' complementaryIntervals K s t := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [add_Icc_diff] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨connectedComponentIn (Icc s t \ K) y, ⟨y, hy, rfl⟩, add_connectedComponentIn T hy⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨T + y, ?_, ?_⟩
    · rw [add_Icc_diff]
      exact ⟨y, hy, rfl⟩
    · rw [add_Icc_diff]
      exact (add_connectedComponentIn T hy).symm

theorem diam_add_image (T : ℝ) (C : Set ℝ) : Metric.diam ((T + ·) '' C) = Metric.diam C :=
  (Isometry.of_dist_eq fun x y => dist_add_left T x y).diam_image C

/-- **Translation invariance of the excursion count.** The number of complementary intervals of `T + K` in
`[T + s, T + t]` of length `> ε` is the number of complementary intervals of `K` in `[s, t]` of length `> ε`. -/
theorem excursionCount_add_image (T : ℝ) (K : Set ℝ) (s t ε : ℝ) :
    excursionCount ((T + ·) '' K) (T + s) (T + t) ε = excursionCount K s t ε := by
  unfold excursionCount
  have h : {C ∈ complementaryIntervals ((T + ·) '' K) (T + s) (T + t) | ε < Metric.diam C} =
      (fun C => (T + ·) '' C) '' {C ∈ complementaryIntervals K s t | ε < Metric.diam C} := by
    rw [complementaryIntervals_add]
    ext C
    constructor
    · rintro ⟨⟨D, hD, rfl⟩, hε⟩
      rw [diam_add_image] at hε
      exact ⟨D, ⟨hD, hε⟩, rfl⟩
    · rintro ⟨D, ⟨hD, hε⟩, rfl⟩
      exact ⟨⟨D, hD, rfl⟩, by rwa [diam_add_image]⟩
  rw [h, Set.ncard_image_of_injective _ (Set.image_injective.2 (add_right_injective T))]

/-- The excursion count of `K` in `[s, t]` only depends on `K ∩ [s, ∞)`. -/
theorem excursionCount_congr_of_inter_Ici {K K' : Set ℝ} (h : K ∩ Ici s = K' ∩ Ici s) (t ε : ℝ) :
    excursionCount K s t ε = excursionCount K' s t ε := by
  have hd : Icc s t \ K = Icc s t \ K' := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      refine ⟨hx, fun hxK' => hxK ?_⟩
      have hx' : x ∈ K' ∩ Ici s := ⟨hxK', hx.1⟩
      rw [← h] at hx'
      exact hx'.1
    · rintro ⟨hx, hxK'⟩
      refine ⟨hx, fun hxK => hxK' ?_⟩
      have hx' : x ∈ K ∩ Ici s := ⟨hxK, hx.1⟩
      rw [h] at hx'
      exact hx'.1
  unfold excursionCount complementaryIntervals
  rw [hd]

theorem mem_forwardLadderSet_shift (hY : ∀ u, 0 ≤ u → Y u = X (T + u) + c) (y : ℝ) :
    y ∈ forwardLadderSet Y 0 ↔ T + y ∈ forwardLadderSet X T := by
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨by linarith, fun s hs => ?_⟩
    have hs0 : 0 ≤ s - T := by linarith [hs.1]
    have hle := h (s - T) ⟨hs0, by linarith [hs.2]⟩
    rw [hY y hy, hY (s - T) hs0, show T + (s - T) = s by ring] at hle
    linarith
  · rintro ⟨hy, h⟩
    have hy0 : 0 ≤ y := by linarith
    refine ⟨hy0, fun s hs => ?_⟩
    have hle := h (T + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [hY y hy0, hY s hs.1]
    linarith

/-- **Ladder set of the restarted path.** If `Y u = X (T + u) + c` for `u ≥ 0`, the forward ladder set of `X` from
`T` is the forward ladder set of `Y` from `0` translated by `T`. -/
theorem forwardLadderSet_shift (hY : ∀ u, 0 ≤ u → Y u = X (T + u) + c) :
    (T + ·) '' forwardLadderSet Y 0 = forwardLadderSet X T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_forwardLadderSet_shift hY y).1 hy
  · intro hx
    refine ⟨x - T, (mem_forwardLadderSet_shift hY _).2 ?_, show T + (x - T) = x by ring⟩
    rwa [show T + (x - T) = x by ring]

/-- **First passage of the restarted path.** If `Y u = X (T + u) + c` for `u ≥ 0` and `X` goes below `X T - b`
after `T`, the first passage of `Y` below `Y 0 - b` is the first passage of `X` below `X T - b` after `T`, minus
`T`. -/
theorem firstPassageBelow_shift (hY : ∀ u, 0 ≤ u → Y u = X (T + u) + c)
    (hne : ∃ s, T ≤ s ∧ X s < X T - b) : firstPassageBelow Y 0 b = firstPassageBelow X T b - T := by
  have hY0 : Y 0 = X T + c := by rw [hY 0 le_rfl, add_zero]
  have hmem : ∀ y, (0 ≤ y ∧ Y y < Y 0 - b) ↔ (T ≤ T + y ∧ X (T + y) < X T - b) := by
    intro y
    constructor
    · rintro ⟨hy, h⟩
      rw [hY y hy, hY0] at h
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hy, h⟩
      have hy0 : 0 ≤ y := by linarith
      rw [hY y hy0, hY0]
      exact ⟨hy0, by linarith⟩
  obtain ⟨s, hTs, hs⟩ := hne
  unfold firstPassageBelow
  apply le_antisymm
  · rw [le_sub_iff_add_le]
    refine le_csInf ⟨s, hTs, hs⟩ fun t ht => ?_
    have hmt : t - T ∈ {y | 0 ≤ y ∧ Y y < Y 0 - b} :=
      (hmem (t - T)).2 (by rw [show T + (t - T) = t by ring]; exact ht)
    have hle := csInf_le (s := {y | 0 ≤ y ∧ Y y < Y 0 - b}) ⟨0, fun _ hr => hr.1⟩ hmt
    linarith
  · refine le_csInf ⟨s - T, (hmem _).2 ?_⟩ fun y hy => ?_
    · rw [show T + (s - T) = s by ring]
      exact ⟨hTs, hs⟩
    · have hle := csInf_le (s := {t | T ≤ t ∧ X t < X T - b}) ⟨T, fun _ hr => hr.1⟩ ((hmem y).1 hy)
      linarith

/-- **Excursion count of the restarted path.** If `Y u = X (T + u) + c` for `u ≥ 0` and `X` goes below `X T - b`
after `T`, the excursion count of `Y` from `0` up to its first passage below `Y 0 - b` is the excursion count of `X`
from `T` up to its first passage below `X T - b`. -/
theorem excursionCount_shift (hY : ∀ u, 0 ≤ u → Y u = X (T + u) + c)
    (hne : ∃ s, T ≤ s ∧ X s < X T - b) (ε : ℝ) :
    excursionCount (forwardLadderSet Y 0) 0 (firstPassageBelow Y 0 b) ε =
      excursionCount (forwardLadderSet X T) T (firstPassageBelow X T b) ε := by
  rw [← excursionCount_add_image T, forwardLadderSet_shift hY, firstPassageBelow_shift hY hne,
    show T + 0 = T by ring, show T + (firstPassageBelow X T b - T) = firstPassageBelow X T b by ring]

/-- **Additivity of the excursion count along the restarted path.** Let `X` be continuous, `a, b ≥ 0`, `ε > 0`,
assume that `X` goes below `X 0 - (a + b)` after `0`, let `T` be the first passage of `X` below `X 0 - a`, and let
`Y u = X (T + u) + c` for `u ≥ 0`. Then the number of excursions of `X` above its running minimum of length `> ε`
before the first passage below `X 0 - (a + b)` is the number before the first passage below `X 0 - a` plus the
number of excursions of `Y` of length `> ε` before its first passage below `Y 0 - b`. -/
theorem excursionCount_firstPassageBelow_add_restart (hX : Continuous X) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {ε : ℝ} (hε : 0 < ε) (hne : ∃ s, 0 ≤ s ∧ X s < X 0 - (a + b))
    (hY : ∀ u, 0 ≤ u → Y u = X (firstPassageBelow X 0 a + u) + c) :
    excursionCount (forwardLadderSet X 0) 0 (firstPassageBelow X 0 (a + b)) ε =
      excursionCount (forwardLadderSet X 0) 0 (firstPassageBelow X 0 a) ε +
        excursionCount (forwardLadderSet Y 0) 0 (firstPassageBelow Y 0 b) ε := by
  obtain ⟨s, hs0, hs⟩ := hne
  have hnea : ∃ s, 0 ≤ s ∧ X s < X 0 - a := ⟨s, hs0, by linarith⟩
  set T := firstPassageBelow X 0 a with hTdef
  have hTK : T ∈ forwardLadderSet X 0 := firstPassageBelow_mem_forwardLadderSet hX hnea
  have hXT : X T = X 0 - a := apply_firstPassageBelow_eq hX hnea ha
  have hTs : T ≤ s := csInf_le (s := {t | 0 ≤ t ∧ X t < X 0 - a}) ⟨0, fun _ hr => hr.1⟩ ⟨hs0, by linarith⟩
  have hneT : ∃ s, T ≤ s ∧ X s < X T - b := ⟨s, hTs, by linarith⟩
  have hTv : T ≤ firstPassageBelow X T b := le_firstPassageBelow_self hneT
  rw [firstPassageBelow_add hX hnea ha hb, ← hTdef, excursionCount_add hTK hTK.1 hTv hε,
    excursionCount_shift hY hneT ε]
  congr 1
  refine excursionCount_congr_of_inter_Ici ?_ _ ε
  rw [forwardLadderSet_inter_Ici hTK]
  exact (inter_eq_left.2 fun t ht => ht.1).symm

end LatticeProb.LadderSet
