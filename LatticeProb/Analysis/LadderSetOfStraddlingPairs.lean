import LatticeProb.Analysis.StraddlingLevelPairs
import LatticeProb.Analysis.LadderSetReconstruction

/-!
# Ladder sets from straddling level pairs

Let `f : ℝ → ℝ` be continuous and `v` an anchor. The forward ladder set `forwardLadderSet f v` (the times `t ≥ v` at
which `f` attains its running minimum from `v`) is closed and contains the first passage times `firstBelow f v l`
below the levels `l < f v`. Conversely, if `f` takes values below `f v` in every right neighbourhood of `v` and
distinct local minima of `f` have distinct values, then every forward ladder time other than `v` is a limit of first
passage times, so that the forward ladder set is `{v} ∪ closure {firstBelow f v l | l < f v}`
(`forwardLadderSet_eq_insert_closure`). Indeed, a ladder time `t > v` that is not such a limit is a local minimum of
`f` with the same value as the first passage time at its level, which is a local minimum as well. The backward
version uses the last passage times `lastBelow f v l` (`backwardLadderSet_eq_insert_closure`).

Consequently the ladder sets of two continuous functions `X` and `Y` from `v` coincide as soon as their straddling
pairs at `v` coincide. By the no-gap lemma `exists_level_eq_of_dense_straddle_pairs` this is the case when the
straddling pairs of `X` at the levels of a dense set are contour pairs of `Y`
(`ladderSets_eq_of_dense_straddle_pairs`). Together with the reconstruction of the running minimum from the ladder
set by the excursion count (`LadderSet.eq_of_ladderSets_eq_of_dense`), this gives `X = Y`
(`eq_of_dense_straddle_pairs_of_excursionCount`).
-/

set_option autoImplicit false

open Set Filter Topology

namespace LatticeProb

open LatticeProb.LadderSet

section OneFunction

variable {f : ℝ → ℝ} {v : ℝ}

/-- The forward ladder set of a continuous function is closed. -/
theorem isClosed_forwardLadderSet (hf : Continuous f) : IsClosed (forwardLadderSet f v) := by
  refine isClosed_of_closure_subset fun t ht => ?_
  have hsub : forwardLadderSet f v ⊆ Ici v := fun x hx => hx.1
  refine ⟨isClosed_Ici.closure_subset (closure_mono hsub ht), fun s hs => ?_⟩
  rcases hs.2.eq_or_lt with h | hst
  · rw [h]
  · rw [mem_closure_iff_frequently] at ht
    have hev : ∀ᶠ x in 𝓝 t, s < x := Ioi_mem_nhds hst
    have hfreq : ∃ᶠ x in 𝓝 t, f x ∈ Iic (f s) :=
      (ht.and_eventually hev).mono fun x hx => hx.1.2 s ⟨hs.1, hx.2.le⟩
    exact isClosed_Iic.mem_of_frequently_of_tendsto hfreq (hf.tendsto t)

/-- The backward ladder set of a continuous function is closed. -/
theorem isClosed_backwardLadderSet (hf : Continuous f) : IsClosed (backwardLadderSet f v) := by
  refine isClosed_of_closure_subset fun t ht => ?_
  have hsub : backwardLadderSet f v ⊆ Iic v := fun x hx => hx.1
  refine ⟨isClosed_Iic.closure_subset (closure_mono hsub ht), fun s hs => ?_⟩
  rcases hs.1.eq_or_lt with h | hts
  · rw [h]
  · rw [mem_closure_iff_frequently] at ht
    have hev : ∀ᶠ x in 𝓝 t, x < s := Iio_mem_nhds hts
    have hfreq : ∃ᶠ x in 𝓝 t, f x ∈ Iic (f s) :=
      (ht.and_eventually hev).mono fun x hx => hx.1.2 s ⟨hx.2.le, hs.2⟩
    exact isClosed_Iic.mem_of_frequently_of_tendsto hfreq (hf.tendsto t)

/-- The first passage time after `v` below a level `l < f v` is a forward ladder time from `v`. -/
theorem firstBelow_mem_forwardLadderSet (hf : Continuous f) {l : ℝ} (hl : l < f v)
    (hb : ∃ b, v ≤ b ∧ f b ≤ l) : firstBelow f v l ∈ forwardLadderSet f v := by
  refine ⟨(lt_firstBelow hf hl hb).le, fun s hs => ?_⟩
  rcases hs.2.eq_or_lt with h | hst
  · rw [h]
  · rw [apply_firstBelow hf hl hb]
    exact (lt_apply_of_lt_firstBelow hs.1 hst).le

/-- The last passage time before `v` below a level `l < f v` is a backward ladder time from `v`. -/
theorem lastBelow_mem_backwardLadderSet (hf : Continuous f) {l : ℝ} (hl : l < f v)
    (ha : ∃ a ≤ v, f a ≤ l) : lastBelow f v l ∈ backwardLadderSet f v := by
  refine ⟨(lastBelow_lt hf hl ha).le, fun s hs => ?_⟩
  rcases hs.1.eq_or_lt with h | hst
  · rw [h]
  · rw [apply_lastBelow hf hl ha]
    exact (lt_apply_of_lastBelow_lt hst hs.2).le

/-- The forward ladder set from `v` consists of `v` and the closure of the first passage times below the levels
`l < f v`, when `f` is unbounded below after `v`, takes values below `f v` in every right neighbourhood of `v`, and
distinct local minima of `f` have distinct values. -/
theorem forwardLadderSet_eq_insert_closure (hf : Continuous f) (hb : ∀ l, ∃ b, v ≤ b ∧ f b ≤ l)
    (hvR : ∀ u, v < u → ∃ w ∈ Ioo v u, f w < f v)
    (hmin : ∀ p q, p < q → IsLocalMin f p → IsLocalMin f q → f p ≠ f q) :
    forwardLadderSet f v = insert v (closure (firstBelow f v '' Iio (f v))) := by
  apply Subset.antisymm
  · rintro t ⟨hvt, ht⟩
    rcases hvt.eq_or_lt with h | hvt'
    · exact Or.inl h.symm
    right
    have hftv : f t < f v := by
      refine (ht v ⟨le_rfl, hvt⟩).lt_of_ne fun h => ?_
      obtain ⟨w, hw, hfw⟩ := hvR t hvt'
      have := ht w ⟨hw.1.le, hw.2.le⟩
      linarith
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases hw : ∃ w ∈ Ioo t (t + ε), f w < f t
    · obtain ⟨w, hw, hfw⟩ := hw
      obtain ⟨l', hl'w, hl't⟩ := exists_between hfw
      have hbl : ∃ b, v ≤ b ∧ f b ≤ l' := ⟨w, hvt.trans hw.1.le, hl'w.le⟩
      have hl'v : l' < f v := hl't.trans hftv
      refine ⟨firstBelow f v l', ⟨l', hl'v, rfl⟩, ?_⟩
      have h1 : firstBelow f v l' ≤ w := firstBelow_le (hvt.trans hw.1.le) hl'w.le
      have h2 : t ≤ firstBelow f v l' := by
        refine not_lt.1 fun hlt => ?_
        have := ht _ ⟨(lt_firstBelow hf hl'v hbl).le, hlt.le⟩
        rw [apply_firstBelow hf hl'v hbl] at this
        linarith
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hw.2]
    · simp only [not_exists, not_and, not_lt] at hw
      have hbt : ∃ b, v ≤ b ∧ f b ≤ f t := ⟨t, hvt, le_rfl⟩
      set t₁ := firstBelow f v (f t)
      have h1 : t₁ ≤ t := firstBelow_le hvt le_rfl
      have hft₁ : f t₁ = f t := apply_firstBelow hf hftv hbt
      have hvt₁ : v < t₁ := lt_firstBelow hf hftv hbt
      rcases h1.eq_or_lt with h | h
      · exact ⟨t₁, ⟨f t, hftv, rfl⟩, by rw [h, dist_self]; exact hε⟩
      · exfalso
        have hmin₁ : ∀ᶠ x in 𝓝 t₁, f t₁ ≤ f x :=
          Filter.eventually_of_mem (Ioo_mem_nhds hvt₁ h) fun x hx => by
            rw [hft₁]
            exact ht x ⟨hx.1.le, hx.2.le⟩
        have hmin₂ : ∀ᶠ x in 𝓝 t, f t ≤ f x :=
          Filter.eventually_of_mem (Ioo_mem_nhds hvt' (lt_add_of_pos_right t hε)) fun x hx => by
            rcases le_or_gt x t with hxt | hxt
            · exact ht x ⟨hx.1.le, hxt⟩
            · exact hw x ⟨hxt, hx.2⟩
        exact hmin _ _ h hmin₁ hmin₂ hft₁
  · refine insert_subset_iff.2 ⟨⟨le_rfl, fun s hs => ?_⟩,
      (isClosed_forwardLadderSet hf).closure_subset_iff.2 ?_⟩
    · rw [le_antisymm hs.2 hs.1]
    · rintro _ ⟨l, hl, rfl⟩
      exact firstBelow_mem_forwardLadderSet hf hl (hb l)

/-- The backward ladder set from `v` consists of `v` and the closure of the last passage times below the levels
`l < f v`, when `f` is unbounded below before `v`, takes values below `f v` in every left neighbourhood of `v`, and
distinct local minima of `f` have distinct values. -/
theorem backwardLadderSet_eq_insert_closure (hf : Continuous f) (ha : ∀ l, ∃ a ≤ v, f a ≤ l)
    (hvL : ∀ u < v, ∃ w ∈ Ioo u v, f w < f v)
    (hmin : ∀ p q, p < q → IsLocalMin f p → IsLocalMin f q → f p ≠ f q) :
    backwardLadderSet f v = insert v (closure (lastBelow f v '' Iio (f v))) := by
  apply Subset.antisymm
  · rintro t ⟨htv, ht⟩
    rcases htv.eq_or_lt with h | htv'
    · exact Or.inl h
    right
    have hftv : f t < f v := by
      refine (ht v ⟨htv, le_rfl⟩).lt_of_ne fun h => ?_
      obtain ⟨w, hw, hfw⟩ := hvL t htv'
      have := ht w ⟨hw.1.le, hw.2.le⟩
      linarith
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases hw : ∃ w ∈ Ioo (t - ε) t, f w < f t
    · obtain ⟨w, hw, hfw⟩ := hw
      obtain ⟨l', hl'w, hl't⟩ := exists_between hfw
      have hal : ∃ a ≤ v, f a ≤ l' := ⟨w, hw.2.le.trans htv, hl'w.le⟩
      have hl'v : l' < f v := hl't.trans hftv
      refine ⟨lastBelow f v l', ⟨l', hl'v, rfl⟩, ?_⟩
      have h1 : w ≤ lastBelow f v l' := le_lastBelow (hw.2.le.trans htv) hl'w.le
      have h2 : lastBelow f v l' ≤ t := by
        refine not_lt.1 fun hlt => ?_
        have := ht _ ⟨hlt.le, (lastBelow_lt hf hl'v hal).le⟩
        rw [apply_lastBelow hf hl'v hal] at this
        linarith
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hw.1]
    · simp only [not_exists, not_and, not_lt] at hw
      have hat : ∃ a ≤ v, f a ≤ f t := ⟨t, htv, le_rfl⟩
      set t₁ := lastBelow f v (f t)
      have h1 : t ≤ t₁ := le_lastBelow htv le_rfl
      have hft₁ : f t₁ = f t := apply_lastBelow hf hftv hat
      have ht₁v : t₁ < v := lastBelow_lt hf hftv hat
      rcases h1.eq_or_lt with h | h
      · exact ⟨t₁, ⟨f t, hftv, rfl⟩, by rw [← h, dist_self]; exact hε⟩
      · exfalso
        have hmin₁ : ∀ᶠ x in 𝓝 t₁, f t₁ ≤ f x :=
          Filter.eventually_of_mem (Ioo_mem_nhds h ht₁v) fun x hx => by
            rw [hft₁]
            exact ht x ⟨hx.1.le, hx.2.le⟩
        have hmin₂ : ∀ᶠ x in 𝓝 t, f t ≤ f x :=
          Filter.eventually_of_mem (Ioo_mem_nhds (sub_lt_self t hε) htv') fun x hx => by
            rcases le_or_gt t x with htx | htx
            · exact ht x ⟨htx, hx.2.le⟩
            · exact hw x ⟨hx.1, htx⟩
        exact hmin _ _ h hmin₂ hmin₁ hft₁.symm
  · refine insert_subset_iff.2 ⟨⟨le_rfl, fun s hs => ?_⟩,
      (isClosed_backwardLadderSet hf).closure_subset_iff.2 ?_⟩
    · rw [le_antisymm hs.2 hs.1]
    · rintro _ ⟨l, hl, rfl⟩
      exact lastBelow_mem_backwardLadderSet hf hl (ha l)

end OneFunction

section TwoFunctions

variable {X Y : ℝ → ℝ} {v : ℝ}

/-- If the straddling pairs of `X` at `v` at the levels of a dense set are contour pairs of `Y`, then `X` and `Y` have
the same straddling pairs at `v`: every straddling pair of `X` is a straddling pair of `Y`, and conversely. -/
theorem straddle_pairs_eq_of_dense (hX : Continuous X) (hY : Continuous Y)
    (hXlow : ∀ l, (∃ a ≤ v, X a ≤ l) ∧ ∃ b, v ≤ b ∧ X b ≤ l) (hYlow : ∀ m, ∃ u, Y u ≤ m)
    (hvL : ∀ u < v, ∃ w ∈ Ioo u v, X w < X v)
    (hmin : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q) {D : Set ℝ} (hD : Dense D)
    (hpairD : ∀ d ∈ D, d < X v → Y (lastBelow X v d) = Y (firstBelow X v d) ∧
      ∀ u ∈ Ioo (lastBelow X v d) (firstBelow X v d), Y (lastBelow X v d) < Y u) :
    (∀ l < X v, ∃ m < Y v, lastBelow X v l = lastBelow Y v m ∧ firstBelow X v l = firstBelow Y v m) ∧
      ∀ m < Y v, ∃ l < X v, lastBelow X v l = lastBelow Y v m ∧ firstBelow X v l = firstBelow Y v m := by
  refine ⟨fun l hl => ?_, fun m hm =>
    exists_level_eq_of_dense_straddle_pairs hX hY hXlow hvL hmin hD hpairD hm (hYlow m)⟩
  obtain ⟨hYeq, hYin⟩ := straddle_pairs_of_dense hX hY hXlow hD hpairD hl
  have hs := lastBelow_lt hX hl (hXlow l).1
  have ht := lt_firstBelow hX hl (hXlow l).2
  obtain ⟨h1, h2⟩ := lastBelow_eq_and_firstBelow_eq (f := Y) hs ht hYeq hYin
  exact ⟨_, hYin v ⟨hs, ht⟩, h1.symm, h2.symm⟩

/-- Equal ladder sets from equal straddling pairs. Let `X` and `Y` be continuous, unbounded below on both sides of
`v`, with values below their value at `v` in every one-sided neighbourhood of `v`, and with distinct values at
distinct local minima. If the straddling pairs of `X` at `v` at the levels of a dense set are contour pairs of `Y`,
then the forward and the backward ladder sets of `X` and `Y` from `v` coincide. -/
theorem ladderSets_eq_of_dense_straddle_pairs (hX : Continuous X) (hY : Continuous Y)
    (hXlow : ∀ l, (∃ a ≤ v, X a ≤ l) ∧ ∃ b, v ≤ b ∧ X b ≤ l)
    (hYlow : ∀ m, (∃ a ≤ v, Y a ≤ m) ∧ ∃ b, v ≤ b ∧ Y b ≤ m)
    (hXL : ∀ u < v, ∃ w ∈ Ioo u v, X w < X v) (hXR : ∀ u, v < u → ∃ w ∈ Ioo v u, X w < X v)
    (hYL : ∀ u < v, ∃ w ∈ Ioo u v, Y w < Y v) (hYR : ∀ u, v < u → ∃ w ∈ Ioo v u, Y w < Y v)
    (hXmin : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q)
    (hYmin : ∀ p q, p < q → IsLocalMin Y p → IsLocalMin Y q → Y p ≠ Y q) {D : Set ℝ} (hD : Dense D)
    (hpairD : ∀ d ∈ D, d < X v → Y (lastBelow X v d) = Y (firstBelow X v d) ∧
      ∀ u ∈ Ioo (lastBelow X v d) (firstBelow X v d), Y (lastBelow X v d) < Y u) :
    forwardLadderSet X v = forwardLadderSet Y v ∧ backwardLadderSet X v = backwardLadderSet Y v := by
  obtain ⟨hXY, hYX⟩ := straddle_pairs_eq_of_dense hX hY hXlow
    (fun m => (hYlow m).1.imp fun _ ha => ha.2) hXL hXmin hD hpairD
  have himT : firstBelow X v '' Iio (X v) = firstBelow Y v '' Iio (Y v) := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨m, hm, -, h⟩ := hXY l hl
      exact ⟨m, hm, h.symm⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨l, hl, -, h⟩ := hYX m hm
      exact ⟨l, hl, h⟩
  have himS : lastBelow X v '' Iio (X v) = lastBelow Y v '' Iio (Y v) := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨m, hm, h, -⟩ := hXY l hl
      exact ⟨m, hm, h.symm⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨l, hl, h, -⟩ := hYX m hm
      exact ⟨l, hl, h⟩
  constructor
  · rw [forwardLadderSet_eq_insert_closure hX (fun l => (hXlow l).2) hXR hXmin,
      forwardLadderSet_eq_insert_closure hY (fun m => (hYlow m).2) hYR hYmin, himT]
  · rw [backwardLadderSet_eq_insert_closure hX (fun l => (hXlow l).1) hXL hXmin,
      backwardLadderSet_eq_insert_closure hY (fun m => (hYlow m).1) hYL hYmin, himS]

/-- Reconstruction of a path from straddling pairs at a dense set of anchors. Let `X` and `Y` be continuous, with
distinct values at distinct local minima. Suppose that at every anchor `a` of a dense set `A`: both are unbounded
below on both sides of `a` and take values below their value at `a` in every one-sided neighbourhood of `a`; the
straddling pairs of `X` at `a` at the levels of a dense set `D a` are contour pairs of `Y`; and, for `X` and for
`Y` and in both directions, the drop of the running minimum from `a` is the limit of `√(π ε / 2) N_ε`, where `N_ε`
counts the complementary intervals longer than `ε` of the ladder set from `a`. If `X t₀ = Y t₀` for some `t₀`, then
`X = Y`. -/
theorem eq_of_dense_straddle_pairs_of_excursionCount (hX : Continuous X) (hY : Continuous Y)
    {A : Set ℝ} (hA : Dense A)
    (hXlow : ∀ a ∈ A, ∀ l, (∃ s ≤ a, X s ≤ l) ∧ ∃ t, a ≤ t ∧ X t ≤ l)
    (hYlow : ∀ a ∈ A, ∀ m, (∃ s ≤ a, Y s ≤ m) ∧ ∃ t, a ≤ t ∧ Y t ≤ m)
    (hXL : ∀ a ∈ A, ∀ u < a, ∃ w ∈ Ioo u a, X w < X a)
    (hXR : ∀ a ∈ A, ∀ u, a < u → ∃ w ∈ Ioo a u, X w < X a)
    (hYL : ∀ a ∈ A, ∀ u < a, ∃ w ∈ Ioo u a, Y w < Y a)
    (hYR : ∀ a ∈ A, ∀ u, a < u → ∃ w ∈ Ioo a u, Y w < Y a)
    (hXmin : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q)
    (hYmin : ∀ p q, p < q → IsLocalMin Y p → IsLocalMin Y q → Y p ≠ Y q)
    {D : ℝ → Set ℝ} (hD : ∀ a ∈ A, Dense (D a))
    (hpair : ∀ a ∈ A, ∀ d ∈ D a, d < X a → Y (lastBelow X a d) = Y (firstBelow X a d) ∧
      ∀ u ∈ Ioo (lastBelow X a d) (firstBelow X a d), Y (lastBelow X a d) < Y u)
    (hXf : ∀ a ∈ A, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t))))
    (hYf : ∀ a ∈ A, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet Y a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (Y a - sInf (Y '' Icc a t))))
    (hXb : ∀ b ∈ A, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (X b - sInf (X '' Icc t b))))
    (hYb : ∀ b ∈ A, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet Y b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (Y b - sInf (Y '' Icc t b))))
    {t₀ : ℝ} (h0 : X t₀ = Y t₀) :
    X = Y := by
  have hK : ∀ a ∈ A, forwardLadderSet X a = forwardLadderSet Y a ∧
      backwardLadderSet X a = backwardLadderSet Y a := fun a ha =>
    ladderSets_eq_of_dense_straddle_pairs hX hY (hXlow a ha) (hYlow a ha) (hXL a ha) (hXR a ha)
      (hYL a ha) (hYR a ha) hXmin hYmin (hD a ha) (hpair a ha)
  exact eq_of_ladderSets_eq_of_dense hX hY hA hXf hYf hXb hYb (fun a ha => (hK a ha).1)
    (fun b hb => (hK b hb).2) h0

end TwoFunctions

end LatticeProb
