import Mathlib

/-!
# Segments of large diameter and first-exit traces of a curve

Let `η : ℝ → E` be a curve in a pseudometric space. For a start time `t₀`, a centre `z` and a
radius `ρ`, the *first-exit trace* is `η([t₀, σ])`, where `σ` is the first time after `t₀` at
which `η` leaves the open ball `B(z, ρ)`. This file contains the deterministic step which places
a ball contained in a first-exit trace inside a segment `η([a, b])` of large diameter:

* `diam_image_Icc_le_add`: `diam η([a, b]) ≤ diam η([a, s]) + diam η([s, b])` for `s ∈ [a, b]`;
* `exists_not_mem_ball_of_two_mul_lt_diam`: a set of diameter `> 2ρ` leaves every ball of
  radius `ρ`;
* `exists_ball_subset_image_Icc_of_firstExitTrace`: if `t₀ ∈ [a, b]` and `η` leaves `B(z, ρ)`
  during `[t₀, b]`, a ball in the first-exit trace from `t₀` lies in `η([a, b])`;
* `exists_ball_subset_image_Icc_of_diam`: the same under `diam η([a, t₀]) + 2ρ < diam η([a, b])`;
* `firstDiamTime`: the first time `t* ∈ [a, b]` at which `diam η([a, t*])` reaches a level `c`;
  for continuous `η` and `0 ≤ c ≤ diam η([a, b])`, `diam η([a, t*]) = c`
  (`diam_image_Icc_firstDiamTime_le`, `le_diam_image_Icc_firstDiamTime`), so `η([a, t*])` lies in
  no bounded set of diameter `< c` (`not_image_Icc_firstDiamTime_subset`);
* `exists_ball_subset_image_Icc_of_le_firstDiamTime`: if `c + 2ρ < diam η([a, b])`, a ball in the
  first-exit trace from any start time `t₀ ∈ [a, t*]` lies in `η([a, b])`.
-/

noncomputable section

open Metric Set

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E]

/-- The diameter of a curve segment is at most the sum of the diameters of two consecutive
subsegments. -/
theorem diam_image_Icc_le_add (η : ℝ → E) {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    diam (η '' Icc a b) ≤ diam (η '' Icc a s) + diam (η '' Icc s b) := by
  rw [← Icc_union_Icc_eq_Icc has hsb, image_union]
  have h := diam_union (mem_image_of_mem η (right_mem_Icc.2 has))
    (mem_image_of_mem η (left_mem_Icc.2 hsb))
  simpa only [dist_self, add_zero] using h

/-- A set of diameter larger than `2ρ` is not contained in a ball of radius `ρ`. -/
theorem exists_not_mem_ball_of_two_mul_lt_diam {S : Set E} (z : E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : 2 * ρ < diam S) : ∃ x ∈ S, x ∉ ball z ρ := by
  by_contra hcon
  have hsub : S ⊆ ball z ρ := fun x hx => by
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  have := (diam_mono hsub isBounded_ball).trans (diam_ball hρ)
  linarith

/-- The first exit time after `t₀` from `B(z, ρ)` is at most every exit time after `t₀`. -/
theorem sInf_setOf_exit_le {η : ℝ → E} {t₀ t ρ : ℝ} {z : E} (ht₀ : t₀ ≤ t)
    (ht : η t ∉ ball z ρ) : sInf {s | t₀ ≤ s ∧ η s ∉ ball z ρ} ≤ t :=
  csInf_le ⟨t₀, fun _ hs => hs.1⟩ ⟨ht₀, ht⟩

/-- If the curve leaves `B(z, ρ)` during `[t₀, b]` with `a ≤ t₀`, then a ball contained in the
first-exit trace from `B(z, ρ)` started at `t₀` is contained in the segment `η([a, b])`. -/
theorem exists_ball_subset_image_Icc_of_firstExitTrace (η : ℝ → E) {a b t₀ t ρ r : ℝ} {z : E}
    (ha : a ≤ t₀) (ht₀ : t₀ ≤ t) (htb : t ≤ b) (ht : η t ∉ ball z ρ)
    (hE : ∃ w, ball w r ⊆ η '' Icc t₀ (sInf {s | t₀ ≤ s ∧ η s ∉ ball z ρ})) :
    ∃ w, ball w r ⊆ η '' Icc a b := by
  obtain ⟨w, hw⟩ := hE
  exact ⟨w, hw.trans (image_mono
    (Icc_subset_Icc ha ((sInf_setOf_exit_le ht₀ ht).trans htb)))⟩

/-- If `t₀ ∈ [a, b]` and `diam η([a, t₀]) + 2ρ < diam η([a, b])`, then a ball contained in the
first-exit trace from `B(z, ρ)` started at `t₀` is contained in the segment `η([a, b])`. -/
theorem exists_ball_subset_image_Icc_of_diam (η : ℝ → E) {a b t₀ ρ r : ℝ} {z : E}
    (ha : a ≤ t₀) (hb : t₀ ≤ b) (hρ : 0 ≤ ρ)
    (hdiam : diam (η '' Icc a t₀) + 2 * ρ < diam (η '' Icc a b))
    (hE : ∃ w, ball w r ⊆ η '' Icc t₀ (sInf {s | t₀ ≤ s ∧ η s ∉ ball z ρ})) :
    ∃ w, ball w r ⊆ η '' Icc a b := by
  have h1 := diam_image_Icc_le_add η ha hb
  obtain ⟨x, ⟨t, ht, rfl⟩, hx⟩ :=
    exists_not_mem_ball_of_two_mul_lt_diam (S := η '' Icc t₀ b) z hρ (by linarith)
  exact exists_ball_subset_image_Icc_of_firstExitTrace η ha ht.1 ht.2 hx hE

/-- The first time `t ∈ [a, b]` at which the diameter of the segment `η([a, t])` reaches the
level `c`. -/
def firstDiamTime (η : ℝ → E) (a b c : ℝ) : ℝ :=
  sInf {t | t ∈ Icc a b ∧ c ≤ diam (η '' Icc a t)}

theorem firstDiamTime_mem_Icc (η : ℝ → E) {a b c : ℝ} (hab : a ≤ b)
    (hc : c ≤ diam (η '' Icc a b)) : firstDiamTime η a b c ∈ Icc a b :=
  ⟨le_csInf ⟨b, ⟨hab, le_rfl⟩, hc⟩ (fun _ ht => ht.1.1),
    csInf_le ⟨a, fun _ ht => ht.1.1⟩ ⟨⟨hab, le_rfl⟩, hc⟩⟩

/-- Before the first time `t*` at which `diam η([a, t])` reaches `c`, the diameter is `< c`. -/
theorem diam_image_Icc_lt_of_lt_firstDiamTime (η : ℝ → E) {a b c t : ℝ} (hab : a ≤ b)
    (hc : c ≤ diam (η '' Icc a b)) (hat : a ≤ t) (ht : t < firstDiamTime η a b c) :
    diam (η '' Icc a t) < c := by
  by_contra hle
  have htb : t ≤ b := ht.le.trans (firstDiamTime_mem_Icc η hab hc).2
  have : firstDiamTime η a b c ≤ t :=
    csInf_le ⟨a, fun _ hs => hs.1.1⟩ ⟨⟨hat, htb⟩, not_lt.mp hle⟩
  linarith

/-- For a continuous curve and `0 ≤ c ≤ diam η([a, b])`, the segment `η([a, t*])` up to the first
time `t*` at which the diameter reaches `c` has diameter at most `c`. -/
theorem diam_image_Icc_firstDiamTime_le (η : ℝ → E) (hη : Continuous η) {a b c : ℝ}
    (hab : a ≤ b) (hc0 : 0 ≤ c) (hc : c ≤ diam (η '' Icc a b)) :
    diam (η '' Icc a (firstDiamTime η a b c)) ≤ c := by
  set T := firstDiamTime η a b c with hT
  have haT : a ≤ T := (firstDiamTime_mem_Icc η hab hc).1
  rcases haT.eq_or_lt with h | h
  · rw [← h, Icc_self, image_singleton, diam_singleton]
    exact hc0
  have hbdd : Bornology.IsBounded (η '' Ico a T) :=
    (isCompact_Icc.image hη).isBounded.subset (image_mono Ico_subset_Icc_self)
  have hIco : diam (η '' Ico a T) ≤ c := by
    refine diam_le_of_forall_dist_le hc0 ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hm : max u v < T := max_lt hu.2 hv.2
    have hlt := diam_image_Icc_lt_of_lt_firstDiamTime η hab hc (hu.1.trans (le_max_left u v)) hm
    have hd : dist (η u) (η v) ≤ diam (η '' Icc a (max u v)) :=
      dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded
        (mem_image_of_mem η ⟨hu.1, le_max_left u v⟩) (mem_image_of_mem η ⟨hv.1, le_max_right u v⟩)
    linarith
  have hsub : η '' Icc a T ⊆ closure (η '' Ico a T) := by
    rw [← closure_Ico h.ne]
    exact image_closure_subset_closure_image hη
  calc diam (η '' Icc a T) ≤ diam (closure (η '' Ico a T)) := diam_mono hsub hbdd.closure
    _ = diam (η '' Ico a T) := diam_closure _
    _ ≤ c := hIco

/-- For a continuous curve and `c ≤ diam η([a, b])`, the segment `η([a, t*])` up to the first
time `t*` at which the diameter reaches `c` has diameter at least `c`. -/
theorem le_diam_image_Icc_firstDiamTime (η : ℝ → E) (hη : Continuous η) {a b c : ℝ}
    (hab : a ≤ b) (hc : c ≤ diam (η '' Icc a b)) :
    c ≤ diam (η '' Icc a (firstDiamTime η a b c)) := by
  set T := firstDiamTime η a b c with hT
  have hTmem := firstDiamTime_mem_Icc η hab hc
  by_contra hlt
  rw [not_le] at hlt
  set δ := c - diam (η '' Icc a T) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨h, hh0, hh⟩ := Metric.continuousAt_iff.mp hη.continuousAt (δ / 4) (by positivity)
  have hlower : ∀ t ∈ {t | t ∈ Icc a b ∧ c ≤ diam (η '' Icc a t)}, T + h / 2 ≤ t := by
    rintro t ⟨htI, htc⟩
    have hTt : T ≤ t := csInf_le ⟨a, fun _ hs => hs.1.1⟩ ⟨htI, htc⟩
    by_contra hlt'
    rw [not_le] at hlt'
    have hsmall : diam (η '' Icc T t) ≤ δ / 2 := by
      refine diam_le_of_forall_dist_le (by positivity) ?_
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      have hu' : dist u T < h := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
        linarith [hu.2]
      have hv' : dist v T < h := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hv.1])]
        linarith [hv.2]
      have h1 := hh hu'
      have h2 := hh hv'
      have := dist_triangle_right (η u) (η v) (η T)
      linarith
    have hsplit := diam_image_Icc_le_add η hTmem.1 hTt
    linarith
  have hne : ({t | t ∈ Icc a b ∧ c ≤ diam (η '' Icc a t)} : Set ℝ).Nonempty :=
    ⟨b, ⟨hab, le_rfl⟩, hc⟩
  have : T + h / 2 ≤ T := le_csInf hne hlower
  linarith

/-- The segment `η([a, t*])` up to the first time `t*` at which the diameter reaches `c` lies in
no bounded set of diameter `< c`. -/
theorem not_image_Icc_firstDiamTime_subset (η : ℝ → E) (hη : Continuous η) {a b c : ℝ}
    (hab : a ≤ b) (hc : c ≤ diam (η '' Icc a b)) {P : Set E} (hP : Bornology.IsBounded P)
    (hPc : diam P < c) : ¬ η '' Icc a (firstDiamTime η a b c) ⊆ P := fun hsub =>
  absurd ((le_diam_image_Icc_firstDiamTime η hη hab hc).trans (diam_mono hsub hP))
    (not_le.mpr hPc)

/-- **Ball in a segment of large diameter.** Let `η` be continuous, `0 ≤ c`, `0 ≤ ρ` and
`c + 2ρ < diam η([a, b])`, and let `t*` be the first time at which `diam η([a, t*])` reaches `c`.
For every start time `t₀ ∈ [a, t*]`, a ball contained in the first-exit trace from `B(z, ρ)`
started at `t₀` is contained in the segment `η([a, b])`. -/
theorem exists_ball_subset_image_Icc_of_le_firstDiamTime (η : ℝ → E) (hη : Continuous η)
    {a b c t₀ ρ r : ℝ} {z : E} (hc0 : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hcρ : c + 2 * ρ < diam (η '' Icc a b)) (ha : a ≤ t₀) (ht₀ : t₀ ≤ firstDiamTime η a b c)
    (hE : ∃ w, ball w r ⊆ η '' Icc t₀ (sInf {s | t₀ ≤ s ∧ η s ∉ ball z ρ})) :
    ∃ w, ball w r ⊆ η '' Icc a b := by
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Icc_eq_empty_of_lt hab, image_empty, diam_empty] at hcρ
    linarith
  have hc : c ≤ diam (η '' Icc a b) := by linarith
  have hTmem := firstDiamTime_mem_Icc η hab hc
  have hdiam : diam (η '' Icc a t₀) ≤ c :=
    (diam_mono (image_mono (Icc_subset_Icc le_rfl ht₀))
      (isCompact_Icc.image hη).isBounded).trans
      (diam_image_Icc_firstDiamTime_le η hη hab hc0 hc)
  exact exists_ball_subset_image_Icc_of_diam η ha (ht₀.trans hTmem.2) hρ (by linarith) hE

end LatticeProb
