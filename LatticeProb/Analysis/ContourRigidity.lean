import LatticeProb.Analysis.ContourChainColour
import LatticeProb.Analysis.LadderSetOfStraddlingPairs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Rigidity of contour chains

A continuous function `X : ℝ → ℝ` is *ladder regular* on a set of anchors `Q` (`IsLadderRegularOn X Q`) if it is
unbounded below on both sides of every time, distinct local minima of `X` have distinct values, at every anchor of
`Q` it takes values below its value at the anchor in every one-sided neighbourhood of the anchor, and at every anchor
of `Q`, in both directions, the drop of its running minimum is the limit of `√(π ε / 2) N_ε`, where `N_ε` counts the
complementary intervals longer than `ε` of the ladder set from the anchor. These are almost sure properties of a
two-sided Brownian motion for a countable set of anchors; here they enter as hypotheses.

Let `X`, `Y₁`, `Y₂` be ladder regular on a dense set `Q`, and suppose that `Y₁` and `Y₂` have no common weak contour
pair. If, at every anchor of `Q` and at the levels of dense sets given by a property `P` of the straddling pairs, the
straddling pairs of `X` are contour pairs of `Y₁` or of `Y₂`, and the three functions agree at one time, then
`X = Y₁` or `X = Y₂` (`IsLadderRegularOn.eq_or_eq_of_contour_pairs`). Indeed the colour of the chains does not depend
on the anchor (`contour_chain_global_colour`), and a path is determined by its ladder sets
(`eq_of_dense_straddle_pairs_of_excursionCount`). For two pairs of functions `(L, R)` and `(L', R')` with `L ≠ R`,
applying this to `X = L` and to `X = R` gives `(L', R') = (L, R)` or `(L', R') = (R, L)`
(`eq_or_swap_of_contour_pairs`).

The dense sets of levels arise from an exceptional set of times `Z` whose images under `L` and `R` are Lebesgue-null:
at every level outside `L '' Z`, the straddling pair of `L` either is degenerate (the level is not below the value at
the anchor) or has its left endpoint outside `Z` (`dense_setOf_straddle_of_volume_image_eq_zero`). This gives the form
`eq_or_swap_of_contour_pairs_of_volume_image`, in which the straddling pairs are only required to be contour pairs of
`L'` or `R'` when their left endpoint avoids `Z`.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory

namespace LatticeProb

open LatticeProb.LadderSet

/-- A continuous function is *ladder regular* on a set `Q` of anchors: it is unbounded below on both sides of every
time, its distinct local minima have distinct values, it takes values below its value at each anchor of `Q` in every
one-sided neighbourhood of the anchor, and, at each anchor of `Q` and in both directions, the drop of its running
minimum is the limit of `√(π ε / 2) N_ε` for the ladder set from the anchor. -/
structure IsLadderRegularOn (X : ℝ → ℝ) (Q : Set ℝ) : Prop where
  continuous : Continuous X
  low : ∀ w l, (∃ a ≤ w, X a ≤ l) ∧ ∃ b, w ≤ b ∧ X b ≤ l
  locMin_ne : ∀ p q, p < q → IsLocalMin X p → IsLocalMin X q → X p ≠ X q
  descent_left : ∀ a ∈ Q, ∀ u < a, ∃ w ∈ Ioo u a, X w < X a
  descent_right : ∀ a ∈ Q, ∀ u, a < u → ∃ w ∈ Ioo a u, X w < X a
  excursion_forward : ∀ a ∈ Q, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
    (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t)))
  excursion_backward : ∀ b ∈ Q, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
    (excursionCount (backwardLadderSet X b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (X b - sInf (X '' Icc t b)))

/-- Two ladder regular functions agree as soon as they agree at one time and, at every anchor of a dense set and at
the levels of dense sets given by a property `P` of the straddling pairs, the straddling pairs of the first are contour
pairs of the second. -/
theorem IsLadderRegularOn.eq_of_contour_pairs {X Y : ℝ → ℝ} {Q : Set ℝ} (hX : IsLadderRegularOn X Q)
    (hY : IsLadderRegularOn Y Q) (hQ : Dense Q) {P : ℝ → ℝ → Prop}
    (hD : ∀ w ∈ Q, Dense {l | P (lastBelow X w l) (firstBelow X w l)})
    (hpair : ∀ w ∈ Q, ∀ l, P (lastBelow X w l) (firstBelow X w l) → l < X w →
      IsContourPair Y (lastBelow X w l) (firstBelow X w l))
    {t₀ : ℝ} (h0 : X t₀ = Y t₀) : X = Y :=
  eq_of_dense_straddle_pairs_of_excursionCount hX.continuous hY.continuous hQ (fun a _ => hX.low a)
    (fun a _ => hY.low a) hX.descent_left hX.descent_right hY.descent_left hY.descent_right hX.locMin_ne
    hY.locMin_ne (D := fun w => {l | P (lastBelow X w l) (firstBelow X w l)}) hD
    (fun a ha d hd hda => (hpair a ha d hd hda).2) hX.excursion_forward hY.excursion_forward
    hX.excursion_backward hY.excursion_backward h0

/-- **Contour chain rigidity for one function.** Let `X`, `Y₁`, `Y₂` be ladder regular on a dense set `Q`, where `Y₁`
and `Y₂` have no common weak contour pair. If, at every anchor of `Q` and at the levels of dense sets given by a
property `P` of the straddling pairs, the straddling pairs of `X` are contour pairs of `Y₁` or of `Y₂`, and the three
functions agree at one time, then `X = Y₁` or `X = Y₂`. -/
theorem IsLadderRegularOn.eq_or_eq_of_contour_pairs {X Y₁ Y₂ : ℝ → ℝ} {Q : Set ℝ}
    (hX : IsLadderRegularOn X Q) (hY₁ : IsLadderRegularOn Y₁ Q) (hY₂ : IsLadderRegularOn Y₂ Q)
    (hQ : Dense Q) (hNC : ∀ s t, IsWeakContourPair Y₁ s t → IsWeakContourPair Y₂ s t → False)
    {P : ℝ → ℝ → Prop} (hD : ∀ w ∈ Q, Dense {l | P (lastBelow X w l) (firstBelow X w l)})
    (hcol : ∀ w ∈ Q, ∀ l, P (lastBelow X w l) (firstBelow X w l) → l < X w →
      IsContourPair Y₁ (lastBelow X w l) (firstBelow X w l) ∨
        IsContourPair Y₂ (lastBelow X w l) (firstBelow X w l))
    {t₀ : ℝ} (h₁ : X t₀ = Y₁ t₀) (h₂ : X t₀ = Y₂ t₀) : X = Y₁ ∨ X = Y₂ := by
  rcases contour_chain_global_colour hX.continuous hY₁.continuous hY₂.continuous hX.low hX.locMin_ne hNC hQ
    hD hcol with h | h
  · exact Or.inl (hX.eq_of_contour_pairs hY₁ hQ hD h h₁)
  · exact Or.inr (hX.eq_of_contour_pairs hY₂ hQ hD h h₂)

/-- **Contour chain rigidity for pairs: equality or swap.** Let `L`, `R`, `L'`, `R'` be ladder regular on a dense set
`Q`, where `L ≠ R` and `L'`, `R'` have no common weak contour pair, and let the four functions agree at one time.
If, at every anchor of `Q` and at the levels of dense sets given by a property `P` of the straddling pairs, the
straddling pairs of `L` and those of `R` are contour pairs of `L'` or of `R'`, then `(L', R') = (L, R)` or
`(L', R') = (R, L)`. -/
theorem eq_or_swap_of_contour_pairs {L R L' R' : ℝ → ℝ} {Q : Set ℝ} (hL : IsLadderRegularOn L Q)
    (hR : IsLadderRegularOn R Q) (hL' : IsLadderRegularOn L' Q) (hR' : IsLadderRegularOn R' Q) (hQ : Dense Q)
    (hNC : ∀ s t, IsWeakContourPair L' s t → IsWeakContourPair R' s t → False) {P : ℝ → ℝ → Prop}
    (hDL : ∀ w ∈ Q, Dense {l | P (lastBelow L w l) (firstBelow L w l)})
    (hDR : ∀ w ∈ Q, Dense {l | P (lastBelow R w l) (firstBelow R w l)})
    (hcolL : ∀ w ∈ Q, ∀ l, P (lastBelow L w l) (firstBelow L w l) → l < L w →
      IsContourPair L' (lastBelow L w l) (firstBelow L w l) ∨
        IsContourPair R' (lastBelow L w l) (firstBelow L w l))
    (hcolR : ∀ w ∈ Q, ∀ l, P (lastBelow R w l) (firstBelow R w l) → l < R w →
      IsContourPair L' (lastBelow R w l) (firstBelow R w l) ∨
        IsContourPair R' (lastBelow R w l) (firstBelow R w l))
    {t₀ c : ℝ} (hL0 : L t₀ = c) (hR0 : R t₀ = c) (hL'0 : L' t₀ = c) (hR'0 : R' t₀ = c) (hLR : L ≠ R) :
    (L' = L ∧ R' = R) ∨ (L' = R ∧ R' = L) := by
  have eL := hL.eq_or_eq_of_contour_pairs hL' hR' hQ hNC hDL hcolL (hL0.trans hL'0.symm)
    (hL0.trans hR'0.symm)
  have eR := hR.eq_or_eq_of_contour_pairs hL' hR' hQ hNC hDR hcolR (hR0.trans hL'0.symm)
    (hR0.trans hR'0.symm)
  rcases eL with h₁ | h₁ <;> rcases eR with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hLR
  · exact Or.inl ⟨h₁.symm, h₂.symm⟩
  · exact Or.inr ⟨h₂.symm, h₁.symm⟩
  · exact absurd (h₁.trans h₂.symm) hLR

/-- At a level `l` not below `f v`, both straddling times of `v` at level `l` are `v`. -/
theorem lastBelow_eq_and_firstBelow_eq_of_le {f : ℝ → ℝ} {v l : ℝ} (hl : f v ≤ l) :
    lastBelow f v l = v ∧ firstBelow f v l = v :=
  ⟨IsGreatest.csSup_eq ⟨⟨le_rfl, hl⟩, fun _ hu => hu.1⟩, IsLeast.csInf_eq ⟨⟨le_rfl, hl⟩, fun _ hu => hu.1⟩⟩

/-- **Straddling pairs avoiding a null set of levels.** Let `X` be continuous and unbounded below on the left of `v`,
and let `Z` be a set of times whose image `X '' Z` is Lebesgue-null. If a property `P` of pairs of times holds for
every pair whose left time is outside `Z` and for every degenerate pair, then the levels `l` at which `P` holds for
the straddling pair of `v` at level `l` are dense. -/
theorem dense_setOf_straddle_of_volume_image_eq_zero {X : ℝ → ℝ} (hX : Continuous X) {v : ℝ}
    (hlow : ∀ l, ∃ a ≤ v, X a ≤ l) {Z : Set ℝ} (hZ : volume (X '' Z) = 0) {P : ℝ → ℝ → Prop}
    (hPZ : ∀ s t, s ∉ Z → P s t) (hPd : ∀ s, P s s) :
    Dense {l | P (lastBelow X v l) (firstBelow X v l)} := by
  have hd : Dense (X '' Z)ᶜ :=
    interior_eq_empty_iff_dense_compl.1 (Measure.interior_eq_empty_of_null hZ)
  refine hd.mono fun l hl => ?_
  rcases lt_or_ge l (X v) with h | h
  · exact hPZ _ _ fun hs => hl ⟨_, hs, apply_lastBelow hX h (hlow l)⟩
  · obtain ⟨h₁, h₂⟩ := lastBelow_eq_and_firstBelow_eq_of_le h
    show P (lastBelow X v l) (firstBelow X v l)
    rw [h₁, h₂]
    exact hPd v

/-- **Rigidity with an exceptional set of times.** The form of `eq_or_swap_of_contour_pairs` in which the straddling
pairs of `L` and `R` are required to be contour pairs of `L'` or `R'` only when their left time avoids a set of times
`Z` whose images under `L` and `R` are Lebesgue-null. -/
theorem eq_or_swap_of_contour_pairs_of_volume_image {L R L' R' : ℝ → ℝ} {Q : Set ℝ}
    (hL : IsLadderRegularOn L Q) (hR : IsLadderRegularOn R Q) (hL' : IsLadderRegularOn L' Q)
    (hR' : IsLadderRegularOn R' Q) (hQ : Dense Q)
    (hNC : ∀ s t, IsWeakContourPair L' s t → IsWeakContourPair R' s t → False) {Z : Set ℝ}
    (hZL : volume (L '' Z) = 0) (hZR : volume (R '' Z) = 0)
    (hcolL : ∀ w ∈ Q, ∀ l, lastBelow L w l ∉ Z → l < L w →
      IsContourPair L' (lastBelow L w l) (firstBelow L w l) ∨
        IsContourPair R' (lastBelow L w l) (firstBelow L w l))
    (hcolR : ∀ w ∈ Q, ∀ l, lastBelow R w l ∉ Z → l < R w →
      IsContourPair L' (lastBelow R w l) (firstBelow R w l) ∨
        IsContourPair R' (lastBelow R w l) (firstBelow R w l))
    {t₀ c : ℝ} (hL0 : L t₀ = c) (hR0 : R t₀ = c) (hL'0 : L' t₀ = c) (hR'0 : R' t₀ = c) (hLR : L ≠ R) :
    (L' = L ∧ R' = R) ∨ (L' = R ∧ R' = L) := by
  refine eq_or_swap_of_contour_pairs hL hR hL' hR' hQ hNC (P := fun s t => s = t ∨ s ∉ Z)
    (fun w _ => dense_setOf_straddle_of_volume_image_eq_zero hL.continuous (fun l => (hL.low w l).1) hZL
      (fun _ _ h => Or.inr h) (fun _ => Or.inl rfl))
    (fun w _ => dense_setOf_straddle_of_volume_image_eq_zero hR.continuous (fun l => (hR.low w l).1) hZR
      (fun _ _ h => Or.inr h) (fun _ => Or.inl rfl))
    (fun w hw l hP hl => ?_) (fun w hw l hP hl => ?_) hL0 hR0 hL'0 hR'0 hLR
  · rcases hP with h | h
    · exact absurd h ((lastBelow_lt hL.continuous hl (hL.low w l).1).trans
        (lt_firstBelow hL.continuous hl (hL.low w l).2)).ne
    · exact hcolL w hw l h hl
  · rcases hP with h | h
    · exact absurd h ((lastBelow_lt hR.continuous hl (hR.low w l).1).trans
        (lt_firstBelow hR.continuous hl (hR.low w l).2)).ne
    · exact hcolR w hw l h hl

end LatticeProb
