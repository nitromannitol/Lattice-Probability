import LatticeProb.Analysis.ExcursionCountShift
import LatticeProb.Analysis.ExcursionCountRational
import LatticeProb.Analysis.ExcursionCountSandwich
import LatticeProb.Analysis.LadderSetOfStraddlingPairs

/-!
# The end of the first long excursion

For a set `K ⊆ ℝ` (in the applications the forward ladder set of a continuous path from `0`) and `ε > 0`,
`longEndSet K ε` is the set of points `x ∈ K` preceded, after `0`, by a closed interval with rational endpoints of
length larger than `ε` that does not meet `K`. Its infimum `ρ` is the right end of the first complementary interval of
`K` of length larger than `ε`. The facts proved here, all deterministic, are used to restart a path at `ρ`:

* `csInf_mem_longEndSet`: for closed `K` the infimum is attained;
* `excursionCount_csInf_longEndSet_le_one`: at most one excursion of length larger than `ε` ends by time `ρ`;
* `mem_longEndSet_of_one_le_excursionCount`, `one_le_excursionCount_of_mem_longEndSet`: a point of `K` lies in
  `longEndSet K ε` iff at least one excursion of length larger than `ε` is completed by that time;
* `excursionCount_le_restart_csInf_longEndSet`: if a continuous path has at least `k + 1` excursions above its
  running minimum of length larger than `ε` before its first passage below `X 0 - b`, the path restarted at `ρ` has at
  least `k` of them before its own first passage below its starting value minus `b`;
* `exists_mem_longEndSet_le_congr`: whether `ρ ≤ t` depends only on `K ∩ [0, t]`;
* `le_firstPassageBelow_iff_forall_Icc`: `T` is at most the first passage below `X 0 - b` iff `X ≥ X 0 - b` on `[0, T]`.

The rational form of the excursion count (`le_excursionCount_iff`) replaces every argument on components.
-/

open Set

namespace LatticeProb.LadderSet

variable {K : Set ℝ} {ε : ℝ}

/-- The ends of long gaps of `K`: points `x ∈ K` such that some closed interval `[r, u]` with rational endpoints,
`0 ≤ r`, `r + ε < u ≤ x`, does not meet `K`. -/
def longEndSet (K : Set ℝ) (ε : ℝ) : Set ℝ :=
  {x | x ∈ K ∧ ∃ r u : ℚ, 0 ≤ (r : ℝ) ∧ (r : ℝ) + ε < u ∧ (u : ℝ) ≤ x ∧ ∀ y ∈ Icc (r : ℝ) u, y ∉ K}

theorem lt_of_mem_longEndSet {x : ℝ} (hx : x ∈ longEndSet K ε) : ε < x := by
  obtain ⟨-, r, u, hr, hru, hux, -⟩ := hx
  linarith

theorem bddBelow_longEndSet (hε : 0 < ε) : BddBelow (longEndSet K ε) :=
  ⟨0, fun _ hx => (hε.trans (lt_of_mem_longEndSet hx)).le⟩

/-- **The end of the first long gap is attained.** For a closed set `K` and `ε > 0`, if `longEndSet K ε` is nonempty
then its infimum belongs to it. -/
theorem csInf_mem_longEndSet (hK : IsClosed K) (hε : 0 < ε) (hne : (longEndSet K ε).Nonempty) :
    sInf (longEndSet K ε) ∈ longEndSet K ε := by
  have hρK : sInf (longEndSet K ε) ∈ K :=
    hK.closure_subset_iff.2 (fun _ hx => hx.1) (csInf_mem_closure hne (bddBelow_longEndSet hε))
  obtain ⟨x, hx, hxρ⟩ := exists_lt_of_csInf_lt hne
    (show sInf (longEndSet K ε) < sInf (longEndSet K ε) + ε by linarith)
  obtain ⟨-, r, u, hr, hru, hux, hfree⟩ := hx
  refine ⟨hρK, r, u, hr, hru, ?_, hfree⟩
  by_contra hlt
  exact hfree _ ⟨by linarith, (not_le.1 hlt).le⟩ hρK

/-- **At most one long excursion ends by the end of the first one.** -/
theorem excursionCount_csInf_longEndSet_le_one (hε : 0 < ε) :
    excursionCount K 0 (sInf (longEndSet K ε)) ε ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ excursionCount K 0 (sInf (longEndSet K ε)) ε := by omega
  obtain ⟨r, u, hint, hsep⟩ := (le_excursionCount_iff hε 2).1 h2
  obtain ⟨x, hxK, hx⟩ := hsep 0 1 (by decide)
  have key : ∀ i j : Fin 2, (u i : ℝ) ≤ x → x ≤ r j → False := by
    intro i j hux hxr
    have hmem : x ∈ longEndSet K ε := ⟨hxK, r i, u i, (hint i).1, (hint i).2.1, hux, (hint i).2.2.2⟩
    have hle : sInf (longEndSet K ε) ≤ x := csInf_le (bddBelow_longEndSet hε) hmem
    have h1 := (hint j).2.1
    have h2 := (hint j).2.2.1
    linarith
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key 0 1 h1 h2
  · exact key 1 0 h1 h2

/-- A point of `K` by which a long excursion is completed lies in `longEndSet K ε`. -/
theorem mem_longEndSet_of_one_le_excursionCount (hε : 0 < ε) {t : ℝ} (htK : t ∈ K)
    (h : 1 ≤ excursionCount K 0 t ε) : t ∈ longEndSet K ε := by
  obtain ⟨r, u, hint, -⟩ := (le_excursionCount_iff hε 1).1 h
  exact ⟨htK, r 0, u 0, (hint 0).1, (hint 0).2.1, (hint 0).2.2.1, (hint 0).2.2.2⟩

/-- A long excursion is completed by any time after a point of `longEndSet K ε`. -/
theorem one_le_excursionCount_of_mem_longEndSet (hε : 0 < ε) {x t : ℝ} (hx : x ∈ longEndSet K ε) (hxt : x ≤ t) :
    1 ≤ excursionCount K 0 t ε := by
  obtain ⟨-, r, u, hr, hru, hux, hfree⟩ := hx
  refine (le_excursionCount_iff hε 1).2
    ⟨fun _ => r, fun _ => u, fun _ => ⟨hr, hru, hux.trans hxt, hfree⟩, fun i j hij => ?_⟩
  exact absurd (Subsingleton.elim i j) hij

/-- **Restart at the end of the first long excursion.** Let `X` be continuous, `ε > 0`, assume that `X`
goes below `X 0 - b` and has at least `k + 1` excursions above its running minimum of length larger than `ε` before
its first passage below `X 0 - b`. Let `ρ` be the end of the first such excursion and `Y u = X (ρ + u) + c` for
`u ≥ 0`. If `X` goes below `X ρ - b` after `ρ`, then `Y` has at least `k` excursions above its running minimum of
length larger than `ε` before its first passage below `Y 0 - b`. Moreover `ρ` is at most the first passage of `X`. -/
theorem excursionCount_le_restart_csInf_longEndSet {X Y : ℝ → ℝ} (hX : Continuous X) {b c : ℝ}
    (hε : 0 < ε) {k : ℕ} (hne : ∃ s, 0 ≤ s ∧ X s < X 0 - b)
    (hk : k + 1 ≤ excursionCount (forwardLadderSet X 0) 0 (firstPassageBelow X 0 b) ε) :
    sInf (longEndSet (forwardLadderSet X 0) ε) ∈ longEndSet (forwardLadderSet X 0) ε ∧
      sInf (longEndSet (forwardLadderSet X 0) ε) ≤ firstPassageBelow X 0 b ∧
      ((∀ u, 0 ≤ u → Y u = X (sInf (longEndSet (forwardLadderSet X 0) ε) + u) + c) →
        (∃ s, sInf (longEndSet (forwardLadderSet X 0) ε) ≤ s ∧
          X s < X (sInf (longEndSet (forwardLadderSet X 0) ε)) - b) →
        k ≤ excursionCount (forwardLadderSet Y 0) 0 (firstPassageBelow Y 0 b) ε) := by
  have hτK : firstPassageBelow X 0 b ∈ forwardLadderSet X 0 := firstPassageBelow_mem_forwardLadderSet hX hne
  have hτL : firstPassageBelow X 0 b ∈ longEndSet (forwardLadderSet X 0) ε :=
    mem_longEndSet_of_one_le_excursionCount hε hτK (by omega)
  have hTL := csInf_mem_longEndSet (isClosed_forwardLadderSet hX) hε ⟨_, hτL⟩
  have hTτ : sInf (longEndSet (forwardLadderSet X 0) ε) ≤ firstPassageBelow X 0 b :=
    csInf_le (bddBelow_longEndSet hε) hτL
  refine ⟨hTL, hTτ, fun hY hneY => ?_⟩
  set T := sInf (longEndSet (forwardLadderSet X 0) ε) with hTdef
  have hTK : T ∈ forwardLadderSet X 0 := hTL.1
  have hT0 : 0 ≤ T := hTK.1
  have hsplit := excursionCount_add hTK hT0 hTτ hε
  have h1 : excursionCount (forwardLadderSet X 0) 0 T ε ≤ 1 := excursionCount_csInf_longEndSet_le_one hε
  have hloc : excursionCount (forwardLadderSet X 0) T (firstPassageBelow X 0 b) ε =
      excursionCount (forwardLadderSet X T) T (firstPassageBelow X 0 b) ε := by
    refine excursionCount_congr_of_inter_Ici ?_ _ ε
    rw [forwardLadderSet_inter_Ici hTK]
    exact (inter_eq_left.2 fun t ht => ht.1).symm
  have hXT : X T ≤ X 0 := hTK.2 0 ⟨le_refl _, hT0⟩
  have hττ' : firstPassageBelow X 0 b ≤ firstPassageBelow X T b := by
    obtain ⟨s, hs, hsX⟩ := hneY
    show sInf {t | 0 ≤ t ∧ X t < X 0 - b} ≤ sInf {t | T ≤ t ∧ X t < X T - b}
    exact csInf_le_csInf ⟨0, fun t ht => ht.1⟩ ⟨s, hs, hsX⟩ fun t ht => ⟨hT0.trans ht.1, by linarith [ht.2]⟩
  have hmono := excursionCount_mono_right (forwardLadderSet X T) T hε hττ'
  rw [excursionCount_shift hY hneY ε]
  omega

/-- **Locality of `ρ ≤ t`.** Whether a point of `longEndSet K ε` lies in `[0, t]` depends only on `K ∩ [0, t]`. -/
theorem exists_mem_longEndSet_le_congr {K' : Set ℝ} (hε : 0 < ε) {t : ℝ} (h : K ∩ Icc 0 t = K' ∩ Icc 0 t) :
    (∃ x ∈ longEndSet K ε, x ≤ t) ↔ ∃ x ∈ longEndSet K' ε, x ≤ t := by
  have key : ∀ {K₁ K₂ : Set ℝ}, K₁ ∩ Icc 0 t = K₂ ∩ Icc 0 t →
      (∃ x ∈ longEndSet K₁ ε, x ≤ t) → ∃ x ∈ longEndSet K₂ ε, x ≤ t := by
    rintro K₁ K₂ h ⟨x, ⟨hxK, r, u, hr, hru, hux, hfree⟩, hxt⟩
    have hx : x ∈ Icc 0 t := ⟨by linarith, hxt⟩
    refine ⟨x, ⟨((Set.ext_iff.1 h x).1 ⟨hxK, hx⟩).1, r, u, hr, hru, hux, fun y hy hyK => hfree y hy ?_⟩, hxt⟩
    have hyI : y ∈ Icc 0 t := ⟨hr.trans hy.1, hy.2.trans (hux.trans hxt)⟩
    exact ((Set.ext_iff.1 h y).2 ⟨hyK, hyI⟩).1
  exact ⟨key h, key h.symm⟩

/-- **Before the first passage.** For a continuous path that goes below `X 0 - b` (`b ≥ 0`), a time `T` is at most
its first passage below `X 0 - b` iff `X ≥ X 0 - b` on `[0, T]`. -/
theorem le_firstPassageBelow_iff_forall_Icc {X : ℝ → ℝ} {b T : ℝ} (hX : Continuous X) (hb : 0 ≤ b)
    (hne : ∃ s, 0 ≤ s ∧ X s < X 0 - b) :
    T ≤ firstPassageBelow X 0 b ↔ ∀ s ∈ Icc 0 T, X 0 - b ≤ X s := by
  have hbdd : BddBelow {t | 0 ≤ t ∧ X t < X 0 - b} := ⟨0, fun t ht => ht.1⟩
  constructor
  · intro hT s hs
    rcases (hs.2.trans hT).lt_or_eq with hlt | heq
    · by_contra hcon
      exact (not_le.2 hlt) (csInf_le hbdd ⟨hs.1, not_le.1 hcon⟩)
    · rw [heq, apply_firstPassageBelow_eq hX hne hb]
  · intro h
    obtain ⟨s, hs0, hs⟩ := hne
    refine le_csInf ⟨s, hs0, hs⟩ fun t ht => ?_
    by_contra hcon
    exact (not_le.2 ht.2) (h t ⟨ht.1, (not_le.1 hcon).le⟩)

end LatticeProb.LadderSet
