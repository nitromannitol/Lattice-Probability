import LatticeProb.LQG.ContactWindowComponentLowGammaCount

/-! # Contact-window component counts with at most one strict window

Consider two nonconsecutive cells of the space-filling curve of a mating-of-trees
coupling, and suppose that every nonsingleton connected component of their intersection
meets the image of a strict contact window. If exactly one of the two contact windows
(left or right boundary length) is strict, the intersection has exactly one nonsingleton
component, namely the component containing the images of that window. If neither window
is strict, the intersection has no nonsingleton component. For `0 < γ ≤ √2` the covering
hypothesis holds almost surely, simultaneously for all meshes and cell pairs.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb

/-- Two connected components of `S` which meet coincide. -/
theorem eq_of_mem_connectedComponentIn_image_of_inter_nonempty
    {β : Type*} [TopologicalSpace β] {S C E : Set β}
    (hC : C ∈ connectedComponentIn S '' S) (hE : E ∈ connectedComponentIn S '' S)
    (h : (C ∩ E).Nonempty) : C = E := by
  obtain ⟨p, -, rfl⟩ := hC
  obtain ⟨q, -, rfl⟩ := hE
  obtain ⟨z, hzC, hzE⟩ := h
  rw [connectedComponentIn_eq hzC, connectedComponentIn_eq hzE]

/-- If every compact subinterval of an open interval maps into `C`, so does the open
interval. -/
theorem image_Ioo_subset_of_forall_Icc_subset
    {β : Type*} (f : ℝ → β) {lo hi : ℝ} {C : Set β}
    (h : ∀ a b, lo < a → b < hi → a < b → f '' Icc a b ⊆ C) :
    f '' Ioo lo hi ⊆ C := by
  rintro _ ⟨l, ⟨hlo, hhi⟩, rfl⟩
  exact h ((lo + l) / 2) ((l + hi) / 2) (by linarith) (by linarith) (by linarith)
    ⟨l, ⟨by linarith, by linarith⟩, rfl⟩

/-- If every nonsingleton component of `S` meets a set `U` contained in the image of one
open window whose compact subwindows all map into the nonsingleton component `C`, then
`C` is the only nonsingleton component. -/
theorem nonSingletonComponents_eq_singleton_of_meets_window
    {β : Type*} [TopologicalSpace β] {S C U : Set β} (f : ℝ → β) {lo hi : ℝ}
    (hC : C ∈ nonSingletonComponents S)
    (hsub : ∀ a b, lo < a → b < hi → a < b → f '' Icc a b ⊆ C)
    (hmeet : ∀ E ∈ nonSingletonComponents S, (E ∩ U).Nonempty)
    (hU : U ⊆ f '' Ioo lo hi) :
    nonSingletonComponents S = {C} := by
  refine Set.Subset.antisymm (fun E hE => ?_) (Set.singleton_subset_iff.mpr hC)
  obtain ⟨z, hzE, hzU⟩ := hmeet E hE
  exact eq_of_mem_connectedComponentIn_image_of_inter_nonempty hE.1 hC.1
    ⟨z, hzE, image_Ioo_subset_of_forall_Icc_subset f hsub (hU hzU)⟩

/-- If every nonsingleton component of `S` meets the empty set, there is none. -/
theorem nonSingletonComponents_eq_empty_of_meets_empty
    {β : Type*} [TopologicalSpace β] {S U : Set β}
    (hmeet : ∀ E ∈ nonSingletonComponents S, (E ∩ U).Nonempty) (hU : U = ∅) :
    nonSingletonComponents S = ∅ := by
  subst hU
  refine Set.eq_empty_iff_forall_notMem.mpr fun E hE => ?_
  obtain ⟨z, -, hz⟩ := hmeet E hE
  simp at hz

end LatticeProb

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- A strict left contact window determines a nonsingleton component of the whole cell
intersection containing the images of all its compact subwindows. -/
theorem ae_left_contact_window_nonSingletonComponent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      ∃ C ∈ LatticeProb.nonSingletonComponents
          ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
           (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
        ∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C := by
  filter_upwards [ae_left_contact_windows_one_component D,
    ae_shared_frontiers_of_coupling D] with ω hl hf
  intro ε x y hε hxy hleft
  obtain ⟨C, hC, hCinf, hCl⟩ := hl ε x y hε hxy hleft
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  rw [← hfront] at hC
  exact ⟨C, ⟨hC, hCinf.nontrivial.not_subsingleton⟩, hCl⟩

/-- A strict right contact window determines a nonsingleton component of the whole cell
intersection containing the images of all its compact subwindows. -/
theorem ae_right_contact_window_nonSingletonComponent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      ∃ C ∈ LatticeProb.nonSingletonComponents
          ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
           (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
        ∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C := by
  filter_upwards [ae_right_contact_windows_one_component D,
    ae_shared_frontiers_of_coupling D] with ω hr hf
  intro ε x y hε hxy hright
  obtain ⟨C, hC, hCinf, hCr⟩ := hr ε x y hε hxy hright
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  rw [← hfront] at hC
  exact ⟨C, ⟨hC, hCinf.nontrivial.not_subsingleton⟩, hCr⟩

/-- If each nonsingleton cell-intersection component meets a strict contact window, and
only the left window is strict, there is exactly one nonsingleton component. -/
theorem ae_contact_window_components_left_only_of_meets_windows
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      dWinHi ε (rCoord (bm ω)) x y ≤ dWinLo ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      (∀ C ∈ LatticeProb.nonSingletonComponents S,
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty) →
      ∃ C ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) ∧
        LatticeProb.nonSingletonComponents S = {C} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_left_contact_window_nonSingletonComponent D] with ω hl
  intro ε x y hε hxy hleft hright
  dsimp only
  intro hmeet
  obtain ⟨C, hC, hCl⟩ := hl ε x y hε hxy hleft
  have hS := LatticeProb.nonSingletonComponents_eq_singleton_of_meets_window _ hC hCl hmeet
    (by rw [Set.Ioo_eq_empty (not_lt.mpr hright), Set.image_empty, Set.union_empty])
  refine ⟨C, hC, hCl, hS, ?_, ?_⟩
  · rw [hS, Set.ncard_singleton]
  · rw [hS, Set.encard_singleton]

/-- If each nonsingleton cell-intersection component meets a strict contact window, and
only the right window is strict, there is exactly one nonsingleton component. -/
theorem ae_contact_window_components_right_only_of_meets_windows
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinHi ε (lCoord (bm ω)) x y ≤ dWinLo ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      (∀ C ∈ LatticeProb.nonSingletonComponents S,
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty) →
      ∃ E ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ E) ∧
        LatticeProb.nonSingletonComponents S = {E} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_right_contact_window_nonSingletonComponent D] with ω hr
  intro ε x y hε hxy hleft hright
  dsimp only
  intro hmeet
  obtain ⟨E, hE, hEr⟩ := hr ε x y hε hxy hright
  have hS := LatticeProb.nonSingletonComponents_eq_singleton_of_meets_window _ hE hEr hmeet
    (by rw [Set.Ioo_eq_empty (not_lt.mpr hleft), Set.image_empty, Set.empty_union])
  refine ⟨E, hE, hEr, hS, ?_, ?_⟩
  · rw [hS, Set.ncard_singleton]
  · rw [hS, Set.encard_singleton]

/-- If each nonsingleton cell-intersection component meets a strict contact window, and
neither window is strict, there is no nonsingleton component. -/
theorem contact_window_components_none_of_meets_windows
    (η : C(ℝ, ℂ)) (b : Path2) (ε : ℝ) (x y : ℤ)
    (hleft : dWinHi ε (lCoord b) x y ≤ dWinLo ε (lCoord b) x y)
    (hright : dWinHi ε (rCoord b) x y ≤ dWinLo ε (rCoord b) x y) :
    let S := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
    (∀ C ∈ LatticeProb.nonSingletonComponents S,
      (C ∩ ((fun level => η (ellMinus b (ε * x) level)) ''
        Ioo (dWinLo ε (lCoord b) x y) (dWinHi ε (lCoord b) x y) ∪
        (fun level => η (rhoMinus b (ε * x) level)) ''
        Ioo (dWinLo ε (rCoord b) x y) (dWinHi ε (rCoord b) x y))).Nonempty) →
    LatticeProb.nonSingletonComponents S = ∅ ∧
      (LatticeProb.nonSingletonComponents S).ncard = 0 ∧
      (LatticeProb.nonSingletonComponents S).encard = 0 := by
  dsimp only
  intro hmeet
  have hS := LatticeProb.nonSingletonComponents_eq_empty_of_meets_empty hmeet
    (by rw [Set.Ioo_eq_empty (not_lt.mpr hleft), Set.Ioo_eq_empty (not_lt.mpr hright),
      Set.image_empty, Set.image_empty, Set.union_empty])
  refine ⟨hS, ?_, ?_⟩
  · rw [hS, Set.ncard_empty]
  · rw [hS, Set.encard_empty]

/-- For `0 < γ ≤ √2`, if only the left contact window is strict, the cell intersection
has exactly one nonsingleton component. -/
theorem ae_contact_window_components_left_only_of_le_sqrt_two
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      dWinHi ε (rCoord (bm ω)) x y ≤ dWinLo ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ∃ C ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) ∧
        LatticeProb.nonSingletonComponents S = {C} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_contact_window_components_left_only_of_meets_windows D,
    ae_contact_components_meet_windows_of_le_sqrt_two hγ0 hγ D] with ω hcount hmeet
  intro ε x y hε hxy hl hr
  exact hcount ε x y hε hxy hl hr (hmeet ε x y hε hxy)

/-- For `0 < γ ≤ √2`, if only the right contact window is strict, the cell intersection
has exactly one nonsingleton component. -/
theorem ae_contact_window_components_right_only_of_le_sqrt_two
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinHi ε (lCoord (bm ω)) x y ≤ dWinLo ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ∃ E ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ E) ∧
        LatticeProb.nonSingletonComponents S = {E} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_contact_window_components_right_only_of_meets_windows D,
    ae_contact_components_meet_windows_of_le_sqrt_two hγ0 hγ D] with ω hcount hmeet
  intro ε x y hε hxy hl hr
  exact hcount ε x y hε hxy hl hr (hmeet ε x y hε hxy)

/-- For `0 < γ ≤ √2`, if neither contact window is strict, the cell intersection has no
nonsingleton component. -/
theorem ae_contact_window_components_none_of_le_sqrt_two
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinHi ε (lCoord (bm ω)) x y ≤ dWinLo ε (lCoord (bm ω)) x y →
      dWinHi ε (rCoord (bm ω)) x y ≤ dWinLo ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      LatticeProb.nonSingletonComponents S = ∅ ∧
        (LatticeProb.nonSingletonComponents S).ncard = 0 ∧
        (LatticeProb.nonSingletonComponents S).encard = 0 := by
  filter_upwards [ae_contact_components_meet_windows_of_le_sqrt_two hγ0 hγ D] with ω hmeet
  intro ε x y hε hxy hl hr
  exact contact_window_components_none_of_meets_windows (η ω) (bm ω) ε x y hl hr
    (hmeet ε x y hε hxy)

end MatedCRTHarmonic.MoTInput
