import LatticeProb.LQG.CoupledContactArc
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DDrawing
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0SideStrict

/-! # Sided contact sets of two cells

For a contour coordinate `X` and two non-consecutive cells `I_x = [ε(x-1), εx]` and
`I_y = [ε(y-1), εy]`, the *direct `X`-contact times* are the times `s ∈ I_x` which are directly
`X`-identified with a time `u ∈ I_y`: `X s = X u < X v` for `s < v < u`.

Deterministically, under the Peanosphere bundle, the image of these times under the curve lies
in both cells; every contact time has its `X`-value in the closed level window
`[max(inf_{I_x} X, inf_{I_y} X), inf_{[εx, ε(y-1)]} X]`; if the window is degenerate there is at
most one contact time; and every level strictly inside the window is the value of the last
contact before `εx`, which is a contact time.

For the curve of a mating-of-trees coupling, almost surely for all meshes and all
non-consecutive pairs, the contact image of each coordinate is nontrivial exactly when its
window is strict, and then it contains an arc lying in both cell frontiers. This is the
description of the adjacency condition (1.1) of the mated-CRT map by two cells intersecting
along a non-trivial arc of their left (respectively right) outer boundaries (Gwynne-Miller-
Sheffield, after Duplantier-Miller-Sheffield, Section 8.2). Hence the *sided contact
multiplicity*, the number of coordinates with a nontrivial contact image, is the number of
strict windows for all meshes, and almost surely at a fixed mesh the number of coordinates
satisfying (1.1).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal unitInterval

namespace MatedCRTHarmonic.RouteM

variable {ω : MatedCRT.Path2} {η : ℝ → ℂ}

/-- The direct `X`-contact times of the cells `x` and `y`: the times of `[ε(x-1), εx]` which are
directly `X`-identified with a time of `[ε(y-1), εy]`. -/
def directContactTimes (ε : ℝ) (X : ℝ → ℝ) (x y : ℤ) : Set ℝ :=
  {s | s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x) ∧
    ∃ u ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y), directRel X s u}

/-- If direct `X`-identifications are identified by the curve, the image of the direct contact
times lies in both cells. -/
theorem image_directContactTimes_subset {X : ℝ → ℝ}
    (hmerge : ∀ s u, directRel X s u → η s = η u) (ε : ℝ) (x y : ℤ) :
    η '' directContactTimes ε X x y ⊆
      η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  rintro _ ⟨s, ⟨hs, u, hu, hrel⟩, rfl⟩
  exact ⟨⟨s, hs, rfl⟩, ⟨u, hu, (hmerge s u hrel).symm⟩⟩

/-- A direct contact time has its value in the closed level window. -/
theorem mem_window_of_mem_directContactTimes {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ}
    (hε : 0 < ε) {x y : ℤ} (hxy : x + 1 < y) {s : ℝ} (hs : s ∈ directContactTimes ε X x y) :
    dWinLo ε X x y ≤ X s ∧ X s ≤ dWinHi ε X x y := by
  obtain ⟨hsx, u, hu, hlt, heq, habove⟩ := hs
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hab : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have hbc : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hcd : ε * ((y : ℝ) - 1) ≤ ε * y := by nlinarith
  refine ⟨max_le ((DAux.intervalInf_spec hX hab).2 s hsx) ?_, ?_⟩
  · rw [heq]
    exact (DAux.intervalInf_spec hX hcd).2 u hu
  · obtain ⟨v, hv, hXv⟩ := (DAux.intervalInf_spec hX hbc).1
    change X s ≤ MatedCRT.intervalInf X (ε * x) (ε * ((y : ℝ) - 1))
    rw [← hXv]
    by_cases hvs : v ≤ s
    · have : v = s := le_antisymm hvs (hsx.2.trans hv.1)
      rw [this]
    · by_cases hvu : u ≤ v
      · have : v = u := le_antisymm (hv.2.trans hu.1) hvu
        rw [this, heq]
      · exact (habove v ⟨lt_of_not_ge hvs, lt_of_not_ge hvu⟩).le

/-- If the level window is degenerate, there is at most one direct contact time. -/
theorem directContactTimes_subsingleton {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ}
    (hε : 0 < ε) {x y : ℤ} (hxy : x + 1 < y) (hwin : dWinHi ε X x y ≤ dWinLo ε X x y) :
    (directContactTimes ε X x y).Subsingleton := by
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hbc : ε * (x : ℝ) < ε * ((y : ℝ) - 1) := by nlinarith
  have key : ∀ s ∈ directContactTimes ε X x y, ∀ s' ∈ directContactTimes ε X x y,
      s < s' → False := by
    intro s hs s' hs' hss'
    have h1 := mem_window_of_mem_directContactTimes hX hε hxy hs
    have h2 := mem_window_of_mem_directContactTimes hX hε hxy hs'
    obtain ⟨_, u, hu, _, _, habove⟩ := hs
    have hs'u : s' < u := lt_of_le_of_lt hs'.1.2 (lt_of_lt_of_le hbc hu.1)
    have := habove s' ⟨hss', hs'u⟩
    linarith [h1.1, h1.2, h2.1, h2.2]
  intro s hs s' hs'
  rcases lt_trichotomy s s' with h | h | h
  · exact (key s hs s' hs' h).elim
  · exact h
  · exact (key s' hs' s hs h).elim

/-- Every level strictly inside the window is the value of the last contact before `εx`, which
is a direct contact time. -/
theorem dLast_mem_directContactTimes {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ} (hε : 0 < ε)
    {x y : ℤ} (hxy : x + 1 < y) {lev : ℝ} (hlo : dWinLo ε X x y < lev)
    (hhi : lev < dWinHi ε X x y) :
    dLast X (ε * x) lev ∈ directContactTimes ε X x y := by
  obtain ⟨h, -⟩ := lowArcData_contacts hX hε hxy hlo hhi
  exact ⟨Ioo_subset_Icc_self h.mem₁, _, Ioo_subset_Icc_self h.mem₂, h.rel⟩

/-- A nontrivial contact image forces a strict level window. -/
theorem lt_of_nontrivial_image_directContactTimes {X : ℝ → ℝ} (hX : Continuous X) {ε : ℝ}
    (hε : 0 < ε) {x y : ℤ} (hxy : x + 1 < y)
    (h : (η '' directContactTimes ε X x y).Nontrivial) :
    dWinLo ε X x y < dWinHi ε X x y := by
  by_contra hwin
  exact Set.not_nontrivial_iff.2
    ((directContactTimes_subsingleton hX hε hxy (not_lt.1 hwin)).image η) h

open Classical in
/-- The sided contact multiplicity of two cells: the number of contour coordinates whose
direct contact image is nontrivial. -/
noncomputable def sidedContactMult (ε : ℝ) (ω : MatedCRT.Path2) (η : ℝ → ℂ) (x y : ℤ) : ℕ :=
  (if (η '' directContactTimes ε (lCoord ω) x y).Nontrivial then 1 else 0) +
    (if (η '' directContactTimes ε (rCoord ω) x y).Nontrivial then 1 else 0)

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

private theorem nontrivial_of_arc {p : C(unitInterval, ℂ)} (hp : Function.Injective p)
    {S : Set ℂ} (hS : range p ⊆ S) : S.Nontrivial := by
  refine ⟨p 0, hS ⟨0, rfl⟩, p 1, hS ⟨1, rfl⟩, fun h => ?_⟩
  have := congrArg Subtype.val (hp h)
  norm_num at this

/-- Left sided contacts: almost surely, for all meshes and non-consecutive cells, the image of
the direct left contact times lies in both cells, is nontrivial exactly when the left window is
strict, and then contains an arc of both cell frontiers. -/
theorem ae_left_sided_contact
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      (η ω) '' directContactTimes ε (lCoord (bm ω)) x y ⊆
          (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
        (((η ω) '' directContactTimes ε (lCoord (bm ω)) x y).Nontrivial ↔
          dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y) ∧
        (dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
          ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
            range p ⊆ (η ω) '' directContactTimes ε (lCoord (bm ω)) x y ∧
            (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
            (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)))) := by
  filter_upwards [ae_peanosphere D, ae_left_contact_window_arc D] with ω hP harc
  intro ε x y hε hxy
  have hX : Continuous (lCoord (bm ω)) := continuous_lCoord
  have hmerge : ∀ s u, directRel (lCoord (bm ω)) s u → η ω s = η ω u :=
    fun s u h => hP.merge s u (Or.inl h)
  have hArc : dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
        range p ⊆ (η ω) '' directContactTimes ε (lCoord (bm ω)) x y ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) := by
    intro hwin
    set lo := dWinLo ε (lCoord (bm ω)) x y
    set hi := dWinHi ε (lCoord (bm ω)) x y
    obtain ⟨p, hp, hr, hfx, hfy⟩ := harc ε x y ((2 * lo + hi) / 3) ((lo + 2 * hi) / 3) hε hxy
      (by linarith) (by linarith) (by linarith)
    refine ⟨p, hp, ?_, hfx, hfy⟩
    intro z hz
    obtain ⟨lev, hlev, rfl⟩ := hr hz
    exact ⟨_, dLast_mem_directContactTimes hX hε hxy (by linarith [hlev.1])
      (by linarith [hlev.2]), rfl⟩
  refine ⟨image_directContactTimes_subset hmerge ε x y,
    ⟨lt_of_nontrivial_image_directContactTimes hX hε hxy, fun hwin => ?_⟩, hArc⟩
  obtain ⟨p, hp, hr, -⟩ := hArc hwin
  exact nontrivial_of_arc hp hr

/-- Right sided contacts: the analogue of `ae_left_sided_contact` for the right coordinate. -/
theorem ae_right_sided_contact
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      (η ω) '' directContactTimes ε (rCoord (bm ω)) x y ⊆
          (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
        (((η ω) '' directContactTimes ε (rCoord (bm ω)) x y).Nontrivial ↔
          dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y) ∧
        (dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
          ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
            range p ⊆ (η ω) '' directContactTimes ε (rCoord (bm ω)) x y ∧
            (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
            (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)))) := by
  filter_upwards [ae_peanosphere D, ae_right_contact_window_arc D] with ω hP harc
  intro ε x y hε hxy
  have hX : Continuous (rCoord (bm ω)) := continuous_rCoord
  have hmerge : ∀ s u, directRel (rCoord (bm ω)) s u → η ω s = η ω u :=
    fun s u h => hP.merge s u (Or.inr h)
  have hArc : dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      ∃ p : C(unitInterval, ℂ), Function.Injective p ∧
        range p ⊆ (η ω) '' directContactTimes ε (rCoord (bm ω)) x y ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x))) ∧
        (∀ t, p t ∈ frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) := by
    intro hwin
    set lo := dWinLo ε (rCoord (bm ω)) x y
    set hi := dWinHi ε (rCoord (bm ω)) x y
    obtain ⟨p, hp, hr, hfx, hfy⟩ := harc ε x y ((2 * lo + hi) / 3) ((lo + 2 * hi) / 3) hε hxy
      (by linarith) (by linarith) (by linarith)
    refine ⟨p, hp, ?_, hfx, hfy⟩
    intro z hz
    obtain ⟨lev, hlev, rfl⟩ := hr hz
    exact ⟨_, dLast_mem_directContactTimes hX hε hxy (by linarith [hlev.1])
      (by linarith [hlev.2]), rfl⟩
  refine ⟨image_directContactTimes_subset hmerge ε x y,
    ⟨lt_of_nontrivial_image_directContactTimes hX hε hxy, fun hwin => ?_⟩, hArc⟩
  obtain ⟨p, hp, hr, -⟩ := hArc hwin
  exact nontrivial_of_arc hp hr

open Classical in
/-- Almost surely, for all meshes and non-consecutive cells, the sided contact multiplicity is
the number of strict level windows. -/
theorem ae_sidedContactMult_eq_strict_windows
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      sidedContactMult ε (bm ω) (η ω) x y =
        (if dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y then 1 else 0) +
          (if dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y then 1 else 0) := by
  filter_upwards [ae_left_sided_contact D, ae_right_sided_contact D] with ω hl hr
  intro ε x y hε hxy
  have h1 := (hl ε x y hε hxy).2.1
  have h2 := (hr ε x y hε hxy).2.1
  unfold sidedContactMult
  by_cases a : dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y <;>
    by_cases b : dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y <;>
    simp [a, b, h1, h2]

open Classical in
/-- At a fixed positive mesh, almost surely for all non-consecutive cells the sided contact
multiplicity is the number of coordinates satisfying the side condition (1.1). -/
theorem ae_sidedContactMult_eq_sideCond_count {ε : ℝ} (hε : 0 < ε)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ x y : ℤ, x + 1 < y →
      sidedContactMult ε (bm ω) (η ω) x y =
        (if SideCond ε (lCoord (bm ω)) x y then 1 else 0) +
          (if SideCond ε (rCoord (bm ω)) x y then 1 else 0) := by
  have hs : ∀ᵐ ω ∂P, SideStrict ε (bm ω) :=
    ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable (ae_sideStrict D.boundaryLawBM ε hε)
  filter_upwards [ae_sidedContactMult_eq_strict_windows D, hs] with ω hm hs
  intro x y hxy
  rw [hm ε x y hε hxy]
  have iL : SideCond ε (lCoord (bm ω)) x y ↔
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y :=
    ⟨DAux.dWin_lt_L hs hxy, fun h => h.le⟩
  have iR : SideCond ε (rCoord (bm ω)) x y ↔
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y :=
    ⟨DAux.dWin_lt_R hs hxy, fun h => h.le⟩
  by_cases a : dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y <;>
    by_cases b : dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y <;>
    simp [a, b, iL, iR]

end MatedCRTHarmonic.MoTInput
