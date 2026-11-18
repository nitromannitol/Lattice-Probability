import LatticeProb.LQG.ContactWindowComponentOneSidedCount

/-! # Simultaneous running infima merge the left and right contact windows

Let `(L, R)` be the contour pair of a mating-of-trees coupling and `b < t`. Suppose both
coordinates stay strictly above their values at `t` throughout `[b, t)`: `t` is a
simultaneous strict running infimum of `L` and `R` started at `b` (a `π/2`-cone time whose
cone interval contains `[b, t]`). Then the last time before `b` at which `L ≤ L_t` is
directly `L`-identified with `t`, and likewise for `R`, so the space-filling curve maps both
last contacts to `η t`.

Consequently, for two nonconsecutive cells `η([ε(x-1), εx])` and `η([ε(y-1), εy])`, if such a
time `t` after `εx` has `L_t` and `R_t` in the open left and right contact windows, then the
left and right contact images meet at `η t` (a pinch point of the two boundary arcs), and one
nonsingleton component of the cell intersection contains both. If moreover every nonsingleton
component meets a strict contact-window image, the intersection has exactly one nonsingleton
component, although both contact windows are strict.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.RouteM

variable {ω : MatedCRT.Path2} {η : ℝ → ℂ}

/-- If `L` stays strictly above `L_t` on `[b, t)`, the last time before `b` at which
`L ≤ L_t` is directly `L`-identified with `t`. -/
theorem directRel_ellMinus_of_forall_Ico_lt (P : Peanosphere ω η) {b t : ℝ} (hbt : b < t)
    (hL : ∀ u ∈ Ico b t, lCoord ω t < lCoord ω u) :
    directRel (fun u => (ω u).1) (ellMinus ω b (lCoord ω t)) t := by
  have hmem := ellMinus_mem P b (lCoord ω t)
  have hlev : lCoord ω (ellMinus ω b (lCoord ω t)) = lCoord ω t :=
    ellMinus_level P (hL b ⟨le_rfl, hbt⟩)
  refine ⟨lt_of_le_of_lt hmem.1 hbt, hlev, ?_⟩
  intro u hu
  change lCoord ω (ellMinus ω b (lCoord ω t)) < lCoord ω u
  rw [hlev]
  rcases le_or_gt b u with hbu | hub
  · exact hL u ⟨hbu, hu.2⟩
  · by_contra hle
    rw [not_lt] at hle
    have hbdd : BddAbove {s | s ≤ b ∧ lCoord ω s ≤ lCoord ω t} := ⟨b, fun s hs => hs.1⟩
    have hle' : u ≤ ellMinus ω b (lCoord ω t) := le_csSup hbdd ⟨hub.le, hle⟩
    exact (not_lt.mpr hle') hu.1

/-- If `R` stays strictly above `R_t` on `[b, t)`, the last time before `b` at which
`R ≤ R_t` is directly `R`-identified with `t`. -/
theorem directRel_rhoMinus_of_forall_Ico_lt (P : Peanosphere ω η) {b t : ℝ} (hbt : b < t)
    (hR : ∀ u ∈ Ico b t, rCoord ω t < rCoord ω u) :
    directRel (fun u => (ω u).2) (rhoMinus ω b (rCoord ω t)) t := by
  have hmem := rhoMinus_mem P b (rCoord ω t)
  have hlev : rCoord ω (rhoMinus ω b (rCoord ω t)) = rCoord ω t :=
    rhoMinus_level P (hR b ⟨le_rfl, hbt⟩)
  refine ⟨lt_of_le_of_lt hmem.1 hbt, hlev, ?_⟩
  intro u hu
  change rCoord ω (rhoMinus ω b (rCoord ω t)) < rCoord ω u
  rw [hlev]
  rcases le_or_gt b u with hbu | hub
  · exact hR u ⟨hbu, hu.2⟩
  · by_contra hle
    rw [not_lt] at hle
    have hbdd : BddAbove {s | s ≤ b ∧ rCoord ω s ≤ rCoord ω t} := ⟨b, fun s hs => hs.1⟩
    have hle' : u ≤ rhoMinus ω b (rCoord ω t) := le_csSup hbdd ⟨hub.le, hle⟩
    exact (not_lt.mpr hle') hu.1

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, at every simultaneous strict running infimum `t` of `L` and `R` started
at `b < t`, the last `L`- and `R`-contacts before `b` at the levels `L_t`, `R_t` are both
mapped to `η t`. -/
theorem ae_last_contacts_eq_of_simultaneous_running_inf
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ b t : ℝ, b < t →
      (∀ u ∈ Ico b t, lCoord (bm ω) t < lCoord (bm ω) u) →
      (∀ u ∈ Ico b t, rCoord (bm ω) t < rCoord (bm ω) u) →
      η ω (ellMinus (bm ω) b (lCoord (bm ω) t)) = η ω t ∧
        η ω (rhoMinus (bm ω) b (rCoord (bm ω) t)) = η ω t := by
  filter_upwards [ae_peanosphere D] with ω hP
  intro b t hbt hL hR
  exact ⟨hP.merge _ _ (Or.inl (directRel_ellMinus_of_forall_Ico_lt hP hbt hL)),
    hP.merge _ _ (Or.inr (directRel_rhoMinus_of_forall_Ico_lt hP hbt hR))⟩

/-- Almost surely, for all meshes and nonconsecutive cells: if a simultaneous strict running
infimum `t` of `L` and `R` started at `εx` has `L_t` and `R_t` in the open contact windows,
then a single nonsingleton component of the cell intersection contains `η t` and every
compact strict left and right contact-window image. -/
theorem ae_contact_window_component_of_simultaneous_running_inf
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (t : ℝ),
      0 < ε → x + 1 < y → ε * x < t →
      (∀ u ∈ Ico (ε * x) t, lCoord (bm ω) t < lCoord (bm ω) u) →
      (∀ u ∈ Ico (ε * x) t, rCoord (bm ω) t < rCoord (bm ω) u) →
      dWinLo ε (lCoord (bm ω)) x y < lCoord (bm ω) t →
      lCoord (bm ω) t < dWinHi ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < rCoord (bm ω) t →
      rCoord (bm ω) t < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ∃ C ∈ LatticeProb.nonSingletonComponents S, η ω t ∈ C ∧
        (∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) ∧
        (∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) := by
  filter_upwards [ae_contact_window_components_count D,
    ae_last_contacts_eq_of_simultaneous_running_inf D] with ω hcount hlast
  intro ε x y t hε hxy hxt hL hR hl1 hl2 hr1 hr2
  obtain ⟨C, hC, E, hE, hCl, hEr, -, -⟩ :=
    hcount ε x y hε hxy (hl1.trans hl2) (hr1.trans hr2)
  obtain ⟨hzl, hzr⟩ := hlast (ε * x) t hxt hL hR
  obtain ⟨m, hm1, hm2⟩ := exists_between hl2
  obtain ⟨n, hn1, hn2⟩ := exists_between hr2
  have htC : η ω t ∈ C := by
    rw [← hzl]
    exact hCl _ _ hl1 hm2 hm1 (mem_image_of_mem _ ⟨le_rfl, hm1.le⟩)
  have htE : η ω t ∈ E := by
    rw [← hzr]
    exact hEr _ _ hr1 hn2 hn1 (mem_image_of_mem _ ⟨le_rfl, hn1.le⟩)
  have hCE : C = E :=
    LatticeProb.eq_of_mem_connectedComponentIn_image_of_inter_nonempty hC.1 hE.1
      ⟨η ω t, htC, htE⟩
  subst hCE
  exact ⟨C, hC, htC, hCl, hEr⟩

/-- Almost surely, for all meshes and nonconsecutive cells: on a simultaneous strict running
infimum `t` of `L` and `R` started at `εx` with `L_t`, `R_t` in the open contact windows, if
every nonsingleton component meets a strict contact-window image, the cell intersection has
exactly one nonsingleton component, although both contact windows are strict. -/
theorem ae_contact_window_components_count_one_of_simultaneous_running_inf
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (t : ℝ),
      0 < ε → x + 1 < y → ε * x < t →
      (∀ u ∈ Ico (ε * x) t, lCoord (bm ω) t < lCoord (bm ω) u) →
      (∀ u ∈ Ico (ε * x) t, rCoord (bm ω) t < rCoord (bm ω) u) →
      dWinLo ε (lCoord (bm ω)) x y < lCoord (bm ω) t →
      lCoord (bm ω) t < dWinHi ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < rCoord (bm ω) t →
      rCoord (bm ω) t < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      (∀ C ∈ LatticeProb.nonSingletonComponents S,
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty) →
      (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_contact_window_components_exact_count_of_meets_windows D,
    ae_last_contacts_eq_of_simultaneous_running_inf D] with ω hcount hlast
  intro ε x y t hε hxy hxt hL hR hl1 hl2 hr1 hr2 S hmeet
  obtain ⟨C, hC, E, hE, hCl, hEr, -, hone, -⟩ :=
    hcount ε x y hε hxy (hl1.trans hl2) (hr1.trans hr2) hmeet
  obtain ⟨hzl, hzr⟩ := hlast (ε * x) t hxt hL hR
  obtain ⟨m, hm1, hm2⟩ := exists_between hl2
  obtain ⟨n, hn1, hn2⟩ := exists_between hr2
  have htC : η ω t ∈ C := by
    rw [← hzl]
    exact hCl _ _ hl1 hm2 hm1 (mem_image_of_mem _ ⟨le_rfl, hm1.le⟩)
  have htE : η ω t ∈ E := by
    rw [← hzr]
    exact hEr _ _ hr1 hn2 hn1 (mem_image_of_mem _ ⟨le_rfl, hn1.le⟩)
  exact hone (LatticeProb.eq_of_mem_connectedComponentIn_image_of_inter_nonempty hC.1 hE.1
    ⟨η ω t, htC, htE⟩)

end MatedCRTHarmonic.MoTInput
