import LatticeProb.LQG.ContactWindowComponent
import LatticeProb.Topology.RandomShiftedCellComponentArray

/-! # Component counts from contour contact windows -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Strict contact windows on both sides determine non-singleton components of
    the whole cell intersection. If these components are distinct, the extended
    component count is at least two. -/
theorem ae_contact_window_components_count
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ∃ C ∈ LatticeProb.nonSingletonComponents S, ∃ D ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) ∧
        (∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ D) ∧
        1 ≤ (LatticeProb.nonSingletonComponents S).encard ∧
        (C ≠ D → 2 ≤ (LatticeProb.nonSingletonComponents S).encard) := by
  filter_upwards [ae_left_contact_windows_one_component D,
    ae_right_contact_windows_one_component D, ae_shared_frontiers_of_coupling D] with ω hl hr hf
  intro ε x y hε hxy hleft hright
  obtain ⟨C, hC, hCinf, hCl⟩ := hl ε x y hε hxy hleft
  obtain ⟨E, hE, hEinf, hEr⟩ := hr ε x y hε hxy hright
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  rw [← hfront] at hC hE
  have hCN : C ∈ LatticeProb.nonSingletonComponents
      ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
       (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) :=
    ⟨hC, hCinf.nontrivial.not_subsingleton⟩
  have hEN : E ∈ LatticeProb.nonSingletonComponents
      ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
       (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) :=
    ⟨hE, hEinf.nontrivial.not_subsingleton⟩
  refine ⟨C, hCN, E, hEN, hCl, hEr, Set.one_le_encard_iff_nonempty.mpr ⟨C, hCN⟩, ?_⟩
  intro hne
  calc
    2 = ({C, E} : Set (Set ℂ)).encard := (Set.encard_pair hne).symm
    _ ≤ _ := Set.encard_mono (Set.pair_subset hCN hEN)

end MatedCRTHarmonic.MoTInput
