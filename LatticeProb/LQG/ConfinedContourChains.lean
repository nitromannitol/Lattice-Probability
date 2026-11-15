import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel
import Mathlib.Logic.Relation

/-! # Contour identifications confined to an interval -/

set_option autoImplicit false

open Set MatedCRTHarmonic.MatedCRT

namespace LatticeProb

/-- Direct identifications with endpoints in an interval depend only on the
values of the contour on that interval. -/
theorem directRel_iff_of_eqOn_Icc {X Y : ℝ → ℝ} {a b s t : ℝ}
    (h : EqOn X Y (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    DirectRel X s t ↔ DirectRel Y s t := by
  have hi : ∀ u ∈ Ioo s t, u ∈ Icc a b := by
    intro u hu
    exact ⟨le_trans hs.1 (le_of_lt hu.1), le_trans (le_of_lt hu.2) ht.2⟩
  have hinner : (∀ u ∈ Ioo s t, Y s < X u) ↔
      (∀ u ∈ Ioo s t, Y s < Y u) := by
    constructor <;> intro hx u hu <;> simpa only [h (hi u hu)] using hx u hu
  simp only [DirectRel, h hs, h ht, hinner]

/-- Generated identifications whose intermediate times stay in an interval
are determined by the two contours on that interval. -/
theorem confined_eqvGen_directRel_iff {X Y X' Y' : ℝ → ℝ} {a b : ℝ}
    (hX : EqOn X X' (Icc a b)) (hY : EqOn Y Y' (Icc a b))
    (s t : Icc a b) :
    Relation.EqvGen (fun u v : Icc a b => DirectRel X u v ∨ DirectRel Y u v) s t ↔
      Relation.EqvGen (fun u v : Icc a b => DirectRel X' u v ∨ DirectRel Y' u v) s t := by
  have hrel : (fun u v : Icc a b => DirectRel X u v ∨ DirectRel Y u v) =
      (fun u v : Icc a b => DirectRel X' u v ∨ DirectRel Y' u v) := by
    funext u v
    exact propext (or_congr (directRel_iff_of_eqOn_Icc hX u.2 v.2)
      (directRel_iff_of_eqOn_Icc hY u.2 v.2))
  rw [hrel]

/-- Every confined identification is also an identification in the full
parameter space. -/
theorem eqvGen_directRel_of_confined {X Y : ℝ → ℝ} {a b : ℝ} {s t : Icc a b}
    (h : Relation.EqvGen (fun u v : Icc a b => DirectRel X u v ∨ DirectRel Y u v) s t) :
    Relation.EqvGen (fun u v : ℝ => DirectRel X u v ∨ DirectRel Y u v) s t := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ huv
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

end LatticeProb
