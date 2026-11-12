import Mathlib
import LatticeProb.Prob.UpcrossGlue
import LatticeProb.Prob.UpcrossReversalPathwise
import LatticeProb.Prob.UpcrossShift

/-!
# Pathwise stopping of the glued path

Let `y`, `z` be continuous paths started at `0`, `a > 0`, `a < b`, and `T = glueTime a y` the first
hit of `-a` by `y` (assumed finite).  The glued path `G = glueC a y z` is `s ↦ a + y (T - s)` up to
time `T` and `s ↦ a + z (s - T)` afterwards.

* `stopAt_glueC_of_levelFailure`: if `y` hits `-a` before `b - a`, then `G` first hits `b` after
  `T`, at the time `T + τ` with `τ` the first hit of `b - a` by `z`, and `G` stopped there is the
  reversed piece of `y` followed by `z` stopped at `τ`.
* `stopAt_glueC_of_levelSuccess`: if `y` hits `b - a` before `-a`, then `G` first hits `b` before
  `T`, and `G` stopped there is the time reversal of the first up-crossing piece to `b` of the
  negated increments of `y` after its first hit of `b - a`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A continuous path from `0` stays below a positive level before its first hit of it. -/
lemma lt_of_coe_lt_hitFrom {w : ℝ≥0 → ℝ} {c : ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hc : 0 < c) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < hitFrom c 0 w) : w u < c := by
  by_contra h
  replace h := not_lt.1 h
  obtain ⟨s, hs, hws⟩ := intermediate_value_Icc (zero_le) hw.continuousOn
    ⟨by rw [hw0]; exact hc.le, h⟩
  exact lt_irrefl _ (hu.trans_le ((hitFrom_le zero_le hws).trans (ENNReal.coe_le_coe.2 hs.2)))

section Glue

variable {a b : ℝ} {y z : C(ℝ≥0, ℝ)}

lemma hitFrom_neg_eq_glueTime (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤) :
    hitFrom (-a) 0 (y : ℝ≥0 → ℝ) = (glueTime a y : ℝ≥0∞) := by
  unfold glueTime; exact (ENNReal.coe_toNNReal hT).symm

lemma coe_y_glueTime (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤) : y (glueTime a y) = -a := by
  obtain ⟨s, hsT, -, hs, -⟩ := exists_hitFrom_eq y.continuous hT
  have : glueTime a y = s := by
    unfold glueTime
    rw [hsT]; simp
  rw [this]; exact hs

/-- If `y` hits `-a` before `b - a`, the glued path stays below `b` up to the time `T`. -/
lemma glueC_lt_of_le_glueTime (hab : a < b) (hy : y 0 = 0) (hz : z 0 = 0)
    (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hlt : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) < hitFrom (b - a) 0 (y : ℝ≥0 → ℝ))
    {s : ℝ≥0} (hs : s ≤ glueTime a y) : glueC a y z s < b := by
  rw [glueC_apply_of_le hs, hz]
  have hTe := hitFrom_neg_eq_glueTime hT
  have : y (glueTime a y - s) < b - a :=
    lt_of_coe_lt_hitFrom y.continuous hy (by linarith)
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 tsub_le_self) (hTe ▸ hlt))
  linarith

/-- **First hit of `b` by the glued path, when `y` hits `-a` before `b - a`.** -/
lemma hitFrom_glueC_of_levelFailure (hab : a < b) (hy : y 0 = 0) (hz : z 0 = 0)
    (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hlt : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) < hitFrom (b - a) 0 (y : ℝ≥0 → ℝ)) :
    hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ) =
      (glueTime a y : ℝ≥0∞) + hitFrom (b - a) 0 (z : ℝ≥0 → ℝ) := by
  have hbelow := fun s (hs : s ≤ glueTime a y) => glueC_lt_of_le_glueTime hab hy hz hT hlt hs
  by_cases hz' : hitFrom (b - a) 0 (z : ℝ≥0 → ℝ) = ⊤
  · rw [hz', add_top]
    refine top_unique (le_iInf₂ fun s hs => ?_)
    exfalso
    rcases le_or_gt s (glueTime a y) with h | h
    · exact (hbelow s h).ne hs.2
    · have hzs : z (s - glueTime a y) = b - a := by
        have := hs.2
        rw [glueC_apply_of_ge hy h.le] at this
        linarith
      exact (ENNReal.coe_ne_top (r := s - glueTime a y)) (top_unique
        (hz' ▸ hitFrom_le zero_le hzs))
  · obtain ⟨e, he, -, hze, hmin⟩ := exists_hitFrom_eq z.continuous hz'
    rw [he, ← ENNReal.coe_add]
    refine le_antisymm ?_ (le_iInf₂ fun s hs => ?_)
    · refine hitFrom_le zero_le ?_
      rw [show (glueC a y z : ℝ≥0 → ℝ) (glueTime a y + e) = glueC a y z (glueTime a y + e) from rfl,
        glueC_apply_of_ge hy le_self_add, add_tsub_cancel_left, hze]
      ring
    · rcases le_or_gt s (glueTime a y) with h | h
      · exact absurd hs.2 (hbelow s h).ne
      · have hzs : z (s - glueTime a y) = b - a := by
          have := hs.2
          rw [glueC_apply_of_ge hy h.le] at this
          linarith
        exact ENNReal.coe_le_coe.2 ((le_tsub_iff_left h.le).1 (hmin _ zero_le hzs))

/-- **P1.**  If `y` hits `-a` before `b - a`, the glued path stopped at its first hit of `b` is the
reversed piece of `y` followed by `z` stopped at its first hit of `b - a`. -/
theorem stopAt_glueC_of_levelFailure (hab : a < b) (hy : y 0 = 0) (hz : z 0 = 0)
    (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hlt : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) < hitFrom (b - a) 0 (y : ℝ≥0 → ℝ)) :
    ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ)) (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
      concatAt (glueTime a y) (revLevel a (glueTime a y) (-(y : ℝ≥0 → ℝ)))
        ((stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) := by
  rw [hitFrom_glueC_of_levelFailure hab hy hz hT hlt]
  funext s
  simp only [stopAt_apply, concatAt, revLevel, Pi.neg_apply]
  by_cases hz' : hitFrom (b - a) 0 (z : ℝ≥0 → ℝ) = ⊤
  · rw [hz']
    simp only [add_top, le_top, inf_of_le_left, ENNReal.toNNReal_coe, glueC_apply]
    ring
  · obtain ⟨e, he, -⟩ := exists_hitFrom_eq z.continuous hz'
    rw [he, ← ENNReal.coe_add, ← ENNReal.coe_min, ← ENNReal.coe_min, ENNReal.toNNReal_coe,
      ENNReal.toNNReal_coe]
    rcases le_total s (glueTime a y + e) with h | h
    · rw [min_eq_left h, min_eq_left (tsub_le_iff_left.2 h), glueC_apply]
      ring
    · have hTs : glueTime a y ≤ s := le_self_add.trans h
      have h1 : glueTime a y - (glueTime a y + e) = 0 := tsub_eq_zero_of_le le_self_add
      have h2 : glueTime a y - s = 0 := tsub_eq_zero_of_le hTs
      rw [min_eq_right h, min_eq_right ((le_tsub_iff_left hTs).2 h), glueC_apply, h1,
        add_tsub_cancel_left, h2, hy]
      ring

/-- **P2.**  If `y` hits `b - a` before `-a`, the glued path stopped at its first hit of `b` is the
time reversal of the first up-crossing piece to `b` of the negated increments of `y` after its first
hit of `b - a`; it does not depend on `z`. -/
theorem stopAt_glueC_of_levelSuccess (ha : 0 < a) (hab : a < b) (hz : z 0 = 0)
    (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hlt : hitFrom (b - a) 0 (y : ℝ≥0 → ℝ) < hitFrom (-a) 0 (y : ℝ≥0 → ℝ)) :
    ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ)) (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
      upcrossRev b (firstUpcrossPiece b
        (-((shiftPath (hitFrom (b - a) 0 (y : ℝ≥0 → ℝ)).toNNReal y : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ))) := by
  have hb : 0 < b := ha.trans hab
  have hTe := hitFrom_neg_eq_glueTime hT
  set T := glueTime a y with hTdef
  have hlt' : hitFrom (b - a) 0 (y : ℝ≥0 → ℝ) < (T : ℝ≥0∞) := by rw [← hTe]; exact hlt
  have hτfin : hitFrom (b - a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤ := ne_top_of_lt hlt'
  obtain ⟨τ, hτe, -, hyτ, -⟩ := exists_hitFrom_eq y.continuous hτfin
  have hτT : τ ≤ T := ENNReal.coe_le_coe.1 (by rw [← hτe]; exact hlt'.le)
  rw [hτe, ENNReal.toNNReal_coe]
  set v : ℝ≥0 → ℝ := -((shiftPath τ y : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) with hvdef
  have hvapp : ∀ u, v u = (b - a) - y (τ + u) := fun u => by
    rw [hvdef]; simp only [Pi.neg_apply, shiftPath_apply, hyτ]; ring
  have hv_cont : Continuous v := (shiftPath τ y).continuous.neg
  have hv0 : v 0 = 0 := by rw [hvapp]; simp [hyτ]
  have hvhit : hitFrom b 0 v = ((T - τ : ℝ≥0) : ℝ≥0∞) := by
    refine le_antisymm ?_ (le_iInf₂ fun s hs => ?_)
    · refine hitFrom_le zero_le ?_
      rw [hvapp, add_tsub_cancel_of_le hτT, coe_y_glueTime hT]; ring
    · have hys : y (τ + s) = -a := by have := hs.2; rw [hvapp] at this; linarith
      have h1 : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≤ ((τ + s : ℝ≥0) : ℝ≥0∞) := hitFrom_le zero_le hys
      rw [hTe] at h1
      exact ENNReal.coe_le_coe.2 (tsub_le_iff_left.2 (ENNReal.coe_le_coe.1 h1))
  have hend : upcrossEnd₁ b v = ((T - τ : ℝ≥0) : ℝ≥0∞) := by
    rw [upcrossEnd₁_of_zero_start hv0, hvhit]
  obtain ⟨d, hd, hI, -⟩ := isUpcross_upcrossStart₁ hv_cont hb
    (by rw [hend]; exact ENNReal.coe_ne_top)
  have hdT : d = T - τ := ENNReal.coe_inj.1 (hd.symm.trans hend)
  set g := upcrossStart₁ b v with hg
  obtain ⟨hgd, hvg, hvd, hmid⟩ := hI
  have hgd' : g < T - τ := by rw [← hdT]; exact hgd
  have hlamT : τ + g ≤ T := (le_tsub_iff_left hτT).1 hgd'.le
  set D := d - g with hD
  have hgD : g + D = d := add_tsub_cancel_of_le hgd.le
  have hTD : T - D = τ + g := by
    rw [hD, hdT, tsub_tsub, tsub_tsub_cancel_of_le hlamT]
  have hDT : D ≤ T := (tsub_le_self).trans (hdT ▸ tsub_le_self)
  have hsum : τ + g + D = T := ((tsub_eq_iff_eq_add_of_le hDT).1 hTD).symm
  have hylam : y (τ + g) = b - a := by have := hvg; rw [hvapp] at this; linarith
  have hGD : glueC a y z D = b := by
    rw [glueC_apply_of_le hDT, hz, hTD, hylam]; ring
  have hσ : hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ) = (D : ℝ≥0∞) := by
    refine le_antisymm (hitFrom_le zero_le hGD) (le_iInf₂ fun s hs => ?_)
    have hsb : glueC a y z s = b := hs.2
    rcases le_or_gt T s with hTs | hsT
    · exact ENNReal.coe_le_coe.2 (hDT.trans hTs)
    · by_contra hcon
      have hsD : s < D := ENNReal.coe_lt_coe.1 (not_le.1 hcon)
      rw [glueC_apply_of_le hsT.le, hz] at hsb
      have hyu : y (T - s) = b - a := by linarith
      have h1 : s + (τ + g) < T :=
        (add_lt_add_of_lt_of_le hsD le_rfl).trans_eq (by rw [add_comm]; exact hsum)
      have h2 : τ + g < T - s := lt_tsub_iff_left.2 h1
      have hτu : τ ≤ T - s := le_self_add.trans h2.le
      have hgs' : g < T - s - τ := lt_tsub_iff_left.2 h2
      have hs'd : T - s - τ ≤ d := by rw [hdT]; exact tsub_le_tsub_right tsub_le_self τ
      have hvs' : v (T - s - τ) = 0 := by rw [hvapp, add_tsub_cancel_of_le hτu, hyu]; ring
      rcases hs'd.lt_or_eq with hlt2 | heq
      · exact (hmid _ hgs' hlt2).1.ne' hvs'
      · rw [heq, hvd] at hvs'; exact hb.ne' hvs'
  have hdd : (upcrossEnd₁ b v).toNNReal = d := by rw [hd]; exact ENNReal.toNNReal_coe d
  rw [upcrossRev_firstUpcrossPiece hv_cont hb, hdd, ← hg, ← hD, hσ]
  funext s
  simp only [stopAt_apply, revLevel, firstUpcrossPiece, pieceAt, hdd, ← hg]
  rw [← ENNReal.coe_min, ENNReal.toNNReal_coe]
  rcases le_total s D with hsD | hDs
  · rw [min_eq_left hsD, glueC_apply_of_le (hsD.trans hDT), hz]
    have hmin : g + (D - s) ≤ d := (add_le_add le_rfl tsub_le_self).trans hgD.le
    have hidx : τ + (g + (D - s)) = T - s := by
      rw [← add_assoc, ← add_tsub_assoc_of_le hsD, hsum]
    rw [min_eq_left hmin, hvapp, hidx]
    ring
  · rw [min_eq_right hDs, hGD, tsub_eq_zero_of_le hDs, add_zero, min_eq_left hgd.le, hvg]
    ring

end Glue

end LatticeProb
