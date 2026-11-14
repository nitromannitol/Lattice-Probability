/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortPiece
import Mathlib.Data.Fintype.EquivFin

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

theorem laneC_short_family_le_small_crossLen (i : Bool) (ξ : ℝ) (f : ℂ → ℝ) :
    (⨅ b ∈ laneCShortBlocks,
       ⨅ j ∈ T20D.shortJ 3 b,
         crossLenIn ξ f (T20D.RS 3 j) (T20D.RS₁ 3 j) (T20D.RS₂ 3 j)) ≤
      crossLenIn ξ f (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) := by
  apply le_crossLenIn
  intro G hG
  obtain ⟨z, hz, w, hw, hpath, hmap⟩ := hG
  obtain ⟨b, hb, j, hj, hle⟩ :=
    laneC_short_piece_of_small_annulus i hpath hz hw hmap
  exact (iInf₂_le b hb).trans ((iInf₂_le j hj).trans hle)

theorem laneC_short_rectangle_of_small (i : Bool) (ξ : ℝ) (f : ℂ → ℝ) (a : ℝ)
    (hsmall : crossLenIn ξ f (laneCUnitUcross i)
      (laneCUnitInner i) (laneCUnitOuter i) < ENNReal.ofReal a) :
    ∃ j ∈ laneCShortRects, T20B.mrectLen ξ f 3 j.1 j.2 1 3 < a := by
  classical
  have h := (laneC_short_family_le_small_crossLen i ξ f).trans_lt hsmall
  obtain ⟨b, hb'⟩ := iInf_lt_iff.mp h
  obtain ⟨hb, hj'⟩ := iInf_lt_iff.mp hb'
  obtain ⟨j, hj''⟩ := iInf_lt_iff.mp hj'
  obtain ⟨hj, hlt⟩ := iInf_lt_iff.mp hj''
  refine ⟨j, ?_, ?_⟩
  · rw [laneCShortRects_eq]
    exact Finset.mem_biUnion.mpr ⟨b, hb, hj⟩
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

noncomputable def laneCShortEnumerate (k : ℕ) : Circle × ℂ :=
  if hk : k < laneCShortRects.card then
    ((laneCShortRects.equivFin.symm ⟨k, hk⟩ : Circle × ℂ))
  else (1, 0)

theorem laneC_shortEnumerate_surj {j : Circle × ℂ} (hj : j ∈ laneCShortRects) :
    ∃ k ∈ Finset.range laneCShortRects.card, laneCShortEnumerate k = j := by
  classical
  let x : laneCShortRects := ⟨j, hj⟩
  let k := laneCShortRects.equivFin x
  refine ⟨k.val, Finset.mem_range.mpr k.isLt, ?_⟩
  simp [laneCShortEnumerate, k.isLt, k, x]

 

theorem laneC_unit_short_family :
    ∃ (Js : Finset ℕ) (us : ℕ → Circle) (cs : ℕ → ℂ),
      (Js.card : ℝ) ≤ 12996 ∧
      ∀ (i : Bool) (ξ : ℝ) (f : ℂ → ℝ) (a : ℝ),
        crossLenIn ξ f (laneCUnitUcross i)
          (laneCUnitInner i) (laneCUnitOuter i) < ENNReal.ofReal a →
          ∃ j ∈ Js, T20B.mrectLen ξ f 3 (us j) (cs j) 1 3 < a := by
  let Js := Finset.range laneCShortRects.card
  let us : ℕ → Circle := fun k => (laneCShortEnumerate k).1
  let cs : ℕ → ℂ := fun k => (laneCShortEnumerate k).2
  refine ⟨Js, us, cs, ?_, ?_⟩
  · simpa only [Js, Finset.card_range] using laneC_shortRects_card_le
  · intro i ξ f a hsmall
    obtain ⟨j, hj, hlt⟩ := laneC_short_rectangle_of_small i ξ f a hsmall
    obtain ⟨k, hk, hkj⟩ := laneC_shortEnumerate_surj hj
    exact ⟨k, hk, by simpa only [us, cs, hkj] using hlt⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
