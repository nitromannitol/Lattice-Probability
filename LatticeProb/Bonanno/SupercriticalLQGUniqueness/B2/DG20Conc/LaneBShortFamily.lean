/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBShortFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBShortLower
import Mathlib.Data.Fintype.EquivFin

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

open Classical in
def laneBShortRects (R : ℝ) : Finset (Circle × ℂ) :=
  (laneBBoundaryBlocks (laneBGridRadius R)).biUnion (T20D.shortJ 0)

theorem laneB_shortRects_card_le {R : ℝ} (hR : 24 ≤ R) :
    ((laneBShortRects R).card : ℝ) ≤ 44 * R := by
  classical
  have hcard : (laneBShortRects R).card ≤
      ∑ b ∈ laneBBoundaryBlocks (laneBGridRadius R), (T20D.shortJ 0 b).card := by
    exact Finset.card_biUnion_le
  have hsum : (∑ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
      (T20D.shortJ 0 b).card) ≤
      4 * (laneBBoundaryBlocks (laneBGridRadius R)).card := by
    calc
      _ ≤ ∑ _b ∈ laneBBoundaryBlocks (laneBGridRadius R), 4 :=
        Finset.sum_le_sum (fun b _ => T20D.card_shortJ_le 0 b)
      _ = _ := by simp [mul_comm]
  have hreal : ((laneBShortRects R).card : ℝ) ≤
      4 * ((laneBBoundaryBlocks (laneBGridRadius R)).card : ℝ) := by
    exact_mod_cast hcard.trans hsum
  have hb := laneB_boundaryBlocks_card_le_linear hR
  nlinarith

theorem laneB_shortRect_of_annulus_small
    {R : ℝ} (hR : 24 ≤ R) (ξ : ℝ) (f : ℂ → ℝ) (a : ℝ)
    (hsmall : crossLenIn ξ f
      {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
      (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) < ENNReal.ofReal a) :
    ∃ j ∈ laneBShortRects R,
      T20B.mrectLen ξ f 0 j.1 j.2 1 3 < a := by
  classical
  obtain ⟨b, hb, j, hj, hlt⟩ :=
    laneB_short_rectangle_of_annulus_small hR ξ f a hsmall
  exact ⟨j, Finset.mem_biUnion.mpr ⟨b, hb, hj⟩, hlt⟩

 


noncomputable def laneBShortEnumerate (R : ℝ) (k : ℕ) : Circle × ℂ :=
  if hk : k < (laneBShortRects R).card then
    ((laneBShortRects R).equivFin.symm ⟨k, hk⟩ : Circle × ℂ)
  else (1, 0)

theorem laneB_shortEnumerate_surj (R : ℝ)
    {j : Circle × ℂ} (hj : j ∈ laneBShortRects R) :
    ∃ k ∈ Finset.range (laneBShortRects R).card,
      laneBShortEnumerate R k = j := by
  classical
  let x : (laneBShortRects R) := ⟨j, hj⟩
  let k := (laneBShortRects R).equivFin x
  refine ⟨k.val, Finset.mem_range.mpr k.isLt, ?_⟩
  simp [laneBShortEnumerate, k.isLt, k, x]

 
theorem laneB_large_annulus_short_family
    {R : ℝ} (hR : 24 ≤ R) :
    ∃ (Js : Finset ℕ) (us : ℕ → Circle) (cs : ℕ → ℂ),
      (Js.card : ℝ) ≤ 44 * R ∧
      ∀ (ξ : ℝ) (f : ℂ → ℝ) (a : ℝ),
        crossLenIn ξ f
          {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
          (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) < ENNReal.ofReal a →
          ∃ j ∈ Js, T20B.mrectLen ξ f 0 (us j) (cs j) 1 3 < a := by
  let Js := Finset.range (laneBShortRects R).card
  let us : ℕ → Circle := fun k => (laneBShortEnumerate R k).1
  let cs : ℕ → ℂ := fun k => (laneBShortEnumerate R k).2
  refine ⟨Js, us, cs, ?_, ?_⟩
  · simpa only [Js, Finset.card_range] using laneB_shortRects_card_le hR
  · intro ξ f a hsmall
    obtain ⟨j, hj, hlt⟩ := laneB_shortRect_of_annulus_small hR ξ f a hsmall
    obtain ⟨k, hk, hkj⟩ := laneB_shortEnumerate_surj R hj
    exact ⟨k, hk, by simpa only [us, cs, hkj] using hlt⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
