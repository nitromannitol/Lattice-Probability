/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongPlacement
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue2
import Mathlib.Data.Fintype.EquivFin

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

open Classical in
def laneBLongRects (R : ℝ) : Finset (Circle × ℂ) :=
  (laneBBoundaryBlocks (laneBGridRadius R)).biUnion fun b =>
    Finset.univ.image (S6U.siteJ 0 b)

theorem laneB_longRects_card_le {R : ℝ} (hR : 24 ≤ R) :
    ((laneBLongRects R).card : ℝ) ≤ 44 * R := by
  classical
  have hcard : (laneBLongRects R).card ≤
      ∑ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
        (Finset.univ.image (S6U.siteJ 0 b)).card := Finset.card_biUnion_le
  have hsum :
      (∑ b ∈ laneBBoundaryBlocks (laneBGridRadius R),
        (Finset.univ.image (S6U.siteJ 0 b)).card) ≤
        4 * (laneBBoundaryBlocks (laneBGridRadius R)).card := by
    calc
      _ ≤ ∑ _b ∈ laneBBoundaryBlocks (laneBGridRadius R), 4 := by
        apply Finset.sum_le_sum
        intro b _
        simpa using (Finset.card_image_le :
          (Finset.univ.image (S6U.siteJ 0 b)).card ≤ (Finset.univ : Finset (Fin 4)).card)
      _ = _ := by simp [mul_comm]
  have hreal : ((laneBLongRects R).card : ℝ) ≤
      4 * ((laneBBoundaryBlocks (laneBGridRadius R)).card : ℝ) := by
    exact_mod_cast hcard.trans hsum
  have hb := laneB_boundaryBlocks_card_le_linear hR
  nlinarith

 
noncomputable def laneBLongEnumerate (R : ℝ) (k : ℕ) : Circle × ℂ :=
  if hk : k < (laneBLongRects R).card then
    ((laneBLongRects R).equivFin.symm ⟨k, hk⟩ : Circle × ℂ)
  else (1, 0)

theorem laneB_longEnumerate_surj (R : ℝ)
    {j : Circle × ℂ} (hj : j ∈ laneBLongRects R) :
    ∃ k ∈ Finset.range (laneBLongRects R).card,
      laneBLongEnumerate R k = j := by
  classical
  let x : (laneBLongRects R) := ⟨j, hj⟩
  let k := (laneBLongRects R).equivFin x
  refine ⟨k.val, Finset.mem_range.mpr k.isLt, ?_⟩
  simp [laneBLongEnumerate, k.isLt, k, x]

end SupercriticalLQGUniqueness.B2.DG20Conc
