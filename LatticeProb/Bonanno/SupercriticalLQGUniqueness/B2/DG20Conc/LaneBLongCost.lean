/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLongFamily

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 

theorem laneB_siteJ_mem_longRects {R : ℝ} {b : ℤ × ℤ}
    (hb : b ∈ laneBBoundaryBlocks (laneBGridRadius R)) (i : Fin 4) :
    S6U.siteJ 0 b i ∈ laneBLongRects R := by
  classical
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr
    ⟨i, Finset.mem_univ _, rfl⟩⟩

 

theorem laneB_siteR_rectLen_eq_mrectLen {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (b : ℤ × ℤ) (i : Fin 4) :
    rectLen ξ f (S6U.siteR b i) =
      ENNReal.ofReal (T20B.mrectLen ξ f 0
        (S6U.siteJ 0 b i).1 (S6U.siteJ 0 b i).2 3 1) := by
  simpa using (S6U.rectLen_siteR (ξ := ξ) hf 0 b i)

 

theorem laneB_siteR_rectLen_le_of_long_family_bound {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {R bnd : ℝ}
    (hfamily : ∀ j ∈ laneBLongRects R,
      T20B.mrectLen ξ f 0 j.1 j.2 3 1 ≤ bnd)
    {b : ℤ × ℤ} (hb : b ∈ laneBBoundaryBlocks (laneBGridRadius R))
    (i : Fin 4) :
    rectLen ξ f (S6U.siteR b i) ≤ ENNReal.ofReal bnd := by
  rw [laneB_siteR_rectLen_eq_mrectLen hf]
  exact ENNReal.ofReal_le_ofReal
    (hfamily _ (laneB_siteJ_mem_longRects hb i))

end SupercriticalLQGUniqueness.B2.DG20Conc
