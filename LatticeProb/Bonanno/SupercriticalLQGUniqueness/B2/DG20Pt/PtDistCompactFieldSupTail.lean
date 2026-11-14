/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactFieldSupTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingUpperSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRealTail
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_compact_phiMN_sup_tail_small
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (n : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧
      P {ω | ∃ x ∈ K, L < |phiMN W P 0 n x ω|} ≤
        ENNReal.ofReal ε := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  let F : C(ℂ, ℝ) → ℝ := fun f =>
    sSup ((fun x : ℂ => |f x|) '' K)
  have hFc : Continuous F := by
    exact hK.continuous_sSup (by fun_prop)
  let φ : Ω → C(ℂ, ℝ) := pathC (phiMN W P 0 n) hφ.cont
  have hφm : Measurable φ := measurable_pathC hφ.cont hφ.meas
  obtain ⟨L, hL, htail⟩ :=
    pt_dist_measurable_real_upper_tail_small P (fun ω => F (φ ω))
      (hFc.measurable.comp hφm) ε hε
  refine ⟨L, hL, ?_⟩
  have hsub :
      {ω | ∃ x ∈ K, L < |phiMN W P 0 n x ω|} ⊆
      {ω | L < F (φ ω)} := by
    rintro ω ⟨x, hx, hbad⟩
    have hbound : BddAbove ((fun y : ℂ => |phiMN W P 0 n y ω|) '' K) :=
      hK.bddAbove_image
        ((continuous_abs.comp (hφ.cont ω)).continuousOn)
    have hxle : |phiMN W P 0 n x ω| ≤ F (φ ω) := by
      exact le_csSup hbound (mem_image_of_mem _ hx)
    exact hbad.trans_le hxle
  exact (measure_mono hsub).trans htail

end SupercriticalLQGUniqueness.B2.DG20Pt
