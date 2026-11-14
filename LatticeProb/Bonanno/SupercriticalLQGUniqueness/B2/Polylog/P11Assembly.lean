/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P11Assembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P11Extend
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P8RatioUniform
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.PfeToDG
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Limit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatSection4Iface
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLB

 


















set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.Polylog

 

theorem pl_c_r_of_ratioUniform (hRU : PLRatioUniform) (hS4 : Iface.DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q) {D : LQGMetric.DistC → LSCMetric}
    {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)} (hD : Iface.IsPfeWeakMetric ξ D c)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Ioi (0 : ℝ),
      C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) ≤ c r ∧ (c r : ℝ) ≤ C * (r : ℝ) ^ ((ξ : ℝ) * Q) := by
  obtain ⟨k, hk, hdy⟩ := pl_dyadic_rate_of_ratioUniform hRU hS4 ξ Q hQ hD m hm
  obtain ⟨K, hK, hsub⟩ := pl_submult_of_ratioUniform hRU ξ Q hQ hD m hm
  obtain ⟨Λ, hΛ, hrat⟩ := hD.2.2.2.2.2.1
  exact normalizer_comparable_of_dyadic hΛ hrat hk hdy hK hsub

 
theorem plThm19Limit_of_heatAnnulusTight_of_compareSubset (hP2 : PLHeatAnnulusTight) (hP6 : PLCompareSubset)
    (hS4 : Iface.DG20Section4) : Iface.PLThm19Limit := by
  intro ξ Q hQ m hm _ε _hε D _hDsub c hD
  have hcomp := pl_c_r_of_ratioUniform (pl_ratio_uniform_of_inputs hP2 hP6 hS4) hS4 ξ Q hQ hD m hm
  exact ⟨hcomp, isWeakLQGMetric_of_pfe_of_normalizer_comparable ξ Q D c hD hcomp⟩

 
theorem iface_plThm19Limit_of_inputs (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive)
    (hP6 : PLCompareSubset) : Iface.PLThm19Limit :=
  have hS4 := DG20Pt.dg20Section4_of_inputs hPerc hExp hPos
  plThm19Limit_of_heatAnnulusTight_of_compareSubset (plHeatAnnulusTight_of_inputs hPerc hS4) hP6 hS4

 


theorem iface_plThm19_of_inputs (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive)
    (hP6 : PLCompareSubset)
    (hNorm : LFPPNormalizerExists) :
    Iface.PLThm19 := by
  intro ξ Q hQ D c hD
  have hS4 := DG20Pt.dg20Section4_of_inputs hPerc hExp hPos
  choose m hm using hNorm ξ
  have hcomp := pl_c_r_of_ratioUniform
    (pl_ratio_uniform_of_inputs (plHeatAnnulusTight_of_inputs hPerc hS4) hP6 hS4) hS4 ξ Q hQ hD m hm
  exact ⟨hcomp, isWeakLQGMetric_of_pfe_of_normalizer_comparable ξ Q D c hD hcomp⟩

end SupercriticalLQGUniqueness.B2.Polylog
