/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.ConnectedDomain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3T15
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Tail

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 



theorem exists_admPath_of_open_connected {U A B : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAU : A ⊆ U) (hBU : B ⊆ U) :
    ∃ q : ℝ → ℂ, AdmPath U A B q := by
  obtain ⟨z, hz⟩ := hA
  obtain ⟨w, hw⟩ := hB
  obtain ⟨q, hq⟩ := LQGMetric.DG.t15_exists_isDGPath hU hUc (hAU hz) (hBU hw)
  refine ⟨q, z, hz, w, hw, ?_, ?_⟩
  · exact ⟨hq.source, hq.target, hq.continuousOn, hq.piecewise_contDiff⟩
  · exact fun t ht => hq.mapsTo ht

 



theorem exists_uniform_tube_of_admPath {U A B : Set ℂ}
    (hU : IsOpen U) {q : ℝ → ℂ} (hq : AdmPath U A B q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      Metric.closedBall (q t) δ ⊆ U := by
  rcases hq with ⟨z, hz, w, hw, hqp, hqU⟩
  have hK : IsCompact (q '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hqp.continuousOn
  have hKU : q '' Icc (0 : ℝ) 1 ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hqU t ht
  obtain ⟨δ, hδ, htube⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hmem : q t ∈ q '' Icc (0 : ℝ) 1 := ⟨t, ht, rfl⟩
  exact (Metric.closedBall_subset_cthickening hmem δ).trans htube

 

end SupercriticalLQGUniqueness.B2.DG20Conc
