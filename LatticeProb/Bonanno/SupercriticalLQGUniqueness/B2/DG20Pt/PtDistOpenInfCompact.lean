/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenInfCompact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactExhaustion
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable

 


set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_crossLenIn_eq_iInf_compacts
    (ξ : ℝ) (φ : ℂ → ℝ) (U A B : Set ℂ)
    (J : ℕ → Set ℂ) (hJU : ∀ n, J n ⊆ U)
    (hcover : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ n, K ⊆ J n) :
    crossLenIn ξ φ U A B = ⨅ n, crossLenIn ξ φ (J n) A B := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    apply le_crossLenIn
    intro P hP
    obtain ⟨z, hz, w, hw, hpath, hJ⟩ := hP
    exact crossLenIn_le_lfppLen (U := U)
      ⟨z, hz, w, hw, hpath, fun t ht => hJU n (hJ t ht)⟩
  · rw [crossLenIn_eq_biInf]
    refine le_iInf₂ fun P hP => ?_
    obtain ⟨z, hz, w, hw, hpath, hPU⟩ := hP
    let K : Set ℂ := P '' Icc (0 : ℝ) 1
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hpath.continuousOn
    have hKU : K ⊆ U := by
      rintro x ⟨t, ht, rfl⟩
      exact hPU t ht
    obtain ⟨n, hn⟩ := hcover K hK hKU
    have hPJ : AdmPath (J n) A B P :=
      ⟨z, hz, w, hw, hpath, fun t ht => hn ⟨t, ht, rfl⟩⟩
    exact (iInf_le _ n).trans (crossLenIn_le_lfppLen hPJ)

end SupercriticalLQGUniqueness.B2.DG20Pt
