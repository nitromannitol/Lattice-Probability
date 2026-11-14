/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfNumeric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfLoglog

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_half_numeric_conditions (ξ : ℝ) (Q : PsiParams)
    (hε : Q.ε₀ ≤ 1) (R₀ : ℝ) :
    ∃ K₀ : ℕ, 64 ≤ K₀ ∧
      ∀ K ≥ K₀, ∀ T : ℝ,
        (2 : ℝ)^(((1 / 2 : ℝ) *
          (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T →
          j1SourceRadius Q K ≤ 1 / 4 ∧
          laneBCoarseIndex Q K + 1 ≤ K ∧
          R₀ ≤ (2 : ℝ)^(laneBCoarseIndex Q K) ∧
          (2 : ℝ)^(laneBCoarseIndex Q K) ≤ 2 * (K : ℝ) ∧
          3 < j1CoarseTailParameter ξ 5 T ∧
          3 < j1CoarseTailParameter ξ
            ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T ∧
          1 ≤ Real.log (Real.log T) ∧
          (1 + |ξ| * 5)^2 ≤ j1CommonDenominator ξ Q K ∧
          (1 + |ξ| * (2 : ℝ)^(laneBCoarseIndex Q K + 1))^2 ≤
            j1CommonDenominator ξ Q K := by
  obtain ⟨K₁, hK₁⟩ := j1_half_small_and_round_start ξ Q
  obtain ⟨K₂, hK₂⟩ := j1_half_source_loglog_ge_one Q
  obtain ⟨K₃, hK₃⟩ := j1_round_scale_range Q R₀ hε
  let K₀ := max 64 (max K₁ (max K₂ K₃))
  refine ⟨K₀, le_max_left _ _, ?_⟩
  intro K hK T hT
  have hK64 : 64 ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := by omega
  have hK6 : 6 ≤ K := by omega
  have hK₁' : K₁ ≤ K := (le_max_left _ _).trans
    ((le_max_right 64 (max K₁ (max K₂ K₃))).trans hK)
  have hK₂' : K₂ ≤ K := (le_max_left _ _).trans
    ((le_max_right K₁ (max K₂ K₃)).trans
      ((le_max_right 64 (max K₁ (max K₂ K₃))).trans hK))
  have hK₃' : K₃ ≤ K := (le_max_right _ _).trans
    ((le_max_right K₁ (max K₂ K₃)).trans
      ((le_max_right 64 (max K₁ (max K₂ K₃))).trans hK))
  obtain ⟨hm, hR, hRK⟩ := hK₃ K hK₃' hK64
  obtain ⟨hs, hr⟩ := hK₁ K hK₁' hK2 T hT
  exact ⟨j1_source_radius_le_quarter Q K hε hK6,
    hm, hR, hRK, hs, hr, hK₂ K hK₂' hK2 T hT,
    j1_small_denominator_bound ξ Q K hK2,
    j1_round_denominator_bound ξ Q K hK2⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
