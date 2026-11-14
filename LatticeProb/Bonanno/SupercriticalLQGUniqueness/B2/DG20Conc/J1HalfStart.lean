/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfStart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceNumeric

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_half_source_parameter_gt_three (ξ : ℝ) (Q : PsiParams) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 2 ≤ K →
      ∀ B T : ℝ, 1 ≤ B → B ≤ 5 * (K : ℝ)^Q.ε₀ →
        (2 : ℝ)^(((1 / 2 : ℝ) *
          (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T →
          3 < j1CoarseTailParameter ξ B T := by
  let ξ' := 2 * |ξ| + 1
  obtain ⟨K₀, hK₀⟩ := j1_eventually_source_log_dominates ξ' Q
  refine ⟨K₀, ?_⟩
  intro K hK hK2 B T hB1 hBmax hT
  have hB : 0 ≤ B := by linarith
  have hξ' : 0 ≤ ξ' := by dsimp [ξ']; positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmain' := hK₀ K hK hK2 B hB hBmax
  have hD : 2 * (1 + |ξ| * B) ≤ 1 + |ξ'| * B := by
    rw [abs_of_nonneg hξ']
    dsimp [ξ']
    nlinarith
  have hmain : (1 + |ξ| * B) * Real.log 3 <
      (1 / 2 : ℝ) *
        ((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) * Real.log 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hD hlog3.le]
  let a := (1 / 2 : ℝ) *
    (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)
  have ha : (0 : ℝ) < (2 : ℝ)^a :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hTpos : 0 < T := ha.trans hT
  have hlogT : a * Real.log 2 < Real.log T := by
    have hh := (Real.log_lt_log_iff ha hTpos).mpr hT
    simpa only [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] using hh
  have hpow : (3 : ℝ)^(1 + |ξ| * B) < T := by
    have hp : (0 : ℝ) < (3 : ℝ)^(1 + |ξ| * B) :=
      Real.rpow_pos_of_pos (by norm_num) _
    apply (Real.log_lt_log_iff hp hTpos).mp
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    exact hmain.trans (by simpa only [a, mul_assoc] using hlogT)
  exact j1_coarse_parameter_gt_three ξ B T hB hpow

theorem j1_half_small_and_round_start (ξ : ℝ) (Q : PsiParams) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 2 ≤ K →
      ∀ T : ℝ,
        (2 : ℝ)^(((1 / 2 : ℝ) *
          (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T →
          3 < j1CoarseTailParameter ξ 5 T ∧
          3 < j1CoarseTailParameter ξ
            ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T := by
  obtain ⟨K₀, hK₀⟩ := j1_half_source_parameter_gt_three ξ Q
  refine ⟨K₀, ?_⟩
  intro K hK hK2 T hT
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hx : 1 ≤ (K : ℝ)^Q.ε₀ :=
    Real.one_le_rpow hKr Q.ε₀_pos.le
  constructor
  · exact hK₀ K hK hK2 5 T (by norm_num) (by linarith) hT
  · have hB := j1_coarse_radius_lt_four_power Q K hK2
    exact hK₀ K hK hK2 _ T
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by linarith) hT

end SupercriticalLQGUniqueness.B2.DG20Conc
