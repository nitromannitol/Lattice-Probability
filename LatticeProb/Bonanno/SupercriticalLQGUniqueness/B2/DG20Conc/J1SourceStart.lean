/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceStart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CommonDenominator
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseStart
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_eventually_large_power (Q : PsiParams) (A : ℝ) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀,
      A < (K : ℝ)^((1 / 2 : ℝ) + 2 * Q.ε₀) := by
  have he : 0 < (1 / 2 : ℝ) + 2 * Q.ε₀ := by linarith [Q.ε₀_pos]
  have ht : Tendsto
      (fun K : ℕ => (K : ℝ)^((1 / 2 : ℝ) + 2 * Q.ε₀))
      atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (ht.eventually_gt_atTop A)
  exact ⟨K₀, hK₀⟩

theorem j1_eventually_source_log_dominates (ξ : ℝ) (Q : PsiParams) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 2 ≤ K →
      ∀ B : ℝ, 0 ≤ B → B ≤ 5 * (K : ℝ)^Q.ε₀ →
        (1 + |ξ| * B) * Real.log 3 <
          (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨K₀, hK₀⟩ := j1_eventually_large_power Q
    ((1 + 5 * |ξ|) * Real.log 3 / Real.log 2)
  refine ⟨K₀, ?_⟩
  intro K hK hK2 B hB hBmax
  let x := (K : ℝ)^Q.ε₀
  let y := (K : ℝ)^((1 / 2 : ℝ) + 2 * Q.ε₀)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hx : 1 ≤ x := Real.one_le_rpow hKr Q.ε₀_pos.le
  have hx0 : 0 < x := by linarith
  have hA : 1 + |ξ| * B ≤ (1 + 5 * |ξ|) * x := by
    have hgap : 0 ≤ 5 * x - B := by linarith
    nlinarith [mul_nonneg (abs_nonneg ξ) hgap]
  have hyl : (1 + 5 * |ξ|) * Real.log 3 < y * Real.log 2 := by
    have hy := mul_lt_mul_of_pos_right (hK₀ K hK) hl2
    have he : ((1 + 5 * |ξ|) * Real.log 3 / Real.log 2) *
        Real.log 2 = (1 + 5 * |ξ|) * Real.log 3 := by
      field_simp [ne_of_gt hl2]
    linarith
  have hxy : x * y = (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) := by
    dsimp [x, y]
    rw [← Real.rpow_add (by linarith [hKr])]
    congr 1
    ring
  have hmul := mul_lt_mul_of_pos_left hyl hx0
  have hleft := mul_le_mul_of_nonneg_right hA hl3.le
  nlinarith [hmul, hleft]

theorem j1_eventually_source_parameter_gt_three (ξ : ℝ)
    (Q : PsiParams) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 2 ≤ K →
      ∀ B T : ℝ, 0 ≤ B → B ≤ 5 * (K : ℝ)^Q.ε₀ →
        (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T →
          3 < j1CoarseTailParameter ξ B T := by
  obtain ⟨K₀, hK₀⟩ := j1_eventually_source_log_dominates ξ Q
  refine ⟨K₀, ?_⟩
  intro K hK hK2 B T hB hBmax hT
  let a := (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)
  have ha : (0 : ℝ) < (2 : ℝ)^a := Real.rpow_pos_of_pos (by norm_num) _
  have hTpos : 0 < T := ha.trans hT
  have hlogT : a * Real.log 2 < Real.log T := by
    have hh := (Real.log_lt_log_iff ha hTpos).mpr hT
    simpa only [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] using hh
  have hmain : (1 + |ξ| * B) * Real.log 3 < Real.log T :=
    (hK₀ K hK hK2 B hB hBmax).trans hlogT
  have hpow : 3 ^ (1 + |ξ| * B) < T := by
    have hp : (0 : ℝ) < 3 ^ (1 + |ξ| * B) :=
      Real.rpow_pos_of_pos (by norm_num) _
    apply (Real.log_lt_log_iff hp hTpos).mp
    simpa only [Real.log_rpow (by norm_num : (0 : ℝ) < 3)] using hmain
  exact j1_coarse_parameter_gt_three ξ B T hB hpow

theorem j1_source_small_and_round_start (ξ : ℝ) (Q : PsiParams) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 2 ≤ K →
      ∀ T : ℝ,
        (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T →
          3 < j1CoarseTailParameter ξ 5 T ∧
          3 < j1CoarseTailParameter ξ
            ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T := by
  obtain ⟨K₀, hK₀⟩ := j1_eventually_source_parameter_gt_three ξ Q
  refine ⟨K₀, ?_⟩
  intro K hK hK2 T hT
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hx : 1 ≤ (K : ℝ)^Q.ε₀ :=
    Real.one_le_rpow hKr Q.ε₀_pos.le
  constructor
  · exact hK₀ K hK hK2 5 T (by norm_num) (by linarith) hT
  · have hB := j1_coarse_radius_lt_four_power Q K hK2
    exact hK₀ K hK hK2 _ T (by positivity) (by linarith) hT

end SupercriticalLQGUniqueness.B2.DG20Conc
