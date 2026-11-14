/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundScaleRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceStart
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseIndexRange

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_eventually_coarse_radius_ge (Q : PsiParams) (R₀ : ℝ) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, R₀ ≤ (K : ℝ)^Q.ε₀ := by
  have ht : Tendsto (fun K : ℕ => (K : ℝ)^Q.ε₀) atTop atTop :=
    (tendsto_rpow_atTop Q.ε₀_pos).comp tendsto_natCast_atTop_atTop
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (ht.eventually_ge_atTop R₀)
  exact ⟨K₀, hK₀⟩

theorem j1_round_scale_range (Q : PsiParams) (R₀ : ℝ)
    (hε : Q.ε₀ ≤ 1) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 64 ≤ K →
      let m := laneBCoarseIndex Q K
      m + 1 ≤ K ∧ R₀ ≤ (2 : ℝ)^m ∧
        (2 : ℝ)^m ≤ 2 * (K : ℝ) := by
  obtain ⟨K₀, hK₀⟩ := j1_eventually_coarse_radius_ge Q R₀
  refine ⟨K₀, ?_⟩
  intro K hK hK64
  dsimp only
  have hK2 : 2 ≤ K := by omega
  have hm := laneB_coarseIndex_add_one_le Q K hε hK2
  have hrad := (laneB_coarseIndex_radius Q K hK2).2
  have hbound := j1_coarse_radius_lt_four_power Q K hK2
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hpow : (K : ℝ)^Q.ε₀ ≤ K :=
    Real.rpow_le_self_of_one_le hKr hε
  have hrad' : R₀ ≤ (2 : ℝ)^(laneBCoarseIndex Q K) := by
    have hh := (hK₀ K hK).trans hrad
    simpa only [Real.rpow_natCast] using hh
  have hpow2 : (2 : ℝ)^(laneBCoarseIndex Q K + 1) =
      2 * (2 : ℝ)^(laneBCoarseIndex Q K) := by
    rw [pow_succ]
    ring
  rw [hpow2] at hbound
  exact ⟨hm, hrad', by linarith⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
