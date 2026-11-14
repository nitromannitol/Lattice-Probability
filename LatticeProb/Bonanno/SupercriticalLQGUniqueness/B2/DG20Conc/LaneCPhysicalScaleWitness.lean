/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleWitness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneC_eventual_physical_scale_witness
    (Q : PsiParams) (hR : Q.r₀ ≤ (1 : ℝ) / 100)
    (hε : Q.ε₀ ≤ (1 : ℝ) / 100) :
    ∃ K₀ : ℕ, ∀ K m n : ℕ, K₀ ≤ K → K ≤ n → m + 1 ≤ K →
      (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ m →
      ∃ s : ℝ,
        (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
          (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
        (2 : ℝ)⁻¹ ^ K + 2 * s ≤ LaneCInputs.sourceRadius K m := by
  obtain ⟨K₁, hK₁⟩ := laneC_eventually_two_le_K_pow Q.ε₀_pos
  refine ⟨max 1 K₁, ?_⟩
  intro K m n hK hKn hmK hmHi
  let s : ℝ := ((K : ℝ) ^ Q.ε₀ / 4) * (2 : ℝ)⁻¹ ^ K
  refine ⟨s, ?_, ?_⟩
  · intro t ht
    exact laneC_sigma_le_quarter_source_scale Q hR hε
      (le_trans (le_max_left 1 K₁) hK)
      (lt_of_lt_of_le (by positivity) ht.1) ht.2
  · have hpow : 0 < (2 : ℝ) ^ K := by positivity
    have hKpow : 2 ≤ (K : ℝ) ^ Q.ε₀ :=
      hK₁ K (le_trans (le_max_right 1 K₁) hK)
    have hbound : 1 + 2 * ((K : ℝ) ^ Q.ε₀ / 4) ≤ (2 : ℝ) ^ m := by
      nlinarith
    rw [laneC_source_radius_eq_ratio (by omega : m ≤ K)]
    dsimp [s]
    rw [inv_pow, inv_eq_one_div]
    calc
      1 / (2 : ℝ) ^ K + 2 * ((K : ℝ) ^ Q.ε₀ / 4 * (1 / (2 : ℝ) ^ K)) =
          (1 + 2 * ((K : ℝ) ^ Q.ε₀ / 4)) / (2 : ℝ) ^ K := by ring
      _ ≤ (2 : ℝ) ^ m / (2 : ℝ) ^ K :=
        (div_le_div_iff_of_pos_right hpow).2 hbound

end SupercriticalLQGUniqueness.B2.DG20Conc
