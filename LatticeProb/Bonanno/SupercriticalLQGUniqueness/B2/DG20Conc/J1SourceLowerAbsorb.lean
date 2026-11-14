/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceLowerAbsorb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRateMono

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_source_lower_two_rate (ξ : ℝ) (Q : PsiParams)
    (CN cN Cg σ : ℝ)
    (hCN : 0 < CN) (hcN : 0 < cN) (hCg : 0 < Cg) (hσ : 0 < σ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ K : ℕ, 2 ≤ K → ∀ B T : ℝ, 0 ≤ B → 0 < T →
        (1 + |ξ| * B)^2 ≤ j1CommonDenominator ξ Q K →
        let s := j1CoarseTailParameter ξ B T
        ENNReal.ofReal ((5 : ℝ)^K) *
          ENNReal.ofReal (CN * Real.exp (-cN * (Real.log s)^2)) +
        ENNReal.ofReal (Cg * 4^K *
          Real.exp (-(Real.log s)^2 / (2 * σ))) ≤
        ENNReal.ofReal ((CN + Cg) * (5 : ℝ)^K *
          Real.exp (-c₀ * (Real.log T)^2 /
            (K : ℝ)^(3 * Q.ε₀))) := by
  let cg := 1 / (2 * σ)
  have hcg : 0 < cg := by dsimp [cg]; positivity
  let d := min cN cg
  have hd : 0 < d := lt_min hcN hcg
  let c₀ := d / (1 + 5 * |ξ|)^2
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀, hc₀, ?_⟩
  intro K hK B T hB hT hD
  dsimp only
  let s := j1CoarseTailParameter ξ B T
  let r := Real.exp (-c₀ * (Real.log T)^2 /
    (K : ℝ)^(3 * Q.ε₀))
  have hf : Real.exp (-cN * (Real.log s)^2) ≤ r := by
    have hh := j1_source_lower_rate_of_le ξ Q K hK B T cN d
      hB hT hcN (min_le_left _ _) hD
    simpa only [c₀, r, s] using hh
  have hg : Real.exp (-(Real.log s)^2 / (2 * σ)) ≤ r := by
    have hh := j1_source_lower_rate_of_le ξ Q K hK B T cg d
      hB hT hcg (min_le_right _ _) hD
    have he : -(Real.log s)^2 / (2 * σ) =
        -cg * (Real.log s)^2 := by dsimp [cg]; ring
    rw [he]
    simpa only [c₀, r, s] using hh
  exact j1_two_rate_absorb K CN Cg
    (Real.exp (-cN * (Real.log s)^2))
    (Real.exp (-(Real.log s)^2 / (2 * σ))) r
    hCN.le hCg.le (Real.exp_pos _).le (Real.exp_pos _).le
    (Real.exp_pos _).le hf hg

end SupercriticalLQGUniqueness.B2.DG20Conc
