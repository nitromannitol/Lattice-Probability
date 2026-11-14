/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceUpperAbsorb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1GaussianUpperRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_source_upper_two_rate (ξ : ℝ) (Q : PsiParams)
    (CP cP Cg σ : ℝ)
    (hCP : 0 < CP) (hcP : 0 < cP) (hCg : 0 < Cg) (hσ : 0 < σ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ K : ℕ, 2 ≤ K → ∀ B T : ℝ, 0 ≤ B → 0 < T →
        (1 + |ξ| * B)^2 ≤ j1CommonDenominator ξ Q K →
        3 < j1CoarseTailParameter ξ B T →
        1 ≤ Real.log (Real.log T) →
        let s := j1CoarseTailParameter ξ B T
        ENNReal.ofReal ((5 : ℝ)^K) *
          ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log s)^2 / Real.log (Real.log s))) +
        ENNReal.ofReal (Cg * 4^K *
          Real.exp (-(Real.log s)^2 / (2 * σ))) ≤
        ENNReal.ofReal ((CP + Cg) * (5 : ℝ)^K *
          Real.exp (-c₀ * (Real.log T)^2 /
            ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by
  let cg := 1 / (2 * σ)
  have hcg : 0 < cg := by dsimp [cg]; positivity
  let d := min cP cg
  have hd : 0 < d := lt_min hcP hcg
  let c₀ := d / (1 + 5 * |ξ|)^2
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀, hc₀, ?_⟩
  intro K hK B T hB hT hD hs hll
  dsimp only
  let s := j1CoarseTailParameter ξ B T
  let r := Real.exp (-c₀ * (Real.log T)^2 /
    ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))
  have hf : Real.exp (-cP * (Real.log s)^2 /
      Real.log (Real.log s)) ≤ r := by
    have hh := j1_source_upper_rate_of_le ξ Q K hK B T cP d
      hB hT hcP (min_le_left _ _) hD hs (by linarith)
    simpa only [c₀, r, s] using hh
  have hg : Real.exp (-(Real.log s)^2 / (2 * σ)) ≤ r := by
    have hh := j1_gaussian_to_source_upper_rate ξ Q K hK B T cg d
      hB hT hcg hd (min_le_right _ _) hD hll
    have he : -(Real.log s)^2 / (2 * σ) =
        -cg * (Real.log s)^2 := by dsimp [cg]; ring
    rw [he]
    simpa only [c₀, r, s] using hh
  exact j1_two_rate_absorb K CP Cg
    (Real.exp (-cP * (Real.log s)^2 / Real.log (Real.log s)))
    (Real.exp (-(Real.log s)^2 / (2 * σ))) r
    hCP.le hCg.le (Real.exp_pos _).le (Real.exp_pos _).le
    (Real.exp_pos _).le hf hg

end SupercriticalLQGUniqueness.B2.DG20Conc
