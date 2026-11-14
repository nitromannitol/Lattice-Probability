/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTailParameters at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistExponentSplit

 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_finite_chain_tail_parameters
    (N : ℕ) (c₀ c₁ a q ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (ha : 0 < a) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 < ε) :
    ∃ T L : ℝ, 3 < T ∧ 0 ≤ L ∧
      (N + 1 : ℝ≥0∞) *
        (ENNReal.ofReal (c₀ * Real.exp
          (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
         2 * ENNReal.ofReal
           (2 * Real.exp (-a * L) * (q / (1 - q)))) ≤
      ENNReal.ofReal ε := by
  let d : ℝ := ε / (2 * ((N : ℝ) + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  let Cg : ℝ := 4 * q / (1 - q)
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  obtain ⟨T, hT, hcross⟩ := pt_dist_loglog_tail_small c₀ c₁ d hc₀ hc₁ hd
  obtain ⟨L, hL, hfield⟩ := pt_dist_exponential_tail_small Cg a d hCg ha hd
  refine ⟨T, L, hT, hL, ?_⟩
  have hgeq :
      2 * ENNReal.ofReal (2 * Real.exp (-a * L) * (q / (1 - q))) =
        ENNReal.ofReal (Cg * Real.exp (-a * L)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    dsimp [Cg]
    ring
  rw [hgeq]
  have hcNonneg : 0 ≤ c₀ * Real.exp
      (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) := by positivity
  have hgNonneg : 0 ≤ Cg * Real.exp (-a * L) := by positivity
  rw [← ENNReal.ofReal_add hcNonneg hgNonneg]
  have hmcast : (N + 1 : ℝ≥0∞) = ENNReal.ofReal ((N : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg N) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [hmcast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) + 1)]
  apply ENNReal.ofReal_le_ofReal
  have hsum : c₀ * Real.exp
      (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)) +
      Cg * Real.exp (-a * L) ≤ 2 * d := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (N : ℝ) + 1 by positivity)
  have hdeq : ((N : ℝ) + 1) * (2 * d) = ε := by
    dsimp [d]
    field_simp
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Pt
