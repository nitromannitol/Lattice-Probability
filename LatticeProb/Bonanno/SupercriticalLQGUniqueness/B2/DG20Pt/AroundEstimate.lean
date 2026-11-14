/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundEstimate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundFailureGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateCompact

 






set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem dg20AroundEstimate_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate') :
    Inputs.DG20AroundEstimate := by
  intro ξ
  obtain ⟨a₀, a₁, ha₀, ha₁, hfour⟩ :=
    around_four_bad_tail_of_percEstimate hPerc ξ
  let c₁ : ℝ := a₁ / 4
  let c₀ : ℝ := (a₀ + 1) * Real.exp
    (c₁ * (Real.log 257) ^ 2 * (1 + (Real.log (Real.log 3))⁻¹))
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hbase := tail_rate_compact_bound a₀ c₁ 257 4 ha₀ hc₁
    (by norm_num) (by norm_num) (by norm_num)
  have hc₀ge : a₀ ≤ c₀ := by
    simpa only [c₀] using hbase.2.1
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  dsimp
  by_cases hlarge : 257 < T
  · let r : ℝ := (2 : ℝ)⁻¹ ^ k
    have hr : 0 < r := by dsimp [r]; positivity
    have hlam : 0 < lambdaN (ξ : ℝ) W P (n - k) := lambdaN_pos hW (n - k)
    have hTlarge : max (9 * (16 : ℝ)) ((16 : ℝ) ^ 2) < T := by
      norm_num
      linarith
    have hS : 9 < T / 16 := by linarith
    let φ : Ω → ℂ → ℝ := fun ω z => phiMN W P 0 n z ω
    let c : Ω → ℝ := fun ω => (ξ : ℝ) * phiMN W P 0 k x ω
    have hsub := around_failure_subset_four_bad (ξ : ℝ) φ c x hr
      (by linarith : 0 < T) hlam
    have hbad := hfour P W hW n k hkn x (T / 16) hS
    dsimp at hbad
    have hbound :
        P {ω | ¬ Inputs.HasAroundLoop (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
          x r hr (ENNReal.ofReal
            (T * r * lambdaN (ξ : ℝ) W P (n - k) *
              Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))} ≤
        ENNReal.ofReal (a₀ * Real.exp
          (-a₁ * (Real.log (T / 16)) ^ 2 /
            Real.log (Real.log (T / 16)))) := by
      exact (measure_mono hsub).trans hbad
    have hrate := gaussian_loglog_rate_div_bound a₁ 16 T ha₁
      (by norm_num) hTlarge
    have hrate' : a₀ * Real.exp
        (-a₁ * (Real.log (T / 16)) ^ 2 /
          Real.log (Real.log (T / 16))) ≤
        c₀ * Real.exp
          (-c₁ * (Real.log T) ^ 2 /
            Real.log (Real.log T)) := by
      calc
        _ ≤ a₀ * Real.exp
            (-(a₁ / 4) * (Real.log T) ^ 2 /
              Real.log (Real.log T)) :=
          mul_le_mul_of_nonneg_left hrate ha₀.le
        _ ≤ c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 /
              Real.log (Real.log T)) := by
          dsimp [c₁]
          exact mul_le_mul_of_nonneg_right hc₀ge (Real.exp_nonneg _)
    exact hbound.trans (ENNReal.ofReal_le_ofReal hrate')
  · have hsmall : T ≤ 257 := le_of_not_gt hlarge
    have hcompact := tail_rate_compact_bound a₀ c₁ 257 T ha₀ hc₁
      (by norm_num) hT hsmall
    have hOne : (1 : ℝ≥0∞) ≤ ENNReal.ofReal
        (c₀ * Real.exp
          (-c₁ * (Real.log T) ^ 2 /
            Real.log (Real.log T))) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by simpa only [c₀] using hcompact.2.2.2)
    have hprob : P {ω | ¬ Inputs.HasAroundLoop (ξ : ℝ)
        (fun z => phiMN W P 0 n z ω) x ((2 : ℝ)⁻¹ ^ k)
        (by positivity)
        (ENNReal.ofReal (T * ((2 : ℝ)⁻¹ ^ k) *
          lambdaN (ξ : ℝ) W P (n - k) *
          Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))} ≤ 1 := by
      calc
        _ ≤ P Set.univ := measure_mono (subset_univ _)
        _ = 1 := by simp
    exact hprob.trans hOne

end SupercriticalLQGUniqueness.B2.DG20Pt
