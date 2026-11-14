/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundBoxRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundBoxTailSite
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateSqrt

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem around_cfg_box_rate_of_percEstimate
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (j : Fin 4) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ, ∀ T : ℝ, 9 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        let A := Inputs.annulus48 x r (by dsimp [r]; positivity)
        P {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
            ENNReal.ofReal (T * r * lambdaN ξ W P (n - k)) <
          crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
            (Strong.cfgOpens A j) (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j)} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨a₀, a₁, d₀, d₁, ha₀, ha₁, hd₀, hd₁, htail⟩ :=
    around_cfg_box_tail_of_percEstimate hPerc ξ j
  let c₀ : ℝ := d₀ + a₀
  let c₁ : ℝ := min (d₁ * Real.log (Real.log 3)) a₁ / 4
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
      Real.exp_one_lt_three
  have hα : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    exact div_pos (lt_min (mul_pos hd₁ hα) ha₁) (by norm_num)
  refine ⟨c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  have hraw := htail P W hW n k hkn x T hT
  dsimp at hraw ⊢
  have hlog : 0 ≤ Real.log T := (Real.log_nonneg (by linarith : 1 ≤ T))
  have hgauss : d₀ * Real.exp (-d₁ * (Real.log T) ^ 2) ≤
      d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hd₀.le
    apply Real.exp_le_exp.mpr
    rw [Real.log_sqrt (by linarith : 0 ≤ T)]
    nlinarith [sq_nonneg (Real.log T)]
  calc
    _ ≤ ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log T) ^ 2)) +
          ENNReal.ofReal (a₀ * Real.exp
            (-a₁ * (Real.log (Real.sqrt T)) ^ 2 /
              Real.log (Real.log (Real.sqrt T)))) := hraw
    _ ≤ ENNReal.ofReal (d₀ * Real.exp (-d₁ * (Real.log (Real.sqrt T)) ^ 2)) +
          ENNReal.ofReal (a₀ * Real.exp
            (-a₁ * (Real.log (Real.sqrt T)) ^ 2 /
              Real.log (Real.log (Real.sqrt T)))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hgauss) le_rfl
    _ ≤ ENNReal.ofReal (c₀ * Real.exp
          (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
        simpa only [c₀, c₁] using gaussian_loglog_sum_sqrt_bound
          a₀ a₁ d₀ d₁ T ha₀ ha₁ hd₀ hd₁ hT

end SupercriticalLQGUniqueness.B2.DG20Pt
