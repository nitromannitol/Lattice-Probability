/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingUpperSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingUpperTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTailParameters

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_upper_tail_small_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (k₀ : ℕ) (M : ℝ), 0 < M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, k₀ ≤ n →
        ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
          P {ω | ¬ lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω)
            ((fun x : ℂ => (r : ℂ) * x) '' U)
            ((r : ℂ) * z) ((r : ℂ) * w) ≤
              ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
            ENNReal.ofReal ε := by
  obtain ⟨ζ, β, hζ, hβ, hα⟩ := pt_dist_positive_exponent_split hPos ξ Q hQ
  obtain ⟨k₀, N, C, Clam, c₀, c₁, hk₀, hC, hClam, hc₀, hc₁, htail⟩ :=
    pt_dist_moving_upper_tail_of_inputs hPerc hExp ξ Q hQ ζ hζ U hU hUc z w hz hw
  let α : ℝ := (ξ : ℝ) * Q - 3 * ζ - 2 * β
  let q : ℝ := (2 : ℝ) ^ (-α)
  let Kc : ℝ := 2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)
  let a : ℝ := β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)
  let qG : ℝ := Real.exp (-a * β)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by dsimp [α] at hα ⊢; linarith)
  have hKc : 0 < Kc := by dsimp [Kc]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hξ : 0 < (ξ : ℝ) := ξ.2
  have ha : 0 < a := by dsimp [a]; positivity
  have hqG0 : 0 < qG := by dsimp [qG]; positivity
  have hqG1 : qG < 1 := by
    dsimp [qG]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos ha hβ])
  obtain ⟨T, L, hT, hL, hsmall⟩ :=
    pt_dist_finite_chain_tail_parameters N c₀ c₁ a qG ε
      hc₀ hc₁ ha hqG0 hqG1 hε
  let M : ℝ := ((N : ℝ) + 1) * Kc * T ^ 2 * Real.exp L * q ^ k₀
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨k₀, M, hM, ?_⟩
  intro Ω _ P _ W hW n hkn r hr1 hr2
  have htail' := htail P W hW n hkn r hr1 hr2 T L β hT hL hβ hα
  dsimp [a, qG] at hsmall
  dsimp [q, Kc, α] at htail'
  have hbound := htail'.trans hsmall
  have hmcast : (N + 1 : ℝ≥0∞) = ENNReal.ofReal ((N : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg N) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hcost :
      (N + 1 : ℝ≥0∞) * ENNReal.ofReal
        ((2 * Clam + 4 + C + 6 * (2 + C) /
            (1 - (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β)))) *
          T ^ 2 * Real.exp L * lambdaN ξ W P n *
          ((2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))) ^ k₀) =
        ENNReal.ofReal (M * lambdaN ξ W P n) := by
    rw [hmcast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) + 1)]
    congr 1
    dsimp [M, Kc, q, α]
    ring
  simpa only [hcost] using hbound

end SupercriticalLQGUniqueness.B2.DG20Pt
