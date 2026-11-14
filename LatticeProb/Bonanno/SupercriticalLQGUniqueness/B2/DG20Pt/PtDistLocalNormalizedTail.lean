/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalNormalizedTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianBudgetBound

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_local_normalized_upper_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) (hconv : Convex ℝ V)
    (R : ℝ) (hR : 1 ≤ R) :
    ∃ C Clam c₀ c₁ : ℝ, 0 < C ∧ 0 < Clam ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k₀ : ℕ, 1 ≤ k₀ → k₀ ≤ n →
        ∀ U : Set ℂ, ∀ z w : ℂ, z ∈ V → w ∈ V →
        dist z w ≤ 2 * ((2 : ℝ)⁻¹ ^ k₀) →
        (∀ k, k₀ ≤ k → ∀ x : ℂ,
          dist z x < ((2 : ℝ)⁻¹) ^ k / 4 →
          ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U) →
        (∀ k, k₀ ≤ k → ∀ x : ℂ,
          dist w x < ((2 : ℝ)⁻¹) ^ k / 4 →
          ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U) →
        closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ V →
        closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ V →
        closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ U →
        closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ U →
        ∀ T L β : ℝ, 3 < T → 0 ≤ L → 0 < β →
        0 < (ξ : ℝ) * Q - 3 * ζ - 2 * β →
          let q := (2 : ℝ) ^
            (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))
          let K := 2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)
          P {ω | ¬ lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω) U z w ≤
              ENNReal.ofReal (K * T ^ 2 * Real.exp L *
                lambdaN ξ W P n * q ^ k₀)} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
          2 * ENNReal.ofReal
            (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
              (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
                (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β)))) := by
  obtain ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, htail⟩ :=
    pt_dist_local_gaussian_budget_tail_of_inputs
      hPerc hExp ξ Q hQ ζ hζ V hV hconv R hR
  refine ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k₀ hk₀ hkn U z w hz hw hzw hcollarZ hcollarW
    hVballZ hVballW hUballZ hUballW T L β hT hL hβ hα
  dsimp
  have hbudget := pt_dist_gaussian_budget_le_uniform
    (ξ : ℝ) Q ζ L β T C Clam (lambdaN ξ W P n) n k₀ hkn
    hα hC.le hClam.le (lambdaN_pos hW n).le
  have hsub :
      {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
        ENNReal.ofReal
          ((2 * Clam + 4 + C +
              6 * (2 + C) /
                (1 - (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β)))) *
            T ^ 2 * Real.exp L * lambdaN ξ W P n *
            ((2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))) ^ k₀)} ⊆
      {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
        ptDistLocalGaussianBudget (ξ : ℝ) Q ζ L β T C Clam
          (lambdaN ξ W P n) n k₀} := by
    intro ω hω hgood
    exact hω (hgood.trans hbudget)
  exact (measure_mono hsub).trans
    (htail P W hW n k₀ hk₀ hkn U z w hz hw hzw hcollarZ hcollarW
      hVballZ hVballW hUballZ hUballW T L β hT hL hβ)

end SupercriticalLQGUniqueness.B2.DG20Pt
