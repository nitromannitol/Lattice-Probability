/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingUpperTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingBuffer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainProb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalNormalizedTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_upper_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) :
    ∃ (k₀ N : ℕ) (C Clam c₀ c₁ : ℝ),
      1 ≤ k₀ ∧ 0 < C ∧ 0 < Clam ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, k₀ ≤ n →
        ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
        ∀ T L β : ℝ, 3 < T → 0 ≤ L → 0 < β →
        0 < (ξ : ℝ) * Q - 3 * ζ - 2 * β →
          let q := (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))
          let Kc := 2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)
          P {ω | ¬ lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω)
            ((fun x : ℂ => (r : ℂ) * x) '' U)
            ((r : ℂ) * z) ((r : ℂ) * w) ≤
              (N + 1 : ℝ≥0∞) * ENNReal.ofReal
                (Kc * T ^ 2 * Real.exp L * lambdaN ξ W P n * q ^ k₀)} ≤
          (N + 1 : ℝ≥0∞) *
            (ENNReal.ofReal (c₀ * Real.exp
              (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
            2 * ENNReal.ofReal
              (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
                (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
                  (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β))))) := by
  obtain ⟨K, hK, hKU, k₀, hk₀, hcollar, N, p, hp0, hpN, hpK, hpstep⟩ :=
    pt_dist_moving_chain hU hUc hz hw
  obtain ⟨V, hV, hconv, hbuffer⟩ := pt_dist_moving_buffer hK
  obtain ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, htail⟩ :=
    pt_dist_local_normalized_upper_tail_of_inputs
      hPerc hExp ξ Q hQ ζ hζ V hV hconv 1 (le_refl _)
  refine ⟨k₀, N, C, Clam, c₀, c₁, hk₀, hC, hClam, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n hkn r hr1 hr2 T L β hT hL hβ hα
  dsimp
  let Ur : Set ℂ := (fun x : ℂ => (r : ℂ) * x) '' U
  let pr : ℕ → ℂ := fun j => (r : ℂ) * p j
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hrn : ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have htermV (j : ℕ) (hj : j ≤ N + 1) :
      closedBall (pr j) (((2 : ℝ)⁻¹) ^ n) ⊆ V :=
    hbuffer r hr1 hr2 (p j) (hpK j hj) _
      (by positivity) hrn
  have htermU (j : ℕ) (hj : j ≤ N + 1) :
      closedBall (pr j) (((2 : ℝ)⁻¹) ^ n) ⊆ Ur := by
    have hball : ball (pr j) (17 * ((2 : ℝ)⁻¹) ^ n) ⊆ Ur :=
      pt_dist_scaled_collar U K n (hcollar n hkn)
        r hr1 (p j) (hpK j hj) (pr j)
        (by simp only [pr, dist_self]; positivity)
    intro y hy
    apply hball
    rw [mem_ball]
    have h := mem_closedBall.mp hy
    have hp : 0 < ((2 : ℝ)⁻¹) ^ n := by positivity
    linarith
  have hcollarR (j : ℕ) (hj : j ≤ N + 1) (k : ℕ) (hk : k₀ ≤ k)
      (x : ℂ) (hx : dist (pr j) x < ((2 : ℝ)⁻¹) ^ k / 4) :
      ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆ Ur :=
    pt_dist_scaled_collar U K k (hcollar k hk) r hr1
      (p j) (hpK j hj) x hx
  let A : ℝ≥0∞ := ENNReal.ofReal
    ((2 * Clam + 4 + C + 6 * (2 + C) /
        (1 - (2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β)))) *
      T ^ 2 * Real.exp L * lambdaN ξ W P n *
      ((2 : ℝ) ^ (-((ξ : ℝ) * Q - 3 * ζ - 2 * β))) ^ k₀)
  let b : ℝ≥0∞ := ENNReal.ofReal
      (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
      2 * ENNReal.ofReal
        (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
          (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
            (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β))))
  have hedge (j : ℕ) (hj : j ≤ N) :
      P {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
          Ur (pr j) (pr (j + 1)) ≤ A} ≤ b := by
    have hj₁ : j ≤ N + 1 := by omega
    have hj₂ : j + 1 ≤ N + 1 := by omega
    have hjV : pr j ∈ V := htermV j hj₁
      (by simp only [mem_closedBall, dist_self]; positivity)
    have hjV' : pr (j + 1) ∈ V := htermV (j + 1) hj₂
      (by simp only [mem_closedBall, dist_self]; positivity)
    exact htail P W hW n k₀ hk₀ hkn Ur (pr j) (pr (j + 1))
      hjV hjV' (hpstep r hr1 hr2 j hj).le
      (hcollarR j hj₁) (hcollarR (j + 1) hj₂)
      (htermV j hj₁) (htermV (j + 1) hj₂)
      (htermU j hj₁) (htermU (j + 1) hj₂)
      T L β hT hL hβ hα
  have hchain := pt_dist_chain_failure_measure_le P (ξ : ℝ)
    (fun ω y => phiMN W P 0 n y ω) Ur pr N A b hedge
  simpa only [pr, hp0, hpN, Ur, A, b] using hchain

end SupercriticalLQGUniqueness.B2.DG20Pt
