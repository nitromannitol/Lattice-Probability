/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalPointTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalPointBound
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesInsideTail
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLambdaLower

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistLocalPointBudget {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (ξ : Ioi (0 : ℝ))
    (Q ζ C Clam T : ℝ) (n k₀ : ℕ) (z w : ℂ) (ω : Ω) : ℝ≥0∞ :=
  let b (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (2 * T ^ 2 * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
  let ell (v : ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal
    (C * T ^ 2 * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (k : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k v ω) * lambdaN ξ W P n)
  let a (v : ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
    (b v (k₀ + (j + 1)) + ell v (k₀ + (j + 1)) + b v (k₀ + j))
  let term (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal
    (Clam * T * lambdaN ξ W P n * (2 : ℝ) ^
      (-((ξ : ℝ) * Q - 3 * ζ) * (n : ℝ)) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 n v ω))
  term z + a z + (b z k₀ + ell z k₀ + b w k₀) + a w + term w

theorem pt_dist_local_point_budget_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) (hconv : Convex ℝ V)
    (R : ℝ) (hR : 1 ≤ R) :
    ∃ C Clam c₀ c₁ : ℝ, 0 < C ∧ 0 < Clam ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k₀ : ℕ, k₀ ≤ n →
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
        ∀ T : ℝ, 3 < T →
          P {ω | ¬ lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω) U z w ≤
              ptDistLocalPointBudget P W ξ Q ζ C Clam T n k₀ z w ω} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨_, _, C, c₀, c₁, hC, hc₀, hc₁, htail⟩ :=
    exists_pt_dist_all_scales_inside_tail_of_inputs
      hPerc hExp ξ Q hQ ζ hζ V hV hconv R (by linarith)
  obtain ⟨Clam, hClam, hlam⟩ :=
    pt_dist_lambdaN_lower_of_inputs hExp ξ Q hQ ζ hζ
  refine ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k₀ hk₀ U z w hz hw hzw hcollarZ hcollarW
    hVballZ hVballW hUballZ hUballW T hT
  obtain ⟨F, hcover, hbad⟩ := htail P W hW n T hT
  have hsubset :
      {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
        ptDistLocalPointBudget P W ξ Q ζ C Clam T n k₀ z w ω} ⊆
      (ptDistAllScalesGood P W ξ Q ζ C n F V R T
        (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))))ᶜ := by
    intro ω hnot hgood
    apply hnot
    simpa only [ptDistLocalPointBudget] using
      pt_dist_local_point_field_bound P W hW ξ Q ζ C Clam n k₀ hk₀
        F V U R T hR hT hζ.le hC.le (hClam)
        (hlam P W hW n) ω hgood
        (fun k hk x hx => (hcover k hk).2.1 x hx)
        (fun k hk v hv => (hcover k hk).2.2 v hv)
        z w hz hw hzw hcollarZ hcollarW
        hVballZ hVballW hUballZ hUballW
  exact (measure_mono hsubset).trans hbad

end SupercriticalLQGUniqueness.B2.DG20Pt
