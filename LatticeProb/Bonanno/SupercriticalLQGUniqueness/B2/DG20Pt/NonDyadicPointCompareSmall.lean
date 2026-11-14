/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointCompareSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointCompareBox

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_compare_small
    (U : Set ℂ) (hU : Bornology.IsBounded U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (ξ : ℝ) (z w : ℂ) (n : ℕ) (s : ℝ),
        0 < s → s ≤ 1 →
        let r : ℝ := (2 : ℝ) ^ s
        let W' := dg20ScaledNoise r (by positivity : 0 < r) W
        let F := fun y ω =>
          phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω
        let G := fun y ω => phiMN W P 0 n ((r : ℂ) * y) ω
        let C := ENNReal.ofReal (Real.exp (|ξ| * a))
        P {ω | ¬
          (lfppDOn ξ (fun y => F y ω) U z w ≤
              C * lfppDOn ξ (fun y => G y ω) U z w ∧
           lfppDOn ξ (fun y => G y ω) U z w ≤
              C * lfppDOn ξ (fun y => F y ω) U z w)} ≤
          ENNReal.ofReal ε := by
  obtain ⟨a₀, ha₀, htail⟩ := dg20_non_dyadic_point_compare_on_bounded U hU
  let m : ℝ := max 0 (Real.log (2 / ε))
  let u : ℝ := Real.sqrt (2 * m)
  have hm0 : 0 ≤ m := le_max_left _ _
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * m := Real.sq_sqrt (by positivity)
  have hsmall : 2 * Real.exp (-u ^ 2 / 2) ≤ ε := by
    rw [hu2, show -(2 * m) / 2 = -m by ring]
    have hE : Real.exp (-m) ≤ ε / 2 := by
      calc Real.exp (-m) ≤ Real.exp (-Real.log (2 / ε)) :=
          Real.exp_le_exp.mpr (by
            dsimp [m]
            linarith [le_max_right 0 (Real.log (2 / ε))])
        _ = ε / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    linarith
  let a : ℝ := a₀ + u
  have ha : 0 ≤ a := add_nonneg ha₀ hu0
  refine ⟨a, ha, ?_⟩
  intro Ω _ P W hW ξ z w n s hs hs1
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have h := htail P W hW ξ z w n s u hs hs1 hu0
  dsimp only [a] at h ⊢
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_le_ofReal hsmall)

end SupercriticalLQGUniqueness.B2.DG20Pt
