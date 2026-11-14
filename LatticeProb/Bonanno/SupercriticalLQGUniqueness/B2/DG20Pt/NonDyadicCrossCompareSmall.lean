/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicCrossCompareSmall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoundedCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCrossingComparison

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_cross_compare_small
    (K : Set ℂ) (hK : Bornology.IsBounded K)
    (ξ : Ioi (0 : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (U A B : Set ℂ) (hUK : U ⊆ K)
        (n : ℕ) (s : ℝ), 0 < s → s ≤ 1 →
        let r : ℝ := (2 : ℝ) ^ s
        let W' := dg20ScaledNoise r (by positivity : 0 < r) W
        let F := fun y ω =>
          phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω
        let G := fun y ω => phiMN W P 0 n ((r : ℂ) * y) ω
        let C := ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * a))
        P {ω | ¬
          (crossLenIn (ξ : ℝ) (fun y => F y ω) U A B ≤
              C * crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ∧
           crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ≤
              C * crossLenIn (ξ : ℝ) (fun y => F y ω) U A B)} ≤
          ENNReal.ofReal ε := by
  obtain ⟨x₀, b, hb, hbox, htail⟩ :=
    dg20_non_dyadic_bounded_compare_pos K hK
  let a₀ : ℝ := ferniqueCF * Real.sqrt ((8 * b) * b)
  let m : ℝ := max 0 (Real.log (2 / ε))
  let u : ℝ := Real.sqrt (2 * m)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * m :=
    Real.sq_sqrt (by dsimp [m]; positivity)
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
  have ha : 0 ≤ a := by
    dsimp [a, a₀]
    have hCF : 0 < ferniqueCF := ferniqueCF_pos
    positivity
  refine ⟨a, ha, ?_⟩
  intro Ω _ P W hW U A B hUK n s hs hs1
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let r : ℝ := (2 : ℝ) ^ s
  let W' := dg20ScaledNoise r (by positivity : 0 < r) W
  let F : ℂ → Ω → ℝ := fun y ω =>
    phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω
  let G : ℂ → Ω → ℝ := fun y ω =>
    phiMN W P 0 n ((r : ℂ) * y) ω
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * a))
  change P {ω | ¬
    (crossLenIn (ξ : ℝ) (fun y => F y ω) U A B ≤
      C * crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ∧
     crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ≤
      C * crossLenIn (ξ : ℝ) (fun y => F y ω) U A B)} ≤
    ENNReal.ofReal ε
  have hsub :
      {ω | ¬
        (crossLenIn (ξ : ℝ) (fun y => F y ω) U A B ≤
          C * crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ∧
         crossLenIn (ξ : ℝ) (fun y => G y ω) U A B ≤
          C * crossLenIn (ξ : ℝ) (fun y => F y ω) U A B)} ⊆
      {ω | ∃ y ∈ K, a < |F y ω - G y ω|} := by
    intro ω hbad
    exact dg20_heat_phi_crossLen_bad_subset_sup_bad
      (ξ : ℝ) F G K U A B a hUK hbad
  have hraw := htail P W hW n s u hs hs1 hu0
  rw [← ofReal_measureReal (measure_ne_top P _)]
  have hmeasure := (measureReal_mono hsub (measure_ne_top P _)).trans hraw
  exact (ENNReal.ofReal_le_ofReal hmeasure).trans
    (ENNReal.ofReal_le_ofReal hsmall)

end SupercriticalLQGUniqueness.B2.DG20Pt
