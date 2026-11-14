/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointCompareBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoundedCompare
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Ratio

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.DFGPS LQGMetric.SupTail LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_compare_on_bounded
    (U : Set ℂ) (hU : Bornology.IsBounded U) :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (ξ : ℝ) (z w : ℂ) (n : ℕ) (s u : ℝ),
        0 < s → s ≤ 1 → 0 ≤ u →
        let r : ℝ := (2 : ℝ) ^ s
        let W' := dg20ScaledNoise r (by positivity : 0 < r) W
        let F := fun y ω =>
          phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω
        let G := fun y ω => phiMN W P 0 n ((r : ℂ) * y) ω
        let C := ENNReal.ofReal (Real.exp (|ξ| * (a + u)))
        P.real {ω | ¬
          (lfppDOn ξ (fun y => F y ω) U z w ≤
              C * lfppDOn ξ (fun y => G y ω) U z w ∧
           lfppDOn ξ (fun y => G y ω) U z w ≤
              C * lfppDOn ξ (fun y => F y ω) U z w)} ≤
          2 * Real.exp (-u ^ 2 / 2) := by
  obtain ⟨x₀, b, hb, hbox, htail⟩ :=
    dg20_non_dyadic_bounded_compare_pos U hU
  let a : ℝ := ferniqueCF * Real.sqrt ((8 * b) * b)
  have ha : 0 ≤ a := by
    dsimp [a]
    have hCF : 0 < ferniqueCF := ferniqueCF_pos
    positivity
  refine ⟨a, ha, ?_⟩
  intro Ω _ P W hW ξ z w n s u hs hs1 hu
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  dsimp only
  let r : ℝ := (2 : ℝ) ^ s
  have hr : 0 < r := by dsimp [r]; positivity
  let W' := dg20ScaledNoise r hr W
  let F : ℂ → Ω → ℝ :=
    fun y ω => phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω
  let G : ℂ → Ω → ℝ :=
    fun y ω => phiMN W P 0 n ((r : ℂ) * y) ω
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * (a + u)))
  change P.real {ω | ¬
      (lfppDOn ξ (fun y => F y ω) U z w ≤
          C * lfppDOn ξ (fun y => G y ω) U z w ∧
       lfppDOn ξ (fun y => G y ω) U z w ≤
          C * lfppDOn ξ (fun y => F y ω) U z w)} ≤ _
  have hsub :
      {ω | ¬
        (lfppDOn ξ (fun y => F y ω) U z w ≤
            C * lfppDOn ξ (fun y => G y ω) U z w ∧
         lfppDOn ξ (fun y => G y ω) U z w ≤
            C * lfppDOn ξ (fun y => F y ω) U z w)} ⊆
      {ω | ∃ y ∈ U, a + u < |F y ω - G y ω|} := by
    intro ω hbad
    by_contra hgood
    have hfield (y : ℂ) (hy : y ∈ U) :
        |F y ω - G y ω| ≤ a + u :=
      le_of_not_gt (fun hgt => hgood ⟨y, hy, hgt⟩)
    apply hbad
    constructor
    · exact lfppDOn_le_of_abs_sub_le hfield z w
    · exact lfppDOn_le_of_abs_sub_le
        (fun y hy => by rw [abs_sub_comm]; exact hfield y hy) z w
  exact (measureReal_mono hsub (measure_ne_top P _)).trans
    (htail P W hW n s u hs hs1 hu)

end SupercriticalLQGUniqueness.B2.DG20Pt
