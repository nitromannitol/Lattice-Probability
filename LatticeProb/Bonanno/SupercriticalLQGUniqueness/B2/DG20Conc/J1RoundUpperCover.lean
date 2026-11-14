/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineAround
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RectLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoverUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRepairedLargeAnnulusGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitLong

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_round_upper_cover
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p) :
    ∃ R₀ G Cpos cPos : ℝ,
      24 ≤ R₀ ∧ 1 ≤ G ∧ 0 < Cpos ∧ 0 < cPos ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hKn : K ≤ n) (R : ℝ) (hR : R₀ ≤ R)
        (c : ℂ) (s : ℝ) (hs : 3 < s),
        P {ω | ENNReal.ofReal ((G * R) *
          (s * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
            ellN ξ W P (n - K) (ENNReal.ofReal p))) <
          (lfppContMetric ξ (fun z => phiMN W P K n
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
            ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
              (show Continuous (fun z : ℂ =>
                (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
            {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
            (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ≤
          ENNReal.ofReal (G * R) * ENNReal.ofReal
            (Cpos * Real.exp
              (-cPos * (Real.log s)^2 / Real.log (Real.log s))) := by
  obtain ⟨Cn, cn, Cp, cp, hCn, hcn, hCp, hcp, ht⟩ := hunit
  obtain ⟨R₀, G, hR₀, hG, hgeom⟩ :=
    laneB_repairedLargeAnnulusGeometry
  refine ⟨R₀, G, Cp, cp, hR₀, hG, hCp, hcp, ?_⟩
  intro Ω _ P W hW K n hKn R hR c s hs
  let Y : ℂ → Ω → ℝ := fun z ω => phiMN W P K n
    (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω
  have hc : Continuous (fun z : ℂ =>
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) := by fun_prop
  have hYc : ∀ ω, Continuous (fun z => Y z ω) :=
    fun ω => ((isPhiVersion_phiMN hW hKn).cont ω).comp hc
  change P {ω | ENNReal.ofReal ((G * R) *
      (s * LambdaN ξ W P (n - K) (ENNReal.ofReal p) *
        ellN ξ W P (n - K) (ENNReal.ofReal p))) <
    (lfppContMetric ξ (fun z => Y z ω) (hYc ω)).aroundDist
      {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
      (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ≤ _
  apply j1_cover_upper_of_rect_tails P Y hYc (hgeom R hR)
  intro u d
  change P {ω | T20B.mrectLen ξ (fun z => Y z ω)
    0 u d 3 1 ∈ Set.Ioi (s * LambdaN ξ W P (n - K)
      (ENNReal.ofReal p) * ellN ξ W P (n - K) (ENNReal.ofReal p))} ≤ _
  dsimp only [Y]
  rw [j1_mrectLen_field_law P W hW hKn ξ 0 u d c 3 1 measurableSet_Ioi]
  simpa only [Set.mem_Ioi] using
    laneA2_unit_long_tail P hW ht (n - K) s hs u d

end SupercriticalLQGUniqueness.B2.DG20Conc
