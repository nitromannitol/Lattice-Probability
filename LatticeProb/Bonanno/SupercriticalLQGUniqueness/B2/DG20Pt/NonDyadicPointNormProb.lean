/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointNormProb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointCompareSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointNormCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointScale

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_non_dyadic_point_norm_compare_small
    (U : Set ℂ) (hU : Bornology.IsBounded U)
    (ξ : Ioi (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (z w : ℂ) (n : ℕ) (s : ℝ),
        0 < s → s ≤ 1 →
        let r : ℝ := (2 : ℝ) ^ s
        let W' := dg20ScaledNoise r (by positivity : 0 < r) W
        let lam := lambdaN ξ W P n
        let F := fun ω => lfppDOn (ξ : ℝ)
          (fun y => phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω)
          U z w
        let D := fun ω => lfppDOn (ξ : ℝ)
          (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w)
        P {ω | ¬
          (ENNReal.ofReal lam⁻¹ * F ω ≤
            ENNReal.ofReal A * (ENNReal.ofReal lam⁻¹ * D ω) ∧
           ENNReal.ofReal lam⁻¹ * D ω ≤
            ENNReal.ofReal A * (ENNReal.ofReal lam⁻¹ * F ω))} ≤
          ENNReal.ofReal ε := by
  obtain ⟨a, ha, hcomp⟩ :=
    dg20_non_dyadic_point_compare_small U hU ε hε
  let A : ℝ := 2 * Real.exp (|(ξ : ℝ)| * a)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro Ω _ P W hW z w n s hs hs1
  dsimp only
  let r : ℝ := (2 : ℝ) ^ s
  have hr1 : 1 ≤ r := by
    dsimp [r]
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs.le)
  have hr2 : r ≤ 2 := by
    dsimp [r]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  let W' := dg20ScaledNoise r hr W
  let lam : ℝ := lambdaN ξ W P n
  have hlam : 0 < lam := lambdaN_pos hW n
  let F : Ω → ℝ≥0∞ := fun ω => lfppDOn (ξ : ℝ)
    (fun y => phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 y ω) U z w
  let G : Ω → ℝ≥0∞ := fun ω => lfppDOn (ξ : ℝ)
    (fun y => phiMN W P 0 n ((r : ℂ) * y) ω) U z w
  let D : Ω → ℝ≥0∞ := fun ω => lfppDOn (ξ : ℝ)
    (fun y => phiMN W P 0 n y ω)
    ((fun x : ℂ => (r : ℂ) * x) '' U)
    ((r : ℂ) * z) ((r : ℂ) * w)
  have hraw := hcomp P W hW (ξ : ℝ) z w n s hs hs1
  have hsub :
      {ω | ¬
        (ENNReal.ofReal lam⁻¹ * F ω ≤
          ENNReal.ofReal A * (ENNReal.ofReal lam⁻¹ * D ω) ∧
         ENNReal.ofReal lam⁻¹ * D ω ≤
          ENNReal.ofReal A * (ENNReal.ofReal lam⁻¹ * F ω))} ⊆
      {ω | ¬
        (F ω ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * a)) * G ω ∧
         G ω ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * a)) * F ω)} := by
    intro ω hbad hgood
    have hscale : D ω = ENNReal.ofReal r * G ω :=
      dg20_lfppDOn_image_mul (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω) U z w r hr
    exact hbad (by
      change ENNReal.ofReal lam⁻¹ * F ω ≤
          ENNReal.ofReal (2 * Real.exp (|(ξ : ℝ)| * a)) *
            (ENNReal.ofReal lam⁻¹ * D ω) ∧
        ENNReal.ofReal lam⁻¹ * D ω ≤
          ENNReal.ofReal (2 * Real.exp (|(ξ : ℝ)| * a)) *
            (ENNReal.ofReal lam⁻¹ * F ω)
      exact dg20_point_norm_compare_of_high_band lam
        (Real.exp (|(ξ : ℝ)| * a)) r hlam
        (Real.exp_pos _).le hr1 hr2
        (F ω) (G ω) (D ω) hgood.1 hgood.2 hscale)
  change P {ω | ¬
    (ENNReal.ofReal lam⁻¹ * F ω ≤
      ENNReal.ofReal A * (ENNReal.ofReal lam⁻¹ * D ω) ∧
     ENNReal.ofReal lam⁻¹ * D ω ≤
      ENNReal.ofReal A * (ENNReal.ofReal lam⁻¹ * F ω))} ≤ _
  exact (measure_mono hsub).trans hraw

end SupercriticalLQGUniqueness.B2.DG20Pt
