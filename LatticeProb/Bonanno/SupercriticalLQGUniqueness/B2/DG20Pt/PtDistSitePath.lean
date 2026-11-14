/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSitePath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCrossingPath

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_site_crossing_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (x : ℂ) (T : ℝ) (hT : 0 < T) (ω : Ω)
    (hgood : ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let a : ℝ := Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω) *
      (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))
    ∃ γ : ℝ → ℂ,
      AdmPath (ball x (17 * r)) (sphere x (r / 4)) (sphere x (16 * r)) γ ∧
      lfppLen (ξ : ℝ) (fun z => phiMN W P 0 n z ω) γ < ENNReal.ofReal (2 * a) := by
  dsimp
  have hlam : 0 < lambdaN ξ W P n := lambdaN_pos hW n
  let a : ℝ := Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω) *
    (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))
  have ha : 0 < a := by dsimp [a]; positivity
  have hcross := hgood.1
  change crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
      (ball x (17 * ((2 : ℝ)⁻¹ ^ k)))
      (sphere x (((2 : ℝ)⁻¹ ^ k) / 4))
      (sphere x (16 * ((2 : ℝ)⁻¹ ^ k))) ≤
    ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
      ENNReal.ofReal (T *
        ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) at hcross
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le] at hcross
  have hstrict : crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
      (ball x (17 * ((2 : ℝ)⁻¹ ^ k)))
      (sphere x (((2 : ℝ)⁻¹ ^ k) / 4))
      (sphere x (16 * ((2 : ℝ)⁻¹ ^ k))) < ENNReal.ofReal (2 * a) :=
    hcross.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * a)).2
      (by dsimp [a]; linarith [ha]))
  exact exists_crossing_of_crossLenIn_lt hstrict

end SupercriticalLQGUniqueness.B2.DG20Pt
