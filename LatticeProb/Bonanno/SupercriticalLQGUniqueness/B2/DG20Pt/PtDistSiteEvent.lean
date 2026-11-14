/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossSite
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundEstimate

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistSiteGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ) (x : ℂ) (T : ℝ) : Set Ω :=
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
      (ball x (17 * r)) (sphere x (r / 4)) (sphere x (16 * r)) ≤
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
          ENNReal.ofReal (T *
            ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) ∧
    Inputs.HasAroundLoop (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
      x r (by dsimp [r]; positivity)
      (ENNReal.ofReal (T * (C *
        (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
          lambdaN ξ W P n) *
        Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))}

 


theorem pt_dist_site_bad_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C a₀ a₁ b₀ b₁ : ℝ,
      0 < C ∧ 0 < a₀ ∧ 0 < a₁ ∧ 0 < b₀ ∧ 0 < b₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ,
          ∀ T : ℝ, 3 < T →
          P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ ≤
            ENNReal.ofReal (a₀ * Real.exp
              (-a₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
            ENNReal.ofReal (b₀ * Real.exp
              (-b₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) := by
  obtain ⟨a₀, a₁, ha₀, ha₁, hA⟩ :=
    pt_dist_across_site_upper_ball_of_inputs hPerc hExp ξ Q hQ ζ hζ
  obtain ⟨C, b₀, b₁, hC, hb₀, hb₁, hB⟩ :=
    around_scale_upper_of_inputs (dg20AroundEstimate_of_percEstimate hPerc)
      hExp ξ Q hQ ζ hζ
  refine ⟨C, a₀, a₁, b₀, b₁, hC, ha₀, ha₁, hb₀, hb₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  have hAcross := hA P W hW n k hkn x T hT
  have hAround := hB P W hW n k hkn x T hT
  dsimp at hAcross hAround
  let A : Set Ω := {ω | ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) *
      ENNReal.ofReal (T *
        ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n)) <
      crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
        (ball x (17 * ((2 : ℝ)⁻¹ ^ k)))
        (sphere x (((2 : ℝ)⁻¹ ^ k) / 4))
        (sphere x (16 * ((2 : ℝ)⁻¹ ^ k)))}
  let B : Set Ω := {ω | ¬ Inputs.HasAroundLoop (ξ : ℝ)
      (fun z => phiMN W P 0 n z ω) x (((2 : ℝ)⁻¹) ^ k)
      (by positivity)
      (ENNReal.ofReal (T * (C *
        (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
          lambdaN ξ W P n) *
        Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)))}
  have hsub : (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ ⊆ A ∪ B := by
    intro ω hω
    simp only [ptDistSiteGood, Set.mem_compl_iff, Set.mem_ofPred_eq,
      not_and_or, not_le, Set.mem_union] at hω ⊢
    exact hω
  calc
    P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ ≤ P (A ∪ B) := measure_mono hsub
    _ ≤ P A + P B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (a₀ * Real.exp
        (-a₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
      ENNReal.ofReal (b₀ * Real.exp
        (-b₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) :=
      add_le_add (by simpa only [A] using hAcross) (by simpa only [B] using hAround)

end SupercriticalLQGUniqueness.B2.DG20Pt
