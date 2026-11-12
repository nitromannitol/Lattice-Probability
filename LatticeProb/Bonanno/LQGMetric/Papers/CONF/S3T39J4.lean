/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412jComp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: completion transfer (DEC-120 §4 S9, packet J4)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), Theorem 3.9 (C:1506–1509).
CONF's probability space is tacitly complete (DV-D120-4); the proof of Theorem 3.9 (via
`CONFThm3_9RestCL`, S3T39J9, S3T39J11) runs on complete spaces. `CONFThm3_9AtC` is `CONFThm3_9At` restricted
to complete probability spaces (with the D130 locality hypothesis on `τ`,
`t39k_isLocalSetDet0_completion`); **`confThm3_9At_of_complete`** removes the restriction by passing
to `(NullMeasurableSpace Ω P, P.completion)` (D70). Copy-and-adapt of
`GM.p412j_P4_12At_of_complete` (P412jComp): the field hypothesis transfers by
`gm_isWholePlaneGFF_completion`, `ae` is unchanged (`Measure.ae_completion`), `confReg` depends on
`P` only through `confRho`, unchanged by completion (`p412j_confRho_completion`), and
`P.completion S = P S` (`Measure.completion_apply`).
-/

noncomputable section

open MeasureTheory Set Metric
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

/-- `confReg` (the event `𝓔_𝕣(a)`) is unchanged by completion -/
theorem t39j_confReg_completion {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hm : Measurable h) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (p : CONFParams) (χ : ℝ) (z₀ : ℂ) (R a : ℝ) :
    confReg ξ cc D P.completion (h ∘ gm_ofNull P) p χ z₀ R a =
      @confReg Ω mΩ ξ cc D P h p χ z₀ R a := by
  simp only [confReg, p412j_confRho_completion hm]
  rfl

/-- the D130 locality hypothesis (`𝓑^•_τ` local modulo additive constants) transfers to the
completion (`gm_ofNull = id`, `Measure.ae_completion`) -/
theorem t39k_isLocalSetDet0_completion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} {A : Ω → Set ℂ} (hA : IsLocalSetDet0 P h A) :
    IsLocalSetDet0 P.completion (h ∘ gm_ofNull P) A := by
  intro U hU
  obtain ⟨F, hF, hEF⟩ := hA U hU
  exact ⟨F, hF, by rw [Measure.ae_completion]; exact hEF⟩

/-- `CONFThm3_9At` restricted to complete probability spaces (D120 S9) -/
def CONFThm3_9AtC (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (χ : ℝ) :
    Prop :=
  ∃ b₁ β : ℝ, 0 < b₁ ∧ 0 < β ∧ ∀ a ∈ Ioo (0 : ℝ) 1, ∃ b₀ : ℝ, 0 < b₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ N : ℕ, 1 ≤ N →
    ∀ τ : Ω → ℝ, IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      P {ω | ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a ∧
          ((N : ℕ∞) : ℕ∞) < (hitSetLM (D (h ω)) z₀ (τ ω)
            (τ ω + (N : ℝ) ^ (-β) * scaleFac (xiGamma γ) c (h ω) R z₀)).encard} ≤
        ENNReal.ofReal (b₀ * Real.exp (-b₁ * (N : ℝ) ^ β))

/-- **D70 completion transfer for CONF Theorem 3.9**: the complete case gives the general one -/
theorem confThm3_9At_of_complete {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    {p : CONFParams} {χ : ℝ} (H : CONFThm3_9AtC γ D c p χ) : CONFThm3_9At γ D c p χ := by
  obtain ⟨b₁, β, hb₁, hβ, H⟩ := H
  refine ⟨b₁, β, hb₁, hβ, fun a ha => ?_⟩
  obtain ⟨b₀, hb₀, H⟩ := H a ha
  refine ⟨b₀, hb₀, fun {Ω} _ P _ h hh z₀ R hR N hN τ hτst hloc hτI => ?_⟩
  have hb := H P.completion (h ∘ gm_ofNull P) (gm_isWholePlaneGFF_completion hh) z₀ R hR N hN
    τ hτst (t39k_isLocalSetDet0_completion hloc) hτI
  rw [t39j_confReg_completion hh.measurable] at hb
  exact le_of_eq_of_le (Measure.completion_apply P _).symm hb

end CONF
end LQGMetric
