/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentWN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional exponential moments of the white noise given its large-time part (P2-GMCID, D67)

For a white noise `W` on `ℝ × ℂ` and a measurable set `S ⊆ ℝ × ℂ` (in the application
`S = (c, ∞) × ℂ`, the "coarse scales" `s > c` of DZZ's white-noise decomposition,
`LBM_LGDarXiv.tex` l. 430–433), let `𝓖_S = σ(W g : g supported in S)` (`wnSigma`). Then:

* `indep_wnSigma_compl` : `𝓖_{Sᶜ}` and `𝓖_S` are independent (from
  `IsWhiteNoise.indepFun_of_disjoint`);
* `condExp_exp_wn` : if `f = f₁ + f₂` with `f₁` supported in `Sᶜ` and `f₂` in `S`, then
  `E(e^{γ W f} | 𝓖_S) = e^{γ W f₂ + γ²‖f₁‖²/2}` a.s.

This is the identity `E(μ_ε(S) | 𝓕_n) = μ^n_ε(S)` of Berestycki, arXiv:1506.09113, §4, `main.tex`
l. 683–685 ("This follows from writing `h = h^n + X` where `X` is independent from `h^n`"), at a
single point, for the white-noise filtration of DZZ l. 653 instead of Karhunen–Loève.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `𝓖_S = σ(W g : g supported in S)`. -/
@[reducible] def wnSigma (W : WNSpace → Ω → ℝ) (S : Set (ℝ × ℂ)) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (g : {g // SupportedIn S g}) => W g ω) inferInstance

lemma wnSigma_le (hW : IsWhiteNoise P W) (S : Set (ℝ × ℂ)) : wnSigma W S ≤ mΩ :=
  Measurable.comap_le (measurable_pi_iff.2 fun (g : {g // SupportedIn S g}) => hW.measurable g.1)

omit mΩ in
lemma measurable_wnSigma {S : Set (ℝ × ℂ)} {g : WNSpace} (hg : SupportedIn S g) :
    Measurable[wnSigma W S] (W g) :=
  have hF : Measurable[wnSigma W S] (fun ω (g : {g // SupportedIn S g}) => W g ω) :=
    comap_measurable _
  (measurable_pi_apply (⟨g, hg⟩ : {g // SupportedIn S g})).comp hF

lemma indep_wnSigma_compl (hW : IsWhiteNoise P W) (S : Set (ℝ × ℂ)) :
    Indep (wnSigma W Sᶜ) (wnSigma W S) P :=
  hW.indepFun_of_disjoint (disjoint_compl_left (a := S))

lemma integrable_exp_wn (hW : IsWhiteNoise P W) (γ : ℝ) (f : WNSpace) :
    Integrable (fun ω => Real.exp (γ * W f ω)) P :=
  (hW.hasLaw_single f).integrable_comp (f := fun x => Real.exp (γ * x))
    (integrable_exp_mul_gaussianReal γ)

lemma integral_exp_wn (hW : IsWhiteNoise P W) (γ : ℝ) (f : WNSpace) :
    ∫ ω, Real.exp (γ * W f ω) ∂P = Real.exp (γ ^ 2 / 2 * ‖f‖ ^ 2) := by
  have h := mgf_gaussianReal (hW.hasLaw_single f) γ
  rw [mgf] at h
  simp only [zero_mul, zero_add, Real.coe_toNNReal _ (sq_nonneg _)] at h
  rw [h]; ring_nf

/-- **Conditional exponential moment**: `E(e^{γ W f} | 𝓖_S) = e^{γ W f₂ + γ²‖f₁‖²/2}` for
`f = f₁ + f₂`, `f₁` supported in `Sᶜ`, `f₂` supported in `S`. -/
theorem condExp_exp_wn (hW : IsWhiteNoise P W) (γ : ℝ) {S : Set (ℝ × ℂ)} {f f₁ f₂ : WNSpace}
    (hf : f = f₁ + f₂) (h₁ : SupportedIn Sᶜ f₁) (h₂ : SupportedIn S f₂) :
    P[fun ω => Real.exp (γ * W f ω) | wnSigma W S] =ᵐ[P]
      fun ω => Real.exp (γ * W f₂ ω + γ ^ 2 / 2 * ‖f₁‖ ^ 2) := by
  have := hW.isProbabilityMeasure
  have hle := wnSigma_le hW S
  have hsplit : (fun ω => Real.exp (γ * W f ω)) =ᵐ[P]
      (fun ω => Real.exp (γ * W f₂ ω)) * fun ω => Real.exp (γ * W f₁ ω) := by
    filter_upwards [hW.add_ae f₁ f₂] with ω hω
    rw [hf, hω, Pi.mul_apply, ← Real.exp_add]; ring_nf
  have hm₂ : StronglyMeasurable[wnSigma W S] fun ω => Real.exp (γ * W f₂ ω) :=
    (Real.measurable_exp.comp ((measurable_wnSigma h₂).const_mul γ)).stronglyMeasurable
  have hm₁ : StronglyMeasurable[wnSigma W Sᶜ] fun ω => Real.exp (γ * W f₁ ω) :=
    (Real.measurable_exp.comp ((measurable_wnSigma h₁).const_mul γ)).stronglyMeasurable
  have hint : Integrable ((fun ω => Real.exp (γ * W f₂ ω)) * fun ω => Real.exp (γ * W f₁ ω)) P :=
    (integrable_exp_wn hW γ f).congr hsplit
  refine (condExp_congr_ae hsplit).trans ?_
  refine (condExp_mul_of_stronglyMeasurable_left hm₂ hint (integrable_exp_wn hW γ f₁)).trans ?_
  filter_upwards [condExp_indep_eq (wnSigma_le hW Sᶜ) hle hm₁ (indep_wnSigma_compl hW S)]
    with ω hω
  rw [Pi.mul_apply, hω, integral_exp_wn hW γ f₁, ← Real.exp_add]

end GMCIdent
end LQGMetric
