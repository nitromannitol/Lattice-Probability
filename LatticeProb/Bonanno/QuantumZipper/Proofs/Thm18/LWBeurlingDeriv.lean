/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingDeriv at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingCarl
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4, node B2a: derivatives of Carleman's circle energy (`CircleEnergyDerivStmt`)

Plan: `handoff/LW-BEURLING.md`. Differentiation under the integral sign (mathlib
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), with the derivative bounded
on the compact rectangle `[t−δ, t+δ] × [−π, π]` inside `{Re ζ < T}`; own routine argument.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Derivative along `t` of a differentiable function at `s + iθ`. -/
lemma lwb_tslice_hasDerivAt {F : ℂ → ℝ} {s θ : ℝ}
    (hF : DifferentiableAt ℝ F ((s : ℂ) + (θ : ℂ) * Complex.I)) :
    HasDerivAt (fun s : ℝ => F ((s : ℂ) + (θ : ℂ) * Complex.I))
      (lpDt F ((s : ℂ) + (θ : ℂ) * Complex.I)) s := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) + (θ : ℂ) * Complex.I) 1 s := by
    simpa using (hasDerivAt_id s).ofReal_comp.add_const ((θ : ℂ) * Complex.I)
  exact hF.hasFDerivAt.comp_hasDerivAt s hl

/-- Differentiation of `s ↦ ∫_{-π}^{π} G(s + iθ) dθ` under the integral sign. -/
lemma lwb_param_deriv {G G' : ℂ → ℝ} {T t : ℝ} (ht : t < T)
    (hGc : ContinuousOn G {ζ : ℂ | ζ.re < T}) (hG'c : ContinuousOn G' {ζ : ℂ | ζ.re < T})
    (hd : ∀ s θ : ℝ, s < T →
      HasDerivAt (fun s : ℝ => G ((s : ℂ) + (θ : ℂ) * Complex.I))
        (G' ((s : ℂ) + (θ : ℂ) * Complex.I)) s) :
    HasDerivAt (fun s : ℝ => ∫ θ in (-π)..π, G ((s : ℂ) + (θ : ℂ) * Complex.I))
      (∫ θ in (-π)..π, G' ((t : ℂ) + (θ : ℂ) * Complex.I)) t := by
  set δ := (T - t) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set Φ : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I with hΦ
  have hΦc : Continuous Φ := by fun_prop
  set S := Φ '' (Icc (t - δ) (t + δ) ×ˢ Icc (-π) π) with hS
  have hSc : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image hΦc
  have hSΩ : S ⊆ {ζ : ℂ | ζ.re < T} := by
    rintro _ ⟨p, hp, rfl⟩
    simp only [hΦ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Set.mem_ofPred_eq,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have := hp.1.2
    rw [hδ] at this
    linarith
  obtain ⟨K, hK⟩ := hSc.exists_bound_of_continuousOn (hG'c.mono hSΩ)
  have hmem : ∀ s θ : ℝ, s < T → ((s : ℂ) + (θ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < T} :=
    fun s θ hs => by simp [hs]
  have hsl : ∀ s : ℝ, s < T → Continuous fun θ : ℝ => G ((s : ℂ) + (θ : ℂ) * Complex.I) :=
    fun s hs => hGc.comp_continuous (lwb_line_continuous s) fun θ => hmem s θ hs
  have hsl' : ∀ s : ℝ, s < T → Continuous fun θ : ℝ => G' ((s : ℂ) + (θ : ℂ) * Complex.I) :=
    fun s hs => hG'c.comp_continuous (lwb_line_continuous s) fun θ => hmem s θ hs
  have hball : Ioo (t - δ) (t + δ) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hlt : ∀ x ∈ Ioo (t - δ) (t + δ), x < T := fun x hx => by
    have := hx.2; rw [hδ] at this; linarith
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (θ : ℝ) => G ((s : ℂ) + (θ : ℂ) * Complex.I))
    (F' := fun (s : ℝ) (θ : ℝ) => G' ((s : ℂ) + (θ : ℂ) * Complex.I)) (bound := fun _ => K)
    hball ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hball] with x hx
    exact (hsl x (hlt x hx)).aestronglyMeasurable
  · exact (hsl t ht).intervalIntegrable _ _
  · exact (hsl' t ht).aestronglyMeasurable
  · refine Eventually.of_forall fun θ hθ x hx => ?_
    have hθ' : θ ∈ Icc (-π) π := by
      have := uIoc_subset_uIcc hθ
      rwa [uIcc_of_le (by linarith [Real.pi_pos])] at this
    exact hK _ ⟨(x, θ), ⟨Ioo_subset_Icc_self hx, hθ'⟩, rfl⟩
  · exact Eventually.of_forall fun θ _ x hx => hd x θ (hlt x hx)

/-- **B2a** (`CircleEnergyDerivStmt`). -/
theorem circleEnergyDerivStmt_holds : CircleEnergyDerivStmt := by
  intro V T hV t ht
  set Ω : Set ℂ := {ζ : ℂ | ζ.re < T} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt Complex.continuous_re continuous_const
  have hd1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ V y) Ω := hV.fderiv_of_isOpen hΩo (by norm_num)
  have hDt : ContDiffOn ℝ 1 (lpDt V) Ω := hd1.clm_apply contDiffOn_const
  have hDtt : ContinuousOn (lpDtt V) Ω :=
    (hDt.continuousOn_fderiv_of_isOpen hΩo le_rfl).clm_apply continuousOn_const
  have hmem : ∀ s θ : ℝ, s < T → ((s : ℂ) + (θ : ℂ) * Complex.I) ∈ Ω :=
    fun s θ hs => by simp [hΩ, hs]
  have hdV : ∀ s θ : ℝ, s < T → DifferentiableAt ℝ V ((s : ℂ) + (θ : ℂ) * Complex.I) :=
    fun s θ hs => (hV.differentiableOn (by norm_num) _ (hmem s θ hs)).differentiableAt
      (hΩo.mem_nhds (hmem s θ hs))
  have hdDt : ∀ s θ : ℝ, s < T → DifferentiableAt ℝ (lpDt V) ((s : ℂ) + (θ : ℂ) * Complex.I) :=
    fun s θ hs => (hDt.differentiableOn (by norm_num) _ (hmem s θ hs)).differentiableAt
      (hΩo.mem_nhds (hmem s θ hs))
  constructor
  · refine lwb_param_deriv (G := fun ζ => V ζ ^ 2)
      (G' := fun ζ => 2 * (V ζ * lpDt V ζ)) ht (hV.continuousOn.pow 2)
      (continuousOn_const.mul (hV.continuousOn.mul hDt.continuousOn)) ?_
    intro s θ hs
    exact ((lwb_tslice_hasDerivAt (hdV s θ hs)).pow 2).congr_deriv (by push_cast; ring)
  · refine lwb_param_deriv (G := fun ζ => 2 * (V ζ * lpDt V ζ))
      (G' := fun ζ => 2 * (lpDt V ζ ^ 2 + V ζ * lpDtt V ζ)) ht
      (continuousOn_const.mul (hV.continuousOn.mul hDt.continuousOn))
      (continuousOn_const.mul ((hDt.continuousOn.pow 2).add (hV.continuousOn.mul hDtt))) ?_
    intro s θ hs
    exact (((lwb_tslice_hasDerivAt (hdV s θ hs)).mul
      (lwb_tslice_hasDerivAt (hdDt s θ hs))).const_mul 2).congr_deriv (by unfold lpDtt lpDt; ring)

end LWFar
end Thm18Asm
end QuantumZipper
