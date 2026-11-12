/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingLogPolar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingDefs
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LWF-4, B4c: log-polar subharmonicity

Task LWB-B4c (plan: `handoff/LW-BEURLING.md`). We prove `LogPolarSubharmStmt`: if `v` has the
local normal form `LocConvHarmForm` on `B(w, ρ)`, then `V(ζ) = v(w + e^ζ)` is `C²` on
`{Re ζ < log ρ}` and `V_tt + V_θθ ≥ 0` there.

Proof: own; standard chain rule (elementary computation, no published source needed). Near a
point where `v = φ ∘ Re ∘ f`, put `G(ξ) = f(w + e^ξ)` (holomorphic). For a direction `u ∈ ℂ`,
`∂_u (φ ∘ Re G) = φ'(Re G) Re(u G')` and
`∂_u² (φ ∘ Re G) = φ''(Re G) Re(u G')² + φ'(Re G) Re(u² G'')`; summing `u = 1` and `u = i`
the `φ'` terms cancel, leaving `φ''(Re G) (Re(G')² + Re(iG')²) ≥ 0`.
-/

noncomputable section

open Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Chain rule for `z ↦ φ (Re (G z))` with `G` complex-differentiable. -/
theorem lpLP_hasFDerivAt_comp_re (φ : ℝ → ℝ) (G : ℂ → ℂ) (ξ : ℂ) (φ' : ℝ) (G' : ℂ)
    (hφ : HasDerivAt φ φ' (G ξ).re) (hG : HasDerivAt G G' ξ) :
    HasFDerivAt (fun z => φ (G z).re)
      (φ' • (Complex.reCLM.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) G').restrictScalars ℝ))) ξ := by
  have h1 : HasFDerivAt G
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) G').restrictScalars ℝ) ξ :=
    hG.hasFDerivAt.restrictScalars ℝ
  have h2 := Complex.reCLM.hasFDerivAt.comp ξ h1
  exact hφ.comp_hasFDerivAt ξ h2

/-- Directional derivative of `z ↦ φ (Re (G z))`. -/
theorem lpLP_fderiv_comp_re_apply (φ : ℝ → ℝ) (G : ℂ → ℂ) (ξ : ℂ) (φ' : ℝ) (G' : ℂ)
    (hφ : HasDerivAt φ φ' (G ξ).re) (hG : HasDerivAt G G' ξ) (u : ℂ) :
    fderiv ℝ (fun z => φ (G z).re) ξ u = φ' * (u * G').re := by
  rw [(lpLP_hasFDerivAt_comp_re φ G ξ φ' G' hφ hG).fderiv]
  simp

/-- Second directional derivatives depend only on the germ. -/
theorem lpLP_second_congr {V W : ℂ → ℝ} {ζ : ℂ} (h : V =ᶠ[𝓝 ζ] W) (u : ℂ) :
    fderiv ℝ (fun ξ => fderiv ℝ V ξ u) ζ u = fderiv ℝ (fun ξ => fderiv ℝ W ξ u) ζ u := by
  have h' : (fun ξ => fderiv ℝ V ξ u) =ᶠ[𝓝 ζ] (fun ξ => fderiv ℝ W ξ u) :=
    h.eventuallyEq_nhds.mono fun y hy => by simp only [hy.fderiv_eq]
  rw [h'.fderiv_eq]

/-- The second directional derivative of `φ ∘ Re ∘ G` for `G` analytic. -/
theorem lpLP_second_formula (φ : ℝ → ℝ) (G : ℂ → ℂ) (ζ : ℂ) (hφ : ContDiff ℝ 2 φ)
    (hG : AnalyticAt ℂ G ζ) (u : ℂ) :
    fderiv ℝ (fun ξ => fderiv ℝ (fun z => φ (G z).re) ξ u) ζ u =
      deriv φ (G ζ).re * (u * (u * deriv (deriv G) ζ)).re +
        (u * deriv G ζ).re * (deriv (deriv φ) (G ζ).re * (u * deriv G ζ).re) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ2 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have hev : (fun ξ => fderiv ℝ (fun z => φ (G z).re) ξ u) =ᶠ[𝓝 ζ]
      (fun ξ => deriv φ (G ξ).re * (u * deriv G ξ).re) := by
    filter_upwards [hG.eventually_analyticAt] with ξ hξ
    exact lpLP_fderiv_comp_re_apply φ G ξ _ _ (hφd _).hasDerivAt
      hξ.differentiableAt.hasDerivAt u
  rw [hev.fderiv_eq]
  have hc := lpLP_hasFDerivAt_comp_re (deriv φ) G ζ _ _ (hφ2 _).hasDerivAt
    hG.differentiableAt.hasDerivAt
  have hG1 : HasDerivAt (fun ξ => u * deriv G ξ) (u * deriv (deriv G) ζ) ζ :=
    (hG.deriv.differentiableAt.hasDerivAt).const_mul u
  have hd := lpLP_hasFDerivAt_comp_re id (fun ξ => u * deriv G ξ) ζ 1 _
    (hasDerivAt_id _) hG1
  have hm : HasFDerivAt (fun ξ => deriv φ (G ξ).re * (u * deriv G ξ).re) _ ζ := hc.mul hd
  rw [hm.fderiv]
  simp

/-- Log-polar Laplacian of `φ ∘ Re ∘ G` is nonnegative for `φ` convex. -/
theorem lpLP_laplacian_nonneg (φ : ℝ → ℝ) (G : ℂ → ℂ) (ζ : ℂ) (hφ : ContDiff ℝ 2 φ)
    (hφ'' : ∀ s, 0 ≤ deriv (deriv φ) s) (hG : AnalyticAt ℂ G ζ) :
    0 ≤ fderiv ℝ (fun ξ => fderiv ℝ (fun z => φ (G z).re) ξ 1) ζ 1 +
      fderiv ℝ (fun ξ => fderiv ℝ (fun z => φ (G z).re) ξ Complex.I) ζ Complex.I := by
  rw [lpLP_second_formula φ G ζ hφ hG, lpLP_second_formula φ G ζ hφ hG]
  have h0 := hφ'' (G ζ).re
  have e1 : (Complex.I * (Complex.I * deriv (deriv G) ζ)).re = -(deriv (deriv G) ζ).re := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [e1]
  simp only [one_mul]
  nlinarith [mul_nonneg h0 (sq_nonneg (deriv G ζ).re),
    mul_nonneg h0 (sq_nonneg (Complex.I * deriv G ζ).re)]

/-- **B4c. Log-polar subharmonicity.** Own; standard chain rule. -/
theorem logPolarSubharmStmt_holds : LogPolarSubharmStmt := by
  intro v w ρ hρ hform
  -- pointwise statement at each `ζ` with `Re ζ < log ρ`
  have key : ∀ ζ : ℂ, ζ.re < Real.log ρ →
      ContDiffAt ℝ 2 (fun ζ => v (w + Complex.exp ζ)) ζ ∧
      0 ≤ lpDtt (fun ζ => v (w + Complex.exp ζ)) ζ +
        lpDθθ (fun ζ => v (w + Complex.exp ζ)) ζ := by
    intro ζ hζ
    have hx : w + Complex.exp ζ ∈ ball w ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
      calc Real.exp ζ.re < Real.exp (Real.log ρ) := Real.exp_lt_exp.mpr hζ
        _ = ρ := Real.exp_log hρ
    have htend : Tendsto (fun ξ : ℂ => w + Complex.exp ξ) (𝓝 ζ) (𝓝 (w + Complex.exp ζ)) :=
      (continuous_const.add Complex.continuous_exp).tendsto ζ
    rcases hform _ hx with h0 | ⟨φ, f, hφ, hφ'', hf, hv⟩
    · have hV : (fun ξ => v (w + Complex.exp ξ)) =ᶠ[𝓝 ζ] fun _ => (0 : ℝ) :=
        h0.comp_tendsto htend
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hV, ?_⟩
      unfold lpDtt lpDθθ lpDt lpDθ
      rw [lpLP_second_congr hV, lpLP_second_congr hV]
      simp
    · set G : ℂ → ℂ := fun ξ => f (w + Complex.exp ξ) with hGdef
      have hGa : AnalyticAt ℂ G ζ := by
        have ha : AnalyticAt ℂ (fun ξ : ℂ => w + Complex.exp ξ) ζ :=
          analyticAt_const.add analyticAt_cexp
        exact AnalyticAt.comp (g := f) (f := fun ξ : ℂ => w + Complex.exp ξ) hf ha
      have hV : (fun ξ => v (w + Complex.exp ξ)) =ᶠ[𝓝 ζ] fun ξ => φ (G ξ).re :=
        hv.comp_tendsto htend
      refine ⟨?_, ?_⟩
      · have hW : ContDiffAt ℝ 2 (fun ξ => φ (G ξ).re) ζ := by
          have hGr : ContDiffAt ℝ 2 G ζ := hGa.contDiffAt.restrict_scalars ℝ
          exact hφ.contDiffAt.comp ζ (Complex.reCLM.contDiff.contDiffAt.comp ζ hGr)
        exact hW.congr_of_eventuallyEq hV
      · unfold lpDtt lpDθθ lpDt lpDθ
        rw [lpLP_second_congr hV, lpLP_second_congr hV]
        exact lpLP_laplacian_nonneg φ G ζ hφ hφ'' hGa
  refine ⟨fun ζ hζ => (key ζ hζ).1.contDiffWithinAt, fun ζ hζ => (key ζ hζ).2⟩

end LWFar
end Thm18Asm
end QuantumZipper
