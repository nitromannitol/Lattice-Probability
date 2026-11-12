/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePsi at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
DDDF (arXiv:1904.08021, `tightness.tex` l. 350–358): fix a smooth radial bump `Φ` with
`0 ≤ Φ ≤ 1`, `Φ = 1` on `B(0,1)`, `Φ = 0` off `B(0,2)`, small constants `r₀, ε₀ > 0`, and set
`σ_t = r₀ √t |log t|^{ε₀}`, `p^{Tr}_{t/2} := p_{t/2} Φ(·/σ_t)`,
`ψ_δ(x) := ∫_{δ²}^1 ∫ p^{Tr}_{t/2}(x − y) W(dy, dt)` (same white noise `W` as `φ`).

Deviations (blueprint DDDF.md, proposed D-DDDF-1, D-DDDF-3):
* D-DDDF-1: `ψ` carries the factor `√π` of `φ` (l. 355 omits it; (2.23) needs the same
  normalization).
* D-DDDF-3: `σ_t := r₀ √t (1 + |log t|)^{ε₀}` (the printed `|log t|^{ε₀}` vanishes at `t = 1`,
  and the claim `sup_t √t/σ_t < ∞` of l. 417 is false for it).

Here the kernel is `psiKernel a b x = phiKernel a b x · Φ(σ_t⁻¹(x − y))`, pointwise dominated by
`phiKernel`, hence in `L²` (`psiKernelL2`), and `psi W a b x = √π W(psiKernelL2 a b x)`.
The cutoff and the constants are bundled in `PsiParams`; `exists_psiCutoff` shows a cutoff with
all of DDDF's properties exists (mathlib's `ContDiffBumpBase.ofInnerProductSpace`).
Also: the generic variance identity `Var(√π W f − √π W g) = π ‖f − g‖²` and a Fubini lemma
for time-weighted kernels used in Lemma 4 and (2.23).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- DDDF's cutoff `Φ` (l. 352): smooth, radial, `0 ≤ Φ ≤ 1`, `Φ = 1` on the unit ball (closed
ball; equivalent by continuity), `Φ = 0` off the open ball of radius `2`. -/
structure PsiCutoff where
  Φ : ℂ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  radial : ∀ x y : ℂ, ‖x‖ = ‖y‖ → Φ x = Φ y
  nonneg : ∀ x, 0 ≤ Φ x
  le_one : ∀ x, Φ x ≤ 1
  eq_one : ∀ x, ‖x‖ ≤ 1 → Φ x = 1
  eq_zero : ∀ x, 2 ≤ ‖x‖ → Φ x = 0

/-- DDDF's data for `ψ`: the cutoff `Φ` and the constants `r₀, ε₀ > 0` (l. 352). -/
structure PsiParams where
  cut : PsiCutoff
  r₀ : ℝ
  ε₀ : ℝ
  r₀_pos : 0 < r₀
  ε₀_pos : 0 < ε₀

namespace PsiCutoff

variable (C : PsiCutoff)

end PsiCutoff

namespace PsiParams

variable (Q : PsiParams)

end PsiParams

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `Var(√π W f − √π W g) = π ‖f − g‖²`. -/
theorem variance_sqrtPi_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    Var[fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω; P] =
      Real.pi * ‖f - g‖ ^ 2 := by
  have h := hW.hasLaw ![f, g] ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have h' : HasLaw (fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω)
      (gaussianReal 0 (‖Real.sqrt Real.pi • f + (-Real.sqrt Real.pi) • g‖ ^ 2).toNNReal) P :=
    h.congr (Eventually.of_forall fun ω => by simp only; ring)
  rw [h'.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity),
    neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt Real.pi_pos.le]

end WhiteNoise
end LQGMetric
