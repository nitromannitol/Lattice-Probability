/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentExp at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable); eLpNorm_le_eLpNorm_of_exponent_le no longer takes the measurability argument. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentWN
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `L¹` continuity of `g ↦ e^{a W(g)}` for a white noise (P2-GMCID, D67)

`tendsto_eLpNorm_exp_wn`: if `g_k → g` in `L²(ℝ × ℂ)` then `e^{a W(g_k)} → e^{a W(g)}` in `L¹(P)`.
Own elementary proof: `E(e^{aW(g_k)} − e^{aW(g)})² = e^{2a²‖g_k‖²} − 2e^{a²‖g_k + g‖²/2} + e^{2a²‖g‖²}`
(Gaussian moment generating function, `integral_exp_wn`), which tends to `0`, and
`‖·‖₁ ≤ ‖·‖₂`. Used for the limit `ε → 0` of `E(μ_ε(S) | 𝓕_n)` in Berestycki's uniqueness argument
(arXiv:1506.09113, §4, l. 686–687: "the right hand side converges … by continuity of `h^n`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the second moment of `e^{aW(g)} − e^{aW(h)}` -/
def expGap (a : ℝ) (g h : WNSpace) : ℝ :=
  Real.exp (2 * a ^ 2 * ‖g‖ ^ 2) - 2 * Real.exp (a ^ 2 / 2 * ‖g + h‖ ^ 2) +
    Real.exp (2 * a ^ 2 * ‖h‖ ^ 2)

lemma memLp_exp_wn (hW : IsWhiteNoise P W) (a : ℝ) (g : WNSpace) :
    MemLp (fun ω => Real.exp (a * W g ω)) 2 P := by
  refine (memLp_two_iff_integrable_sq ((Real.measurable_exp.comp
    ((hW.measurable g).const_mul a)).aestronglyMeasurable)).2 ?_
  refine (integrable_exp_wn hW (2 * a) g).congr (Eventually.of_forall fun ω => ?_)
  simp only [Function.comp_apply, Pi.pow_apply]; rw [sq, ← Real.exp_add]; ring_nf

lemma integral_sq_exp_sub_wn (hW : IsWhiteNoise P W) (a : ℝ) (g h : WNSpace) :
    ∫ ω, (Real.exp (a * W g ω) - Real.exp (a * W h ω)) ^ 2 ∂P = expGap a g h := by
  have e1 : ∀ f : WNSpace, ∫ ω, Real.exp (a * W f ω) ^ 2 ∂P = Real.exp (2 * a ^ 2 * ‖f‖ ^ 2) := by
    intro f
    rw [← show ∫ ω, Real.exp (2 * a * W f ω) ∂P = Real.exp (2 * a ^ 2 * ‖f‖ ^ 2) by
      rw [integral_exp_wn hW]; ring_nf]
    congr 1; funext ω; rw [sq, ← Real.exp_add]; ring_nf
  have e2 : ∫ ω, Real.exp (a * W g ω) * Real.exp (a * W h ω) ∂P =
      Real.exp (a ^ 2 / 2 * ‖g + h‖ ^ 2) := by
    rw [← integral_exp_wn hW a (g + h)]
    refine integral_congr_ae ?_
    filter_upwards [hW.add_ae g h] with ω hω
    rw [hω, ← Real.exp_add]; ring_nf
  have hi : ∀ f : WNSpace, Integrable (fun ω => Real.exp (a * W f ω) ^ 2) P := fun f =>
    (memLp_two_iff_integrable_sq (memLp_exp_wn hW a f).aestronglyMeasurable).1 (memLp_exp_wn hW a f)
  have hm : Integrable (fun ω => Real.exp (a * W g ω) * Real.exp (a * W h ω)) P :=
    (memLp_exp_wn hW a g).integrable_mul (memLp_exp_wn hW a h)
  have ex : (fun ω => (Real.exp (a * W g ω) - Real.exp (a * W h ω)) ^ 2) =
      fun ω => Real.exp (a * W g ω) ^ 2 - 2 * (Real.exp (a * W g ω) * Real.exp (a * W h ω)) +
        Real.exp (a * W h ω) ^ 2 := by
    funext ω; ring
  have h1 := integral_add ((hi g).sub (hm.const_mul 2)) (hi h)
  have h2 := integral_sub (hi g) (hm.const_mul 2)
  simp only [Pi.sub_apply] at h1 h2
  rw [ex, h1, h2, integral_const_mul, e1, e1, e2, expGap]

lemma expGap_self (a : ℝ) (g : WNSpace) : expGap a g g = 0 := by
  unfold expGap
  rw [← two_smul ℝ g, norm_smul]
  norm_num
  ring_nf

lemma continuous_expGap (a : ℝ) (h : WNSpace) : Continuous fun g => expGap a g h := by
  unfold expGap; fun_prop

/-- **`L¹` continuity of `g ↦ e^{aW(g)}`.** -/
theorem tendsto_eLpNorm_exp_wn (hW : IsWhiteNoise P W) (a : ℝ) {g : ℕ → WNSpace} {g₀ : WNSpace}
    (hg : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun k => eLpNorm ((fun ω => Real.exp (a * W (g k) ω)) -
      fun ω => Real.exp (a * W g₀ ω)) 1 P) atTop (𝓝 0) := by
  have := hW.isProbabilityMeasure
  have hb : ∀ k, eLpNorm ((fun ω => Real.exp (a * W (g k) ω)) - fun ω => Real.exp (a * W g₀ ω)) 1 P
      ≤ ENNReal.ofReal (Real.sqrt (expGap a (g k) g₀)) := by
    intro k
    have hD := (memLp_exp_wn hW a (g k)).sub (memLp_exp_wn hW a g₀)
    refine (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num)).trans (le_of_eq ?_)
    rw [hD.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ← integral_sq_exp_sub_wn hW,
      Real.sqrt_eq_rpow]
    congr 2
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofNat]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    · norm_num
  have h0 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (expGap a (g k) g₀))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero, ← Real.sqrt_zero, ← expGap_self a g₀]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_sqrt.tendsto _).comp ((continuous_expGap a g₀).tendsto _ |>.comp hg))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hb

end GMCIdent
end LQGMetric
