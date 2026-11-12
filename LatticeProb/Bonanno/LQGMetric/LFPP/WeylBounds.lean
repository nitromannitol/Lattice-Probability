/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.WeylBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField

/-!
# DFGPS.S5, bounded part: `e^{-ξ‖f‖} D^ε_h ≤ D^ε_{h+f} ≤ e^{ξ‖f‖} D^ε_h`

Task P2-LFPP (DFGPS.S5, `lqg-metric-estimates-final.tex` T:1040/T:897/T:964: "if f is bounded
then …"). Pointwise comparison of the LFPP integrands, and `|f*_ε| ≤ ‖f‖_∞` (the heat kernel is a
probability density). Stated with `|ξ|` (DFGPS have `ξ > 0`). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ}

theorem lfppD_add_le_of_bound (ψ : ℂ → ℝ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) (z w : ℂ) :
    lfppD ξ (fun x => φ x + ψ x) z w ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppD ξ φ z w := by
  unfold lfppD lfppDOn
  rw [ENNReal.mul_iInf_of_ne (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => ?_
  rw [lfppLen_eq, lfppLen_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun s => ?_
  rw [lenDens_add]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  calc ξ * ψ (P.1 s) ≤ |ξ * ψ (P.1 s)| := le_abs_self _
    _ = |ξ| * |ψ (P.1 s)| := abs_mul _ _
    _ ≤ |ξ| * M := mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)

theorem lfppD_le_add_of_bound (ψ : ℂ → ℝ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) (z w : ℂ) :
    lfppD ξ φ z w ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppD ξ (fun x => φ x + ψ x) z w := by
  have := lfppD_add_le_of_bound (ξ := ξ) (φ := fun x => φ x + ψ x) (fun x => -ψ x)
    (fun x => by rw [abs_neg]; exact hM x) z w
  simpa only [add_neg_cancel_right] using this

theorem abs_heatMollify_ofCont_le (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M) {ε : ℝ}
    (hε : ε ≠ 0) (z : ℂ) : |heatMollify ε (ofCont f) z| ≤ M := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  rw [heatMollify_ofCont f M hM ε hε z]
  calc |∫ w, f w * heatKernel (ε ^ 2 / 2) z w| ≤ ∫ w, |f w * heatKernel (ε ^ 2 / 2) z w| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, M * heatKernel (ε ^ 2 / 2) z w := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((integrable_heatKernel _ hs z).const_mul M) (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg _ hs.le z w)]
        exact mul_le_mul_of_nonneg_right (hM w) (heatKernel_nonneg _ hs.le z w)
    _ = M := by rw [integral_const_mul, integral_heatKernel _ hs z, mul_one]

/-- **DFGPS.S5, bounds**: `e^{-|ξ|M} D^ε_h ≤ D^ε_{h+f} ≤ e^{|ξ|M} D^ε_h` for `|f| ≤ M`, where the
truncations of `h` converge (a.s. for a GFF plus a bounded continuous function). -/
theorem lfppDistE_addFun_mem_bounds (ξ : ℝ) {ε : ℝ} (hε : ε ≠ 0) {h : DistC}
    (hconv : ∀ z, Tendsto (fun n : ℕ => h (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (heatMollify ε h z))) (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M) (z w : ℂ) :
    lfppDistE ξ ε (addFun h f) z w ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppDistE ξ ε h z w ∧
      lfppDistE ξ ε h z w ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppDistE ξ ε (addFun h f) z w := by
  simp only [lfppDistE_eq_lfppDOn, heatMollify_addFun hε hconv f M hM]
  exact ⟨lfppD_add_le_of_bound _ (abs_heatMollify_ofCont_le f hM hε) z w,
    lfppD_le_add_of_bound _ (abs_heatMollify_ofCont_le f hM hε) z w⟩

end LFPP
end LQGMetric
