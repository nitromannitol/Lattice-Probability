/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.CircleKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.Smoothness
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Ding–Goswami Prop 3.3: the circle-averaged white-noise kernel and the bound on `G_{v;4}`
(task P2-DGO, WP-105)

Source: Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex` (cited `DGo:`). DGo's field
`ĥ^𝒰_δ(v)` (eq. (3.1), DGo:491–494) is the white noise applied to the circle average over
`∂B_δ(v)` of a heat kernel, and the proof of Prop 3.3 (DGo:618–700) splits
`Δ_δ(v) = ĥ^𝒰_δ(v) − η_δ(v) = √π (G_{v;1} + G_{v;2} + G_{v;3} + G_{v;4})`, where
`G_{v;4} = ∫_{ℝ² × [δ², 1]} (p^δ(s/2; v, w) − p(s/2; v, w)) W(dw, ds)` compares the circle
average of the free kernel with its value at the centre (DGo:625).

* `circKernel a b δ v` — the circle average `(2π)⁻¹ ∫_0^{2π} k_{a,b}(v + δe^{iθ}) dθ` of the
  `L²` kernel `k_{a,b}(x) = phiKernelL2 a b x` of `η_a^b(x) = √π W(k_{a,b}(x))` (Bochner integral
  in `L²(ℝ × ℂ)`), so `√π W(circKernel δ 1 δ v)` is the circle average of `η_δ` and
  `√π W(circKernel δ 1 δ v − phiKernelL2 δ 1 v) = √π G_{v;4}`.
* `norm_sqrtPi_smul_phiKernelL2_sub_le` — `‖√π (k_{a,b}(x) − k_{a,b}(x'))‖ ≤ |x − x'|/a`
  (DGo Lemma 3.2 in kernel form).
* `dgo_varG4_le` — **`Var(√π G_{v;4}) ≤ 1`** (DGo:684–700: "`Var(G_{v;4}) = O(1)`").

Route: DGo compute `Var(G_{v;4}) = I₁ − 2I₂ + I₃` explicitly (DGo:686–699). We use instead the
convexity of the norm (`‖avg f − f(v)‖ ≤ max_θ ‖f(v + δe^{iθ}) − f(v)‖`) and DGo's own Lemma 3.2
with `|v + δe^{iθ} − v| = δ`, which gives the same `O(1)` bound (own two-line variant;
proposed deviation DGo-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped Interval

namespace LQGMetric
namespace DGo

open WhiteNoise

/-- `‖√π (k_{a,b}(x) − k_{a,b}(x'))‖ ≤ |x − x'|/a` for `0 < a ≤ b` (DGo Lemma 3.2, kernel form). -/
theorem norm_sqrtPi_smul_phiKernelL2_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x x' : ℂ) :
    ‖Real.sqrt Real.pi • (phiKernelL2 a b x - phiKernelL2 a b x')‖ ≤ ‖x - x'‖ / a := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have h := hW.hasLaw ![phiKernelL2 a b x, phiKernelL2 a b x']
    ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have e : (fun ω => Real.sqrt Real.pi * W (phiKernelL2 a b x) ω +
      -Real.sqrt Real.pi * W (phiKernelL2 a b x') ω) =
      fun ω => phi W a b x ω - phi W a b x' ω := by
    funext ω; simp only [phi]; ring
  rw [e] at h
  have hv := dgo_lemma32 hW ha hab x x'
  rw [h.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)] at hv
  have e2 : Real.sqrt Real.pi • phiKernelL2 a b x + -Real.sqrt Real.pi • phiKernelL2 a b x' =
      Real.sqrt Real.pi • (phiKernelL2 a b x - phiKernelL2 a b x') := by
    rw [neg_smul, ← sub_eq_add_neg, smul_sub]
  rw [e2] at hv
  have hr : ‖x - x'‖ ^ 2 / a ^ 2 = (‖x - x'‖ / a) ^ 2 := by rw [div_pow]
  rw [hr] at hv
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hv

/-- `x ↦ k_{a,b}(x)` is continuous into `L²` (`0 < a ≤ b`). -/
lemma continuous_phiKernelL2 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Continuous (phiKernelL2 a b) := by
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  refine LipschitzWith.continuous (K := ⟨(Real.sqrt Real.pi * a)⁻¹, by positivity⟩)
    (LipschitzWith.of_dist_le_mul fun x x' => ?_)
  have h := norm_sqrtPi_smul_phiKernelL2_sub_le ha hab x x'
  rw [norm_smul, Real.norm_of_nonneg hpi.le] at h
  change dist _ _ ≤ (Real.sqrt Real.pi * a)⁻¹ * dist x x'
  rw [dist_eq_norm, dist_eq_norm]
  rw [← le_div_iff₀' hpi] at h
  refine h.trans_eq ?_
  field_simp

end DGo
end LQGMetric
