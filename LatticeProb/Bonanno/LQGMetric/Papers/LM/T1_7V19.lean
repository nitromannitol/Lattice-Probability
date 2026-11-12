/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V19 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# LM Theorem 1.7, the limit `ε → 0`: reverse Fatou step

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), D107 §3(v) ("Limit `ε → 0` (dominated convergence given `(h,θ)`)"):
if `v ≤ ∫ G_j` for every mesh `ε_j`, the `G_j` are dominated by an integrable function and
`limsup_j G_j ≤ H` a.e., then `v ≤ ∫ H` (`limsup_lintegral_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace LQGMetric.LM

/-- **reverse Fatou for the mesh limit** -/
theorem t17v_fatou {α : Type*} [MeasurableSpace α] {ν : Measure α} {G : ℕ → α → ℝ≥0∞}
    (hG : ∀ j, Measurable (G j)) {D : α → ℝ≥0∞} (hD : ∫⁻ a, D a ∂ν ≠ ⊤)
    (hGD : ∀ j, G j ≤ᵐ[ν] D) {v : ℝ≥0∞} (hv : ∀ j, v ≤ ∫⁻ a, G j a ∂ν) {H : α → ℝ≥0∞}
    (hH : ∀ᵐ a ∂ν, limsup (fun j => G j a) atTop ≤ H a) : v ≤ ∫⁻ a, H a ∂ν := by
  have h1 : v ≤ limsup (fun j => ∫⁻ a, G j a ∂ν) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall hv) (by isBoundedDefault)
  exact h1.trans ((limsup_lintegral_le D hG hGD hD).trans (lintegral_mono_ae hH))

end LQGMetric.LM
