/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentAbs at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_add_le and eLpNorm_eq_zero_iff no longer take measurability arguments. -/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Identification of a GMC limit with a martingale approximation, abstract step (P2-GMCID, D67)

Berestycki, *An elementary approach to Gaussian multiplicative chaos* (arXiv:1506.09113,
Electron. Commun. Probab. 22 (2017)), §4 "Uniqueness of the limit", proof of Thm 1.1
(uniqueness), `main.tex` l. 680–700:

> `E(μ_ε(S) | 𝓕_n) = μ^n_ε(S)` … the right hand side converges … to `μ^n(S)` … However, we have
> shown that `μ_ε(S)` converges in `L¹(P)` to `μ(S)`, and hence the above right hand side is in
> fact equal to the conditional expectation of `μ(S)` … We deduce `μ^n(S) = E(μ(S) | 𝓕_n)`
> almost surely, and hence `μ'(S) = μ(S)`.

`ae_eq_condExp_of_tendsto_L1` is the first deduction, `ae_tendsto_of_tendsto_L1_condExp` adds
Lévy's upward theorem (mathlib `Integrable.tendsto_ae_condExp`), the step "hence `μ' = μ`" (with
`μ(S)` measurable with respect to `𝓕_∞`, as Berestycki notes in the commented proof, l. 706).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- `L¹` convergence `Y_k → Y` passes to conditional expectations. -/
lemma tendsto_eLpNorm_condExp_sub {m : MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} {Yl : Ω → ℝ}
    (hYi : ∀ k, Integrable (Y k) μ) (hYl : Integrable Yl μ)
    (hY : Tendsto (fun k => eLpNorm (Y k - Yl) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (μ[Y k | m] - μ[Yl | m]) 1 μ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hY (fun _ => zero_le)
    fun k => ?_
  have h := condExp_sub (m := m) (hYi k) hYl
  rw [← eLpNorm_congr_ae h]
  exact eLpNorm_condExp_le_eLpNorm _ le_rfl

/-- **Berestycki §4, first step**: if `Y_k → Y` in `L¹` and `E(Y_k | 𝓕) → Z` in `L¹`, then
`Z = E(Y | 𝓕)` a.s. -/
theorem ae_eq_condExp_of_tendsto_L1 {m : MeasurableSpace Ω} {Y : ℕ → Ω → ℝ} {Yl Z : Ω → ℝ}
    (hYi : ∀ k, Integrable (Y k) μ) (hYl : Integrable Yl μ)
    (hY : Tendsto (fun k => eLpNorm (Y k - Yl) 1 μ) atTop (𝓝 0))
    (hZm : AEStronglyMeasurable[m0] Z μ)
    (hZ : Tendsto (fun k => eLpNorm (μ[Y k | m] - Z) 1 μ) atTop (𝓝 0)) :
    Z =ᵐ[μ] μ[Yl | m] := by
  have h1 := tendsto_eLpNorm_condExp_sub (m := m) hYi hYl hY
  have hle : ∀ k, eLpNorm (Z - μ[Yl | m]) 1 μ ≤
      eLpNorm (μ[Y k | m] - Z) 1 μ + eLpNorm (μ[Y k | m] - μ[Yl | m]) 1 μ := by
    intro k
    have e : Z - μ[Yl | m] = -(μ[Y k | m] - Z) + (μ[Y k | m] - μ[Yl | m]) := by abel
    rw [e]
    refine (eLpNorm_add_le le_rfl).trans ?_
    · rw [eLpNorm_neg]
  have h0 : eLpNorm (Z - μ[Yl | m]) 1 μ = 0 := by
    refine le_antisymm (ge_of_tendsto (by simpa using hZ.add h1) (Eventually.of_forall hle))
      zero_le
  rw [eLpNorm_eq_zero_iff one_ne_zero] at h0
  filter_upwards [h0] with ω hω
  simpa [sub_eq_zero] using hω

end GMCIdent
end LQGMetric
