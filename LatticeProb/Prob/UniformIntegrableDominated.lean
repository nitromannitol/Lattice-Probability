/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Uniform integrability from domination and from summable increments

* `uniformIntegrable_of_ae_le`: a family of real functions dominated almost everywhere by one integrable function
  is uniformly integrable (exponent `p = 1`).
* `exists_integrable_dominating_of_summable`: if the `L¹` norms of the increments `f (n + 1) - f n` of a sequence
  of integrable functions are summable, the sequence is dominated by one integrable function, namely
  `‖f 0‖ + ∑' n, ‖f (n + 1) - f n‖`.
* `uniformIntegrable_of_summable_integral_norm_sub`: such a sequence is uniformly integrable.
* `UniformIntegrable.comp_index`: every reindexed subfamily of a uniformly integrable family is uniformly
  integrable.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace LatticeProb.Prob

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- A family of real functions dominated almost everywhere by a single integrable function is uniformly
integrable. -/
theorem uniformIntegrable_of_ae_le {ι : Type*} {f : ι → α → ℝ} {G : α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hG : Integrable G μ)
    (hle : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ G x) : UniformIntegrable f 1 μ := by
  obtain ⟨hGu, B, hB⟩ :=
    uniformIntegrable_const (ι := ι) le_rfl ENNReal.one_ne_top (memLp_one_iff_integrable.2 hG)
  have hle' : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ ‖G x‖ := fun i =>
    (hle i).mono fun x hx => hx.trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)
  have hle'' : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖(fun _ : ι => G) i ·‖ₑ) := fun i =>
    (hle' i).mono fun x hx => by
      show ‖f i x‖ₑ ≤ ‖G x‖ₑ
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
  exact ⟨hGu.ae_mono hf hle'', B, fun i => (eLpNorm_mono_ae (hf i) (hle' i)).trans (hB i)⟩

/-- If the `L¹` norms of the increments of a sequence of integrable real functions are summable, then the
sequence is dominated almost everywhere by one integrable function. -/
theorem exists_integrable_dominating_of_summable {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable fun n => ∫ x, ‖f (n + 1) x - f n x‖ ∂μ) :
    ∃ G : α → ℝ, Integrable G μ ∧ ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ G x := by
  have hd : ∀ n, Integrable (fun x => f (n + 1) x - f n x) μ := fun n => (hf (n + 1)).sub (hf n)
  set S : α → ℝ≥0∞ := fun x => ∑' n, ‖f (n + 1) x - f n x‖ₑ with hSdef
  have hSm : AEMeasurable S μ := AEMeasurable.tsum fun n => (hd n).aestronglyMeasurable.enorm
  have hint : ∀ n, ∫⁻ x, ‖f (n + 1) x - f n x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ‖f (n + 1) x - f n x‖ ∂μ) :=
    fun n => (ofReal_integral_norm_eq_lintegral_enorm (hd n)).symm
  have hS : ∫⁻ x, S x ∂μ ≠ ∞ := by
    rw [hSdef, lintegral_tsum fun n => (hd n).aestronglyMeasurable.enorm]
    simp only [hint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun x => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨fun x => ‖f 0 x‖ + (S x).toReal, (hf 0).norm.add (integrable_toReal_of_lintegral_ne_top hSm hS),
    fun n => ?_⟩
  filter_upwards [ae_lt_top' hSm hS] with x hx
  have hsum : ∑ k ∈ Finset.range n, ‖f (k + 1) x - f k x‖ ≤ (S x).toReal := by
    have heq : ∑ k ∈ Finset.range n, ‖f (k + 1) x - f k x‖ =
        (∑ k ∈ Finset.range n, ‖f (k + 1) x - f k x‖ₑ).toReal := by
      rw [ENNReal.toReal_sum fun k _ => enorm_ne_top]
      simp only [toReal_enorm]
    rw [heq]
    exact ENNReal.toReal_mono hx.ne (ENNReal.sum_le_tsum _)
  have htel : f n x = f 0 x + ∑ k ∈ Finset.range n, (f (k + 1) x - f k x) := by
    rw [Finset.sum_range_sub (fun k => f k x)]
    ring
  rw [htel]
  exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans hsum))

/-- A sequence of integrable real functions whose increments have summable `L¹` norms is uniformly integrable. -/
theorem uniformIntegrable_of_summable_integral_norm_sub {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable fun n => ∫ x, ‖f (n + 1) x - f n x‖ ∂μ) : UniformIntegrable f 1 μ := by
  obtain ⟨G, hG, hle⟩ := exists_integrable_dominating_of_summable hf hs
  exact uniformIntegrable_of_ae_le (fun n => (hf n).aestronglyMeasurable) hG hle

/-- Every reindexed subfamily of a uniformly integrable family is uniformly integrable. -/
theorem UniformIntegrable.comp_index {ι κ β : Type*} [NormedAddCommGroup β] {p : ℝ≥0∞} {f : ι → α → β}
    (hf : UniformIntegrable f p μ) (n : κ → ι) : UniformIntegrable (fun k => f (n k)) p μ :=
  ⟨hf.1.comp n, hf.2.imp fun _ hC k => hC (n k)⟩

end LatticeProb.Prob
