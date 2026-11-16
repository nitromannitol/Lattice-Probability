import LatticeProb.Analysis.Schauder.InteriorOf
import LatticeProb.Analysis.Schauder.EntryBoundOf
import LatticeProb.Analysis.Schauder.PsiBound
import LatticeProb.Analysis.Schauder.KernelChainIntegrable

/-!
# The interior Schauder estimate

A proof of `LatticeProb.Analysis.Schauder.SchauderInterior d` for every `d`, by the heat kernel. Fix
`x ∈ B₁(x₀)` and unit directions `a, b`, and cut `u` off to `w = η u` with a bump `η` that equals
`1` on `B_{3/4}(x)` and vanishes outside `B₁(x)`. The heat average
`Φ(t) = ∫ p_t(y) ∂_a∂_b w(x-y) dy` tends to `∂_a∂_b u(x)` as `t → 0⁺`, and
`|Φ(1)| ≤ (2^{d/2} + 1) K₀`. Its derivative is `∫ ∂_a∂_b p_t(y) Δw(x-y) dy`. That integral is
split at `|y| = 1/4` into a near part, bounded by the Hölder modulus of `Δu`, and a far part,
bounded through the Gaussian tail of the kernel's
derivatives up to order four. Together they give `|Φ'(t)| ≤ C (K₀ + K₁) t^{α/2-1}`, which is
integrable at `0`. Integrating it gives the entry bound `|∂_a∂_b u(x)| ≤ A K₀ + B (K₀ + K₁)`, and
summing over coordinate directions gives the norm bound.

The ingredients are `abs_dirDeriv_dirDeriv_le_of_psiBound` (the Duhamel step),
`exists_abs_integral_dirDeriv_dirDeriv_heatKernel_mul_le` (the bound on `Φ'`), the integrability of
the third and fourth derivatives of `p_t`, and `schauderInterior_of_entryBound` (entries to norm).
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- **The interior Schauder estimate at unit scale**, proved: the hypothesis
`LatticeProb.Analysis.Schauder.SchauderInterior d` of the general homogenization theorem holds in every
dimension. -/
theorem schauderInterior : LatticeProb.Analysis.Schauder.SchauderInterior d := by
  refine schauderInterior_of_entryBound fun α hα0 hα1 => ?_
  obtain ⟨CΨ, -, hΨ⟩ :=
    exists_abs_integral_dirDeriv_dirDeriv_heatKernel_mul_le (d := d) hα0.le hα1.le
  refine ⟨2 ^ ((d : ℝ) / 2) + 1, CΨ / (α / 2),
    fun u x₀ x K₀ K₁ hu hx hu0 hu1 a b ha hb => ?_⟩
  have h := abs_dirDeriv_dirDeriv_le_of_psiBound hα0
    (fun t ht a b c => integrable_dirDeriv_three_heatKernel ht a b c)
    (fun t ht a b c e => integrable_dirDeriv_four_heatKernel ht a b c e)
    hΨ u x₀ x K₀ K₁ hu hx hu0 hu1 a b ha hb
  calc |dirDeriv a (dirDeriv b u) x|
      ≤ (2 ^ ((d : ℝ) / 2) + 1) * K₀ + CΨ * (K₀ + K₁) / (α / 2) := h
    _ = (2 ^ ((d : ℝ) / 2) + 1) * K₀ + CΨ / (α / 2) * (K₀ + K₁) := by ring

end

end LatticeProb.Analysis.Schauder
