/-
# The weighted Cauchy–Schwarz at the Sobolev weights `w_s`

`DualityBound.integral_abs_mul_le_weighted` is the weighted pairing bound for a general positive
weight `w`.  This module instantiates it at the Fourier-side Sobolev weight
`w_s ξ = (1 + (2π‖ξ‖)²)^s`, giving

  `∫ ξ, ‖𝓕f ξ‖ ‖𝓕g ξ‖ ≤ (∫ ξ, w_s ξ ‖𝓕f ξ‖²)^{1/2} (∫ ξ, (w_s ξ)⁻¹ ‖𝓕g ξ‖²)^{1/2}`,

the `H^s`–`H^{−s}` pairing estimate.  Coupled with the `ofReal_integral_eq_lintegral_ofReal` bridge
and Plancherel (`SobolevDualityBound`, `DualityBound.lean`), it gives the uniform `C^m` bound
`‖f ⋆ ρ‖_∞ ≤ ‖f‖_{H^s} ‖ρ‖_{H^{−s}}` consumed by `FrechetKolmogorovMollifiedCompact`.
-/
import LatticeProb.Analysis.Sobolev.DualityBound

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The `H^s`–`H^{−s}` pairing estimate in Fourier `∫`/`√` form.** -/
theorem integral_abs_mul_le_sobolev {d : ℕ} (s : ℝ) {f g : Space d → ℝ}
    (hf : MemLp (fun ξ : Space d => Real.sqrt ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s)
      * ‖𝓕 (fun x => (f x : ℂ)) ξ‖) 2 volume)
    (hg : MemLp (fun ξ : Space d => (Real.sqrt ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s))⁻¹
      * ‖𝓕 (fun x => (g x : ℂ)) ξ‖) 2 volume) :
    ∫ ξ, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖
      ≤ (∫ ξ, (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) ^ ((1 : ℝ) / 2)
        * (∫ ξ, ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s)⁻¹
            * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have hw : ∀ ξ : Space d, 0 < (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := fun ξ =>
    Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)) s
  exact integral_abs_mul_le_weighted
    (f := fun ξ : Space d => ‖𝓕 (fun x => (f x : ℂ)) ξ‖)
    (g := fun ξ : Space d => ‖𝓕 (fun x => (g x : ℂ)) ξ‖)
    (w := fun ξ : Space d => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s) hw
    (by simpa using hf) (by simpa using hg)

end LatticeProb.Sobolev
