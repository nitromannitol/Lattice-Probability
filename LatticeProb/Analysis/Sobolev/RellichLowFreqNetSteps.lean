/-
# Low-frequency bounds for the Rellich net

`rkLowFreqNet` (`RellichLowFreqNet.lean`) is the low-frequency compactness step of the
Rellich–Kondrachov argument: the low-frequency part of the `H^s(D)` unit ball is covered by
finitely many `H^{s₀}`-balls with test-function centres.  This file proves two bounds on that
low-frequency set:

* `sobolevNormSqLow_le_sobolevNormSq`: for `s₀ ≤ s` the low-frequency part of the
  `H^{s₀}` norm is at most the full `H^s` norm, so the low-frequency set is
  `H^{s₀}`-bounded;
* `sobolevNormSq_le_of_lowFreq`: consequently a low-frequency test function in the
  `H^s` unit ball has `H^{s₀}` norm at most `1 + δ/2`.
-/
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.RellichNet
import LatticeProb.Analysis.Sobolev.RellichMollify

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-! ### Bounded supporting lemmas -/

/-- **The low-frequency part is dominated by the full higher-order norm.**  For
`s₀ ≤ s` the weight `(1 + (2π‖ξ‖)²)^{s₀}` is at most `(1 + (2π‖ξ‖)²)^s`, so the
low-frequency integral at `s₀` is at most the full `H^s` norm. -/
theorem sobolevNormSqLow_le_sobolevNormSq {d : ℕ} {s₀ s Λ : ℝ} (hss : s₀ ≤ s)
    (φ : Space d → ℝ) :
    sobolevNormSqLow d s₀ Λ φ ≤ sobolevNormSq d s φ := by
  have hpoint : ∀ ξ : Space d,
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
        ≤ ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
          * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right (sq_nonneg _)) hss
  unfold sobolevNormSqLow sobolevNormSq
  calc ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖}ᶜ,
        ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖}ᶜ,
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
        lintegral_mono hpoint
    _ ≤ ∫⁻ ξ : Space d,
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        simpa using lintegral_mono_set (μ := volume)
          (f := fun ξ : Space d => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2))
          (Set.subset_univ ({ξ : Space d | Λ < ‖ξ‖}ᶜ))

/-- **The low-frequency set is `H^{s₀}`-bounded.**  A test function in the `H^s`
unit ball whose high-frequency `H^{s₀}` content is at most `δ/2` has `H^{s₀}` norm
at most `1 + δ/2`: the low-frequency part is at most the full `H^s` norm
(`sobolevNormSqLow_le_sobolevNormSq`) and the parts add up. -/
theorem sobolevNormSq_le_of_lowFreq {d : ℕ} {s₀ s Λ δ : ℝ} (hss : s₀ ≤ s)
    {φ : Space d → ℝ} (hφ : sobolevNormSq d s φ ≤ 1)
    (hhigh : sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (δ / 2)) :
    sobolevNormSq d s₀ φ ≤ 1 + ENNReal.ofReal (δ / 2) := by
  calc sobolevNormSq d s₀ φ
      = sobolevNormSqLow d s₀ Λ φ + sobolevNormSqHigh d s₀ Λ φ :=
        (sobolevNormSqLow_add_high d s₀ Λ φ).symm
    _ ≤ sobolevNormSq d s φ + ENNReal.ofReal (δ / 2) :=
        add_le_add (sobolevNormSqLow_le_sobolevNormSq hss φ) hhigh
    _ ≤ 1 + ENNReal.ofReal (δ / 2) := add_le_add hφ le_rfl

end LatticeProb.Sobolev
