import LatticeProb.Analysis.Sobolev.Defs
import LatticeProb.Analysis.Sobolev.ConvolutionJetsIntegrable

/-!
# The negative Sobolev dual norm and the Fourier energy of a cut-off

The Fourier `H^{-s}` energy `fourierNegEnergy d s g` of a function is the lower integral of
`(1 + (2π‖ξ‖)²)^{-s} ‖𝓕 g(ξ)‖²`. For a cut-off `χ ∈ C_c^∞(ℝ^d)` equal to one on `D`, the
`H^{-s}(D)` dual norm of the pairing `φ ↦ ∫ g φ` is bounded by the square root of the energy
of `χ g`: a test function supported in `D` does not see the difference between `g` and `χ g`,
and the Fourier duality bound pairs the energy of `χ g` with `‖φ‖_{H^s} ≤ 1`.
-/

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The Fourier `H^{-s}` energy of a function, as a lower integral (no junk value). -/
noncomputable def fourierNegEnergy (d : ℕ) (s : ℝ) (g : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : Space d, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (-s) * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2)

/-- **The `H^{-s}(D)` dual norm of an integrable pairing is bounded by a Fourier energy.** For a
cut-off `χ ∈ C_c^∞(ℝ^d)` equal to one on `D` and a function `g` integrable against every test
function, the dual norm on `D` of `φ ↦ ∫ g φ` is at most the square root of the Fourier `H^{-s}`
energy of `χ g`: on a test function supported in `D` the pairing equals `∫ (χ g) φ`, which the
Fourier duality bound controls by the energy of `χ g` times `‖φ‖_{H^s}`. -/
theorem negSobolevNorm_le_fourierNegEnergy :
    ∀ (d : ℕ) (s : ℝ) (D : Set (Space d)) (χ g : Space d → ℝ),
    IsTestFn Set.univ χ → (∀ x ∈ D, χ x = 1) →
    (∀ φ : Space d → ℝ, IsTestFn Set.univ φ → Integrable (fun y => g y * φ y)) →
    negSobolevNorm d s D (fun φ => ∫ y, g y * φ y) ≤
      fourierNegEnergy d s (fun x => χ x * g x) ^ (1 / 2 : ℝ) := by
  intro d s D χ g hχ hχD hg
  have hχg : Integrable (fun x => χ x * g x) :=
    (hg χ hχ).congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
  refine sSup_le ?_
  rintro v ⟨φ, hφ, hφn, rfl⟩
  have heq : ∫ y, g y * φ y = ∫ y, (χ y * g y) * φ y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show g y * φ y = χ y * g y * φ y
    by_cases hy : y ∈ tsupport φ
    · rw [hχD y (hφ.2.2 hy), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]
  have hb := sobolevDualityBound_of_integrable_isTestFn (-s) hχg hφ
  rw [neg_neg] at hb
  have hE : ENNReal.ofReal (|∫ y, (χ y * g y) * φ y| ^ 2)
      ≤ fourierNegEnergy d s (fun x => χ x * g x) := by
    refine hb.trans ?_
    calc sobolevNormSq d (-s) (fun x => χ x * g x) * sobolevNormSq d s φ
        ≤ sobolevNormSq d (-s) (fun x => χ x * g x) * 1 := by gcongr
      _ = fourierNegEnergy d s (fun x => χ x * g x) := by
        rw [mul_one]
        rfl
  have hsq : ENNReal.ofReal |∫ y, (χ y * g y) * φ y|
      = (ENNReal.ofReal (|∫ y, (χ y * g y) * φ y| ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  show ENNReal.ofReal |∫ y, g y * φ y| ≤ _
  rw [heq, hsq]
  exact ENNReal.rpow_le_rpow hE (by norm_num)

end LatticeProb.Sobolev
