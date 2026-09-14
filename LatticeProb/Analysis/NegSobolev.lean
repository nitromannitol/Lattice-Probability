/-
Negative-order Sobolev norms on a bounded domain, in the form the divisible
sandpile percolation paper uses.

`LatticeProb.IsTestFn D φ` is `φ ∈ C_c^∞(D)`, `LatticeProb.sobolevNormSq d s φ`
is `‖φ‖_{H^s}²` written through the Fourier transform, and
`LatticeProb.negSobolevNorm d s D F` is the dual norm
`sup{|F(φ)| : φ ∈ C_c^∞(D), ‖φ‖_{H^s} ≤ 1}`, valued in `ℝ≥0∞` so that a
functional outside `H^{-s}` is not given the junk value zero.

The multiplier `(1 + (2π‖ξ‖)²)^s` is increasing in `s`, so the unit ball of
`H^{-s₀}` is contained in that of `H^{-s}` for `s₀ ≤ s`: the continuous
inclusion `H^{-s₀}(D) ⊆ H^{-s}(D)`.
-/
import Mathlib

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

namespace LatticeProb

/-- The plane `ℝ^d` of the paper's test functions. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `φ ∈ C_c^∞(D)`. -/
def IsTestFn {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- `‖φ‖_{H^s}²`, through the Fourier transform. -/
noncomputable def sobolevNormSq (d : ℕ) (s : ℝ) (φ : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : Space d, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)

/-- `‖F‖_{H^{-s}(D)}` for a functional `F` on test functions. -/
noncomputable def negSobolevNorm (d : ℕ) (s : ℝ) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ φ : Space d → ℝ,
    IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1 ∧ v = ENNReal.ofReal |F φ|}

/-- A bounded smooth domain of `ℝ^d`. -/
def IsDomain {d : ℕ} (D : Set (Space d)) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ D.Nonempty

/-- The multiplier of `H^s` is monotone in `s`. -/
theorem rpow_multiplier_mono {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (ξ : Space d) :
    (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
  have h1 : (1 : ℝ) ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
    have : (0 : ℝ) ≤ (2 * Real.pi * ‖ξ‖) ^ 2 := sq_nonneg _
    linarith
  exact Real.rpow_le_rpow_of_exponent_le h1 h

/-- The `H^s` norm is monotone in `s`. -/
theorem sobolevNormSq_mono {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (φ : Space d → ℝ) :
    sobolevNormSq d s₀ φ ≤ sobolevNormSq d s φ := by
  refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_right (rpow_multiplier_mono h ξ) (by positivity)

/-- **The continuous inclusion `H^{-s₀}(D) ⊆ H^{-s}(D)` for `s₀ ≤ s`.** -/
theorem negSobolevNorm_le {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D F ≤ negSobolevNorm d s₀ D F := by
  refine sSup_le fun v hv => ?_
  obtain ⟨φ, hφ, hnorm, rfl⟩ := hv
  exact le_sSup ⟨φ, hφ, le_trans (sobolevNormSq_mono h φ) hnorm, rfl⟩

/-- **The consumer shape.**  A functional of `H^{-s₀}(D)` norm at most `M` has
`H^{-s}(D)` norm at most `M` for `s₀ ≤ s`; equivalently the sublevel set of the
`H^{-s}` norm is contained in that of the `H^{-s₀}` norm. -/
theorem negSobolevNorm_le_of_le {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) {M : ℝ≥0∞} (hM : negSobolevNorm d s₀ D F ≤ M) :
    negSobolevNorm d s D F ≤ M :=
  le_trans (negSobolevNorm_le h D F) hM

/-- The sublevel sets of the negative-order norms are nested in `s`. -/
theorem negSobolevNorm_sublevel_subset {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s)
    (D : Set (Space d)) (M : ℝ≥0∞) :
    {F : (Space d → ℝ) → ℝ | negSobolevNorm d s₀ D F ≤ M} ⊆
      {F : (Space d → ℝ) → ℝ | negSobolevNorm d s D F ≤ M} :=
  fun _ hF => le_trans (negSobolevNorm_le h D _) hF

end LatticeProb
