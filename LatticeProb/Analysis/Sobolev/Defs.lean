/-
Test functions, the Fourier-side Sobolev norms of negative order, and the
bounded-domain predicate, in the form the continuum membrane arguments use.

The objects are:

- `Space d` is `ℝ^d` as a Euclidean space.
- `IsTestFn D φ` is `φ ∈ C_c^∞(D)`.
- `sobolevNormSq d s φ` is `‖φ‖_{H^s}²`, written through the Fourier transform
  as `∫ (1 + (2π‖ξ‖)²)^s ‖𝓕φ(ξ)‖² dξ`.  Mathlib's `𝓕` uses the character
  `e^{-2πi⟪x,ξ⟫}`, so the frequency variable of the paper is `2π` times
  Mathlib's and the factor appears explicitly in the multiplier.  The value
  lives in `ℝ≥0∞`, so a test function outside `H^s` is not given the junk
  value zero.
- `negSobolevNorm d s D F` is `‖F‖_{H^{-s}(D)} = sup{|F(φ)| : φ ∈ C_c^∞(D),
  ‖φ‖_{H^s(D)} ≤ 1}`, again in `ℝ≥0∞`, for a functional `F` on test functions.
- `IsDomain D` records that `D` is a bounded nonempty open set.
-/
import Mathlib

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- `ℝ^d` as a Euclidean space. -/
abbrev Space (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- `φ ∈ C_c^∞(D)`. -/
def IsTestFn {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- `‖φ‖_{H^s}²`, through the Fourier transform. -/
noncomputable def sobolevNormSq (d : ℕ) (s : ℝ) (φ : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : Space d, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)

/-- The high-frequency part of `‖φ‖_{H^s}²`: the same integral restricted to
frequencies `‖ξ‖ > Λ`.  This is the piece the frequency truncation of the
compactness argument discards. -/
noncomputable def sobolevNormSqHigh (d : ℕ) (s : ℝ) (Λ : ℝ) (φ : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖}, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)

/-- `‖F‖_{H^{-s}(D)}` for a functional `F` on test functions. -/
noncomputable def negSobolevNorm (d : ℕ) (s : ℝ) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ φ : Space d → ℝ,
    IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1 ∧ v = ENNReal.ofReal |F φ|}

/-- A bounded smooth domain of `ℝ^d`: the paper's `D` in `H^{-s}(D)`.  Only
boundedness, openness, and nonemptiness are used by the statements below. -/
def IsDomain {d : ℕ} (D : Set (Space d)) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ D.Nonempty

end LatticeProb.Sobolev
