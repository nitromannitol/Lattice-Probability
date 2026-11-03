/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Common.Basic at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Basic conventions for the quantum zipper formalization

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797.  This file fixes the upper half-plane `H` (as a subset of `ℂ`), the
constants `Q = 2/γ + γ/2` and `χ = 2/√κ − √κ/2`, test functions, and dyadic rounding.
See `FOUNDATIONS.md` for the overall design.
-/

noncomputable section

open MeasureTheory

namespace QuantumZipper

/-- The open upper half-plane `ℍ = {z : Im z > 0}`, as a subset of `ℂ`. -/
def H : Set ℂ := {z | 0 < z.im}

/-- The closed upper half-plane `{z : Im z ≥ 0}`. -/
def Hbar : Set ℂ := {z | 0 ≤ z.im}

theorem isOpen_H : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

theorem isClosed_Hbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im

theorem H_subset_Hbar : H ⊆ Hbar := fun z (hz : 0 < z.im) => show 0 ≤ z.im from hz.le

/-- The LQG constant `Q = 2/γ + γ/2`. -/
def Qc (γ : ℝ) : ℝ := 2 / γ + γ / 2

/-- The imaginary-geometry constant `χ = 2/√κ − √κ/2`. -/
def chiC (κ : ℝ) : ℝ := 2 / Real.sqrt κ - Real.sqrt κ / 2

/-- With `γ = √κ`, the constant `Q` reads `2/√κ + √κ/2`. -/
theorem Qc_sqrt (κ : ℝ) : Qc (Real.sqrt κ) = 2 / Real.sqrt κ + Real.sqrt κ / 2 := rfl

/-- Smooth (`C^∞`, not analytic) compactly supported real test functions on `ℂ` whose
topological support lies in `U`. -/
def TestFun (U : Set ℂ) : Type :=
  {ρ : ℂ → ℝ // ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U}

/-- Test functions of total mass zero; pairings with them see a field modulo additive
constants. -/
def TestFun0 (U : Set ℂ) : Type := {ρ : TestFun U // ∫ z, ρ.1 z = 0}

/-- Round down to the dyadic grid of mesh `2^{-n}`. -/
def dyadicRound (n : ℕ) (x : ℝ) : ℝ := ⌊(2 : ℝ) ^ n * x⌋ / (2 : ℝ) ^ n

/-- Round both coordinates down to the dyadic grid of mesh `2^{-n}`. -/
def dyadicRoundC (n : ℕ) (z : ℂ) : ℂ := ⟨dyadicRound n z.re, dyadicRound n z.im⟩

/-- The regularization radii `2^{-k}`. -/
def radius (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ k

theorem radius_pos (k : ℕ) : 0 < radius k := by
  unfold radius; positivity

end QuantumZipper
