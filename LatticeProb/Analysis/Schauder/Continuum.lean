import LatticeProb.Analysis.Sobolev.Defs

/-!
# The continuum objects of Theorem A.1

The objects defined here are:
* the unit cube `Q = (0,1)^d`;
* the `C³` norm of a test function;
* the inverse `(−DΔ_Q)⁻¹` of the Laplacian on `Q` with zero boundary values, and its quadratic form
  `∫_Q f (−DΔ_Q)⁻¹ f`.

Test functions are LatticeProb's `Sobolev.IsTestFn D f`, i.e. `f ∈ C_c^∞(D)`.

Definitional decisions:
* `(−DΔ_Q)⁻¹` is defined spectrally. The Dirichlet Laplacian on the cube has the orthonormal
  eigenbasis `φ_k(z) = Π_i √2 sin(π k_i z_i)`, `k ∈ ℕ₊^d`, with eigenvalues `−π²|k|²`. For `f` in
  `C_c^∞(Q)`, `(−DΔ_Q)⁻¹ f = Σ_k (Dπ²|k|²)⁻¹ ⟨f, φ_k⟩ φ_k`. The series converges absolutely and
  uniformly, and it is the classical solution with zero boundary values.
* The quadratic form is `Σ_k (Dπ²|k|²)⁻¹ ⟨f, φ_k⟩²`, summed in `ℝ≥0∞`. It is finite for `f ∈ L²(Q)`,
  so the real value is honest.
* The `C³` norm is `max_{k ≤ 3} sup_z ‖D^k f(z)‖`, with the Euclidean norm on `ℝ^d`. Any other
  `C³` norm is equivalent up to a constant depending only on `d`, which the statements' constants
  absorb.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory LatticeProb
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- The continuum `ℝ^d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The unit cube `Q = (0, 1)^d` (§1.1). -/
def unitCube (d : ℕ) : Set (Euc d) := {z | ∀ i, 0 < z i ∧ z i < 1}

/-- The norm `‖f‖_{C³} = max_{k ≤ 3} sup_z ‖D^k f(z)‖` (Theorem B). -/
def c3Norm (f : Euc d → ℝ) : ℝ := ⨆ k : Fin 4, ⨆ z, ‖iteratedFDeriv ℝ k f z‖

/-- The Dirichlet eigenfunction `φ_k(z) = Π_i √2 sin(π (k_i + 1) z_i)` of the cube, indexed by
`k ∈ ℕ^d` (so that `k_i + 1 ≥ 1`). -/
def sineMode (k : Fin d → ℕ) (z : Euc d) : ℝ :=
  ∏ i, Real.sqrt 2 * Real.sin (Real.pi * ((k i : ℝ) + 1) * z i)

/-- The eigenvalue `π² |k + 1|²` of `−Δ_Q` for the mode `φ_k`. -/
def dirichletEigenvalue (k : Fin d → ℕ) : ℝ := Real.pi ^ 2 * ∑ i, ((k i : ℝ) + 1) ^ 2

/-- The sine coefficient `⟨f, φ_k⟩ = ∫_Q f φ_k`. -/
def sineCoeff (f : Euc d → ℝ) (k : Fin d → ℕ) : ℝ := ∫ z in unitCube d, f z * sineMode k z

/-- `(−DΔ_Q)⁻¹ f (z) = Σ_k (D π²|k|²)⁻¹ ⟨f, φ_k⟩ φ_k(z)`, the solution of `−DΔu = f` in `Q` with
zero boundary values (Theorem A.1). -/
def dirichletInverse (D : ℝ) (f : Euc d → ℝ) (z : Euc d) : ℝ :=
  ∑' k : Fin d → ℕ, (D * dirichletEigenvalue k)⁻¹ * sineCoeff f k * sineMode k z

/-- The quadratic form `∫_Q f (−DΔ_Q)⁻¹ f = Σ_k (D π²|k|²)⁻¹ ⟨f, φ_k⟩²` (Theorems B (ii) and A.1).
-/
def dirichletForm (D : ℝ) (f : Euc d → ℝ) : ℝ :=
  (∑' k : Fin d → ℕ, ENNReal.ofReal ((D * dirichletEigenvalue k)⁻¹ * sineCoeff f k ^ 2)).toReal

end

end LatticeProb.Analysis.Schauder
