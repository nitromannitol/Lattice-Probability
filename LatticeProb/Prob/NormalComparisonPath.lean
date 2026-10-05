/-
# Normal comparison (Li--Shao): the smart path, entries, definiteness, derivative

Route: `scratch/pk/normalcompare-route.md`, item 2.  The smart path
`S_t = (1 - t) • (v • 1) + t • S` of `LatticeProb/Prob/NormalComparison.lean` joins the product
law `v • 1` at `t = 0` to the covariance `S` at `t = 1`.  This file lands the facts about the
path that the differentiation of the orthant probability (route item 3) and the final assembly
(route item 8) consume.

* Entries: the off-diagonal entry is `t * S i j`; the diagonal entry is
  `(1 - t) * v + t * S i i`; in closed form `S_t i j = c + t * (S i j - c)` with
  `c = (v • 1) i j`, affine in `t`.
* Definiteness: for `t ∈ [0,1]`, `v ≥ 0`, `S` positive semidefinite, `S_t` is positive
  semidefinite (`PosSemidef.one`, `PosSemidef.smul`, `PosSemidef.add`).  For `v > 0` and
  `t ∈ [0,1)` it is positive definite (`PosDef.one`, `PosDef.smul`, `PosDef.add_posSemidef`),
  the weight `(1 - t) v` on the identity being strictly positive.
* Derivative: each entry of the path is affine in `t`, hence `HasDerivAt` with derivative
  `S i j - (v • 1) i j` (so `S i j` off the diagonal, and `0` on the diagonal when `S` has
  constant diagonal `v`), and continuous in `t`.
-/
import Mathlib
import LatticeProb.Prob.NormalComparison

open scoped MatrixOrder Matrix

namespace LatticeProb

/-! ### Entries of the smart path -/

/-- **Closed form of the entries.**  Each entry of the smart path is affine in `t`:
`S_t i j = (v • 1) i j + t * (S i j - (v • 1) i j)`. -/
theorem normalComparisonSmartPath_apply {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (i j : Fin m) :
    normalComparisonSmartPath v S t i j =
      (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j +
        t * (S i j - (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j) := by
  simp only [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Off the diagonal the smart path has entry `t * S i j`. -/
theorem normalComparisonSmartPath_apply_of_ne {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) {i j : Fin m} (h : i ≠ j) :
    normalComparisonSmartPath v S t i j = t * S i j := by
  simp [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne h]

/-- On the diagonal the smart path interpolates linearly between `v` and `S i i`. -/
theorem normalComparisonSmartPath_apply_self {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) (i : Fin m) :
    normalComparisonSmartPath v S t i i = (1 - t) * v + t * S i i := by
  simp [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]

/-! ### Definiteness along the smart path -/

/-- For `v ≥ 0`, `S` positive semidefinite and `t ∈ [0,1]`, the smart path is positive
semidefinite. -/
theorem normalComparisonSmartPath_posSemidef {m : ℕ} {v : ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.PosSemidef) (hv : 0 ≤ v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (normalComparisonSmartPath v S t).PosSemidef := by
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hvI : (v • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hv
  exact (hvI.smul h1).add (hS.smul ht.1)

/-- For `v > 0`, `S` positive semidefinite and `t ∈ [0,1)`, the smart path is positive
definite: the identity part carries the strictly positive weight `(1 - t) v`. -/
theorem normalComparisonSmartPath_posDef {m : ℕ} {v : ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.PosSemidef) (hv : 0 < v) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    (normalComparisonSmartPath v S t).PosDef := by
  have h1 : 0 < 1 - t := by linarith [ht.2]
  have hvI : (v • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := Matrix.PosDef.one.smul hv
  exact (hvI.smul h1).add_posSemidef (hS.smul ht.1)

/-! ### Differentiating the entries along the smart path -/

/-- Each entry of the smart path is differentiable in `t`, with derivative
`S i j - (v • 1) i j`. -/
theorem hasDerivAt_normalComparisonSmartPath {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) (i j : Fin m) :
    HasDerivAt (fun s => normalComparisonSmartPath v S s i j)
      (S i j - (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j) t := by
  have h : HasDerivAt
      (fun s : ℝ => (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j +
        s * (S i j - (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j))
      (S i j - (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j) t :=
    (hasDerivAt_mul_const (S i j - (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i j)).const_add _
  convert h using 1
  funext s
  exact normalComparisonSmartPath_apply v S s i j

/-- Off the diagonal, the entry `S_t i j` has derivative `S i j`. -/
theorem hasDerivAt_normalComparisonSmartPath_of_ne {m : ℕ} (v : ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) {i j : Fin m} (h : i ≠ j) :
    HasDerivAt (fun s => normalComparisonSmartPath v S s i j) (S i j) t := by
  have h0 := hasDerivAt_normalComparisonSmartPath v S t i j
  rwa [Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero, sub_zero] at h0

/-- If `S` has diagonal `v`, each diagonal entry of the smart path is constant, with
derivative `0`. -/
theorem hasDerivAt_normalComparisonSmartPath_diag {m : ℕ} {v : ℝ}
    {S : Matrix (Fin m) (Fin m) ℝ} (hdiag : ∀ i, S i i = v) (t : ℝ) (i : Fin m) :
    HasDerivAt (fun s => normalComparisonSmartPath v S s i i) 0 t := by
  have h0 := hasDerivAt_normalComparisonSmartPath v S t i i
  have hone : (v • (1 : Matrix (Fin m) (Fin m) ℝ)) i i = v := by simp
  rwa [hone, hdiag i, sub_self] at h0

/-- Each entry of the smart path is continuous in `t`. -/
theorem continuous_normalComparisonSmartPath_apply {m : ℕ} (v : ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    Continuous fun s => normalComparisonSmartPath v S s i j :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_normalComparisonSmartPath v S t i j).continuousAt

end LatticeProb
