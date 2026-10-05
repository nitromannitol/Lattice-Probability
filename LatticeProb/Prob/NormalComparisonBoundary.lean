/-
# Normal comparison (Li--Shao): the covariance boundary and differentiation step

Route: `scratch/pk/normalcompare-route.md`, items 2 and 5.  `LatticeProb/Prob/NormalComparison.lean`
lands the smart path `S_t = (1 - t) • (v • 1) + t • S` with its endpoints and diagonal, and the
bivariate density bound `bivariateGaussDensity_le`.  This file lands the next deterministic step:

* the entries of the smart path, its positive semidefiniteness and positive definiteness, and the
  differentiation of each entry in `t` (the differentiation of the covariance along the path);
* the boundary covariance bound: a positive semidefinite matrix with constant diagonal `v` has
  every entry bounded by `v` in absolute value, and consequently so does the smart path.  This is
  the bound that keeps the correlation `t * S i j / v` inside `(-1, 1)` along the path, which is
  what the boundary integral consumes.

No `External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparison

open scoped MatrixOrder
open Matrix

namespace LatticeProb

/-! ### The entries of the smart path -/

/-- **Closed form of the entries.**  Each entry is affine in `t`:
`S_t i j = (v • 1) i j + t * (S i j - (v • 1) i j)`. -/
theorem normalComparisonSmartPath_apply {m : ℕ} (v : ℝ) (S : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) (i j : Fin m) :
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

/-- For `v > 0`, `S` positive semidefinite and `t ∈ [0,1)`, the smart path is positive definite:
the identity part carries the strictly positive weight `(1 - t) v`. -/
theorem normalComparisonSmartPath_posDef {m : ℕ} {v : ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.PosSemidef) (hv : 0 < v) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    (normalComparisonSmartPath v S t).PosDef := by
  have h1 : 0 < 1 - t := by linarith [ht.2]
  have hvI : (v • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := Matrix.PosDef.one.smul hv
  exact (hvI.smul h1).add_posSemidef (hS.smul ht.1)

/-! ### Differentiating the entries along the smart path -/

/-- **The differentiation step.**  Each entry of the smart path is differentiable in `t`, with
derivative `S i j - (v • 1) i j`. -/
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

/-! ### The boundary covariance bound -/

/-- The quadratic form of a positive semidefinite real matrix at `e_i + s • e_j` with `i ≠ j` is
nonnegative: `0 ≤ S i i + s (S i j + S j i) + s² S j j`. -/
private theorem quad_pair_nonneg {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    {i j : Fin n} (s : ℝ) :
    0 ≤ S i i + s * (S i j + S j i) + s ^ 2 * S j j := by
  have h := hS.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j s)
  simp [dotProduct_add, mulVec_add] at h
  linarith

/-- **The boundary covariance bound.**  A positive semidefinite matrix with constant diagonal `v`
has every entry bounded by `v` in absolute value. -/
theorem abs_apply_le_of_posSemidef_diag {n : ℕ} {v : ℝ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hv : 0 < v) (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v) (i j : Fin n) : |S i j| ≤ v := by
  by_cases hij : i = j
  · subst hij
    rw [hdiag i, abs_of_pos hv]
  · have hsym : S j i = S i j := by
      simpa using hS.isHermitian.apply i j
    have h1 := quad_pair_nonneg hS (i := i) (j := j) 1
    have h2 := quad_pair_nonneg hS (i := i) (j := j) (-1)
    rw [hdiag i, hdiag j, hsym] at h1 h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The covariance bound along the smart path.**  For `v > 0`, `S` positive semidefinite with
diagonal `v` and `t ∈ [0,1]`, every entry of `S_t` is bounded by `v`.  This is what keeps the
correlation `t * S i j / v` inside `(-1, 1)`. -/
theorem abs_normalComparisonSmartPath_apply_le {m : ℕ} {v : ℝ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hv : 0 < v) (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin m) :
    |normalComparisonSmartPath v S t i j| ≤ v :=
  abs_apply_le_of_posSemidef_diag hv (normalComparisonSmartPath_posSemidef hS hv.le ht)
    (fun i => normalComparisonSmartPath_diag hdiag t i) i j

end LatticeProb
