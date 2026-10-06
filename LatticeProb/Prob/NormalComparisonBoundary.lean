/-
Normal comparison: covariance-entry bounds.

The smart-path entries, definiteness and derivatives are imported from
NormalComparisonPath. The arbitrary-dimensional covariance-entry bound and
its consequence along the smart path are retained here.
-/
import LatticeProb.Prob.NormalComparisonPath

open scoped MatrixOrder
open Matrix

namespace LatticeProb

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
