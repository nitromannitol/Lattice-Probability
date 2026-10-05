/-
# Normal comparison (Li--Shao): the pair-sum form of the orthant derivative

Route: `scratch/pk/normalcompare-route.md`, item 3 (conclusion).  Along the smart path
`S_t = v • 1 + t • (S - v • 1)` with constant diagonal `S i i = v`, the derivative of the orthant
probability from `hasDerivAt_orthant_covDensity_path` is a full double sum over ordered pairs
`(i, j)` weighted by `B = S - v • 1`.  The diagonal weights `B i i = S i i - v` vanish and the
integrand is symmetric in `(i, j)`, so the double sum is twice the sum over pairs `i < j`, on which
`B i j = S i j`:

  `F'(t₀) = ∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t₀)`,   `I_ij(M) = ∫_{x ≤ b} (aᵢ aⱼ - M⁻¹ᵢⱼ) p_M`,

with `a = M⁻¹ x`.  This file provides

* `orthantPartial2`, the orthant integral `I_ij(M)` of the mixed second partial, and its
  symmetry `orthantPartial2_comm` for positive definite `M`;
* `sum_sum_eq_two_mul_sum_Ioi`, the finite-sum identity for a symmetric function with zero
  diagonal;
* `hasDerivAt_orthant_covDensity_path_pairs`, the pair-sum form of the derivative.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityOrthantPath

open MeasureTheory Matrix

namespace LatticeProb

/-! ### The orthant integral of the mixed second partial -/

/-- `I_ij(M) = ∫_{x ≤ b} (a_i a_j - M⁻¹ i j) density_M`, with `a = M⁻¹ *ᵥ x`. -/
noncomputable def orthantPartial2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∫ x in Set.Iic b, (((M⁻¹ *ᵥ x) i * (M⁻¹ *ᵥ x) j - M⁻¹ i j) * covDensity M x)

/-- Symmetry of `orthantPartial2` in `(i, j)` when `M` is positive definite (hence symmetric,
and so is its inverse). -/
theorem orthantPartial2_comm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (b : Fin n → ℝ) (i j : Fin n) :
    orthantPartial2 M b i j = orthantPartial2 M b j i := by
  have hsymm : M⁻¹ i j = M⁻¹ j i := by
    simpa using hM.isHermitian.inv.apply j i
  unfold orthantPartial2
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ((M⁻¹ *ᵥ x) i * (M⁻¹ *ᵥ x) j - M⁻¹ i j) * covDensity M x
    = ((M⁻¹ *ᵥ x) j * (M⁻¹ *ᵥ x) i - M⁻¹ j i) * covDensity M x
  rw [mul_comm ((M⁻¹ *ᵥ x) i), hsymm]

/-! ### A finite-sum identity -/

/-- For a symmetric function `f` on `Fin n × Fin n` with vanishing diagonal, the full double sum
is twice the sum over the pairs `i < j`. -/
theorem sum_sum_eq_two_mul_sum_Ioi {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  have h1 : ∀ i, ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
  have h3 : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h
      simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h3 i j
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if j < i then f i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
        rw [h2]
        simp only [h1]
        ring

/-! ### The pair-sum form of the derivative -/

/-- **Route item 3, pair-sum form.**  Along the smart path with constant diagonal `S i i = v`, for
`t₀ ∈ (0, 1)`,
`d/dt ∫_{x ≤ b} covDensity S_t x dx = ∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t₀)`,
where `I_ij(M) = orthantPartial2 M b i j`. -/
theorem hasDerivAt_orthant_covDensity_path_pairs {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (b : Fin n → ℝ) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (∑ i, ∑ j ∈ Finset.Ioi i,
        S i j * orthantPartial2 (normalComparisonSmartPath v S t₀) b i j) t₀ := by
  refine (hasDerivAt_orthant_covDensity_path hv hS b ht₀).congr_deriv ?_
  have hPD : (normalComparisonSmartPath v S t₀).PosDef :=
    normalComparisonSmartPath_posDef hS hv ⟨ht₀.1.le, ht₀.2⟩
  set B : Matrix (Fin n) (Fin n) ℝ := S - v • (1 : Matrix (Fin n) (Fin n) ℝ) with hB
  set I : Fin n → Fin n → ℝ := orthantPartial2 (normalComparisonSmartPath v S t₀) b with hI
  have hBii : ∀ i, B i i = 0 := fun i => by
    simp [hB, hdiag i]
  have hBij : ∀ i j, i ≠ j → B i j = S i j := fun i j h => by
    simp [hB, Matrix.one_apply_ne h]
  have hBsymm : ∀ i j, B i j = B j i := fun i j => by
    have hSs : S i j = S j i := by
      simpa using hS.isHermitian.apply j i
    by_cases h : i = j
    · subst h; rfl
    · rw [hBij i j h, hBij j i (Ne.symm h), hSs]
  have hIsymm : ∀ i j, I i j = I j i := fun i j => orthantPartial2_comm hPD b i j
  have key := sum_sum_eq_two_mul_sum_Ioi (fun i j => B i j * I i j)
    (fun i j => by rw [hBsymm i j, hIsymm i j]) (fun i => by rw [hBii i, zero_mul])
  show 1 / 2 * ∑ i, ∑ j, B i j * I i j = _
  rw [key]
  have hrw : ∀ i, ∑ j ∈ Finset.Ioi i, B i j * I i j = ∑ j ∈ Finset.Ioi i, S i j * I i j := by
    intro i
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hBij i j (ne_of_lt (Finset.mem_Ioi.mp hj))]
  simp only [hrw]
  ring

end LatticeProb
