/-
# The pair marginal of the Gaussian density at a corner point

Li--Shao normal comparison, route item 5 (`scratch/pk/normalcompare-route.md`).  The boundary
term of the covariance derivative is
`D = ∫_{x'' ≤ b''} covDensity S (pairCorner σ b x'') dx''`
(`LatticeProb/Prob/GaussCovDensityOrthant.lean`).  This file bounds it by the density of the pair
`(Y_{σ 0}, Y_{σ 1})` at `(b (σ 0), b (σ 1))`.

Route.
1. `pairSumEquiv m : Fin 2 ⊕ Fin m ≃ Fin (m + 2)` (`inl k ↦ k`, `inr k ↦ k.succ.succ`), and
   `e = (pairSumEquiv m).trans σ`, which sends `inl 0 ↦ σ 0`, `inl 1 ↦ σ 1`,
   `inr k ↦ σ k.succ.succ`.  Then `pairCorner σ b x'' ∘ e = Sum.elim ![b (σ 0), b (σ 1)] x''`.
2. `covDensity S z = covDensityOn (S.submatrix e e) (z ∘ e)`
   (`covDensity_eq_covDensityOn`, `covDensityOn_submatrix_equiv`), and
   `S.submatrix e e = fromBlocks A B Bᵀ D` with the upper left block `A` equal to the `2 × 2`
   matrix `!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0), S (σ 1) (σ 1)]` (symmetry of `S`);
   it is positive definite as a principal submatrix of `S`.
3. `integral_covDensityOn_fromBlocks` (Schur-complement marginalisation,
   `LatticeProb/Prob/GaussCovDensitySchur.lean`) integrates out the `x''` block:
   `∫ covDensity S (pairCorner σ b x'') dx'' = covDensity A (b (σ 0), b (σ 1))`.
4. The right side is positive (`covDensity_pos`), and an integral of a non-integrable function
   vanishes (`integral_undef`), so the integrand is integrable; the orthant integral is then at
   most the full integral (`setIntegral_le_integral`, the integrand being positive).
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensitySchur
import LatticeProb.Prob.NormalComparisonOrthantPair
import LatticeProb.Prob.GaussCovDensityTwo

open MeasureTheory Matrix

namespace LatticeProb

/-! ### The index equivalence -/

/-- The index equivalence `Fin 2 ⊕ Fin m ≃ Fin (m + 2)` with `inl k ↦ k`, `inr k ↦ k.succ.succ`. -/
def pairSumEquiv (m : ℕ) : Fin 2 ⊕ Fin m ≃ Fin (m + 2) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 2 m))

/-- The image of `inl k` under `pairSumEquiv m` has underlying natural number `k`. -/
theorem pairSumEquiv_inl (m : ℕ) (k : Fin 2) : (pairSumEquiv m (Sum.inl k) : ℕ) = k := by
  simp [pairSumEquiv]

/-- The image of `inr k` under `pairSumEquiv m` is `k.succ.succ`. -/
theorem pairSumEquiv_inr (m : ℕ) (k : Fin m) : pairSumEquiv m (Sum.inr k) = k.succ.succ := by
  apply Fin.ext
  simp [pairSumEquiv]

/-- The image of `inl 0` under `pairSumEquiv m` is `0`. -/
theorem pairSumEquiv_inl_zero (m : ℕ) : pairSumEquiv m (Sum.inl 0) = 0 := by
  apply Fin.ext
  rw [pairSumEquiv_inl]
  rfl

/-- The image of `inl 1` under `pairSumEquiv m` is `1`. -/
theorem pairSumEquiv_inl_one (m : ℕ) : pairSumEquiv m (Sum.inl 1) = 1 := by
  apply Fin.ext
  rw [pairSumEquiv_inl]
  rfl

/-! ### Reindexing the density along the pair equivalence -/

/-- Composing the corner point with the coordinate bijection `(pairSumEquiv m).trans σ` gives the
pair `![b (σ 0), b (σ 1)]` followed by `x''`. -/
private theorem pairCorner_comp_equiv {m : ℕ} (σ : Equiv.Perm (Fin (m + 2)))
    (b : Fin (m + 2) → ℝ) (x'' : Fin m → ℝ) :
    pairCorner σ b x'' ∘ ((pairSumEquiv m).trans σ) = Sum.elim ![b (σ 0), b (σ 1)] x'' := by
  funext i
  rcases i with k | k
  · fin_cases k
    · simp [pairSumEquiv_inl_zero, pairCorner_apply_zero]
    · simp [pairSumEquiv_inl_one, pairCorner_apply_one]
  · simp [pairSumEquiv_inr, pairCorner_apply_succ_succ]

/-- A symmetric matrix indexed by a sum, pulled back along `e : κ ⊕ ι ≃ n`, is the block matrix
of its four `submatrix` blocks, the lower left one being the transpose of the upper right one. -/
private theorem submatrix_equiv_eq_fromBlocks {κ ι n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.IsHermitian) (e : κ ⊕ ι ≃ n) :
    S.submatrix e e = Matrix.fromBlocks (S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
      (S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)) (S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))ᵀ
      (S.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  have hsymm : ∀ i j, S j i = S i j := fun i j => by simpa using hS.apply i j
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact hsymm _ _
  · rfl

/-- The upper left block of the reindexed covariance is the `2 × 2` covariance matrix of the
pair `(Y_{σ 0}, Y_{σ 1})`. -/
private theorem submatrix_inl_pairEquiv {m : ℕ} (S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
    (σ : Equiv.Perm (Fin (m + 2))) :
    S.submatrix (((pairSumEquiv m).trans σ) ∘ Sum.inl) (((pairSumEquiv m).trans σ) ∘ Sum.inl)
      = (!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0), S (σ 1) (σ 1)] :
          Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSumEquiv_inl_zero, pairSumEquiv_inl_one]

/-- The `2 × 2` covariance matrix of the pair `(Y_{σ 0}, Y_{σ 1})` is positive definite. -/
theorem posDef_pairMatrix {m : ℕ} {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hS : S.PosDef)
    (σ : Equiv.Perm (Fin (m + 2))) :
    (!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0), S (σ 1) (σ 1)] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [← submatrix_inl_pairEquiv S σ]
  exact hS.submatrix (((pairSumEquiv m).trans σ).injective.comp Sum.inl_injective)

/-- The density at the corner point is the density of the reindexed block matrix at
`(![b (σ 0), b (σ 1)], x'')`, whose upper left block is the `2 × 2` matrix of the pair. -/
private theorem exists_blocks {m : ℕ} {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}
    (hS : S.PosDef) (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) :
    ∃ (B : Matrix (Fin 2) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ),
      (Matrix.fromBlocks (!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0), S (σ 1) (σ 1)] :
          Matrix (Fin 2) (Fin 2) ℝ) B Bᵀ D).PosDef ∧
      ∀ x'' : Fin m → ℝ, covDensity S (pairCorner σ b x'') =
        covDensityOn (Matrix.fromBlocks (!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0),
          S (σ 1) (σ 1)] : Matrix (Fin 2) (Fin 2) ℝ) B Bᵀ D)
          (Sum.elim ![b (σ 0), b (σ 1)] x'') := by
  set e : Fin 2 ⊕ Fin m ≃ Fin (m + 2) := (pairSumEquiv m).trans σ with he
  refine ⟨S.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr), S.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr), ?_⟩
  have hblk := submatrix_equiv_eq_fromBlocks hS.isHermitian e
  rw [he, submatrix_inl_pairEquiv S σ] at hblk
  refine ⟨?_, fun x'' => ?_⟩
  · rw [← hblk]
    exact hS.submatrix e.injective
  · have h := covDensityOn_submatrix_equiv e S (pairCorner σ b x'')
    rw [he, pairCorner_comp_equiv] at h
    rw [covDensity_eq_covDensityOn, ← h, hblk]

/-! ### The marginal -/

/-- Marginalisation: integrating the density over the other coordinates at the corner gives the
density of the pair (a `2 × 2` Gaussian density at `(b (σ 0), b (σ 1))`). -/
theorem integral_covDensity_pairCorner {m : ℕ} {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}
    (hS : S.PosDef) (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) :
    ∫ x'' : Fin m → ℝ, covDensity S (pairCorner σ b x'')
      = covDensity (!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0), S (σ 1) (σ 1)] :
          Matrix (Fin 2) (Fin 2) ℝ) ![b (σ 0), b (σ 1)] := by
  obtain ⟨B, D, hP, hden⟩ := exists_blocks hS σ b
  simp_rw [hden]
  rw [integral_covDensityOn_fromBlocks _ B D hP, ← covDensity_eq_covDensityOn]

/-- The density at the corner point is integrable in the remaining coordinates. -/
theorem integrable_covDensity_pairCorner {m : ℕ}
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hS : S.PosDef)
    (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) :
    Integrable (fun x'' : Fin m → ℝ => covDensity S (pairCorner σ b x'')) := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_covDensity_pairCorner hS σ b] at h0
  exact (covDensity_pos (posDef_pairMatrix hS σ) _).ne' h0

/-- The boundary integral over the orthant is at most the pair density. -/
theorem integral_Iic_pairCorner_covDensity_le {m : ℕ}
    {S : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hS : S.PosDef)
    (σ : Equiv.Perm (Fin (m + 2))) (b : Fin (m + 2) → ℝ) :
    ∫ x'' in Set.Iic (fun k : Fin m => b (σ k.succ.succ)), covDensity S (pairCorner σ b x'')
      ≤ covDensity (!![S (σ 0) (σ 0), S (σ 0) (σ 1); S (σ 1) (σ 0), S (σ 1) (σ 1)] :
          Matrix (Fin 2) (Fin 2) ℝ) ![b (σ 0), b (σ 1)] := by
  rw [← integral_covDensity_pairCorner hS σ b]
  exact setIntegral_le_integral (integrable_covDensity_pairCorner hS σ b)
    (Filter.Eventually.of_forall fun x'' => (covDensity_pos hS _).le)

end LatticeProb
