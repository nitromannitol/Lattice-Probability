/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatPositivity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatSemigroup
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatUniformization
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatMatrixBounds

/-! Positivity and substochastic mass of the actual killed heat matrix,
proved by Poisson uniformization. -/

open Matrix
open scoped BigOperators Classical NNReal Matrix Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [DecidableEq V] (N : FiniteConductanceNetwork V)

/-- The lazy one-step matrix killed on leaving `S`. Exterior rows are identities;
the active block is the substochastic restriction of the actual lazy PMF. -/
noncomputable def killedUniformizationMatrix (m : V → ℝ) (S : Set V) : Matrix V V ℝ := by
  classical
  exact Matrix.of fun v w => if v ∈ S then
    if w ∈ S then N.uniformizedTransition m S v w else 0
  else if w = v then 1 else 0

lemma killedUniformizationMatrix_isSubstochastic (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) : MeshOnlyHeat.IsSubstochastic (N.killedUniformizationMatrix m S) := by
  classical
  constructor
  · intro v w
    simp only [killedUniformizationMatrix, Matrix.of_apply]
    split_ifs <;> first | exact N.uniformizedTransition_nonneg m hm S v w | positivity
  · intro v
    by_cases hv : v ∈ S
    · simp only [killedUniformizationMatrix, Matrix.of_apply, hv, ↓reduceIte]
      calc
        _ ≤ ∑ w, N.uniformizedTransition m S v w := by
          apply Finset.sum_le_sum
          intro w _
          split_ifs <;> first | exact le_rfl | exact N.uniformizedTransition_nonneg m hm S v w
        _ = 1 := N.sum_uniformizedTransition m S v
    · simp [killedUniformizationMatrix, hv]

lemma killedUniformizationMatrix_mulVec (m : V → ℝ) (S : Set V) (f : V → ℝ) (v : V) :
    (N.killedUniformizationMatrix m S *ᵥ f) v =
      if v ∈ S then ∑ w, N.uniformizedTransition m S v w * S.indicator f w else f v := by
  classical
  by_cases hv : v ∈ S
  · simp only [Matrix.mulVec, dotProduct, killedUniformizationMatrix, Matrix.of_apply,
      hv, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ S <;> simp [hw]
  · simp [Matrix.mulVec, dotProduct, killedUniformizationMatrix, hv]

lemma killedGeneratorMatrix_eq_uniformization (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) : N.killedGeneratorMatrix m S =
      N.uniformizationRate m • (N.killedUniformizationMatrix m S - 1) := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro w
  ext v
  rw [N.killedGeneratorMatrix_mulVec]
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec,
    Pi.sub_apply, Matrix.one_mulVec, N.killedUniformizationMatrix_mulVec]
  by_cases hv : v ∈ S
  · simp only [hv, ↓reduceIte, killedMassGenerator, Set.indicator_of_mem hv]
    have h := N.uniformizedTransition_generator m hm S
      (S.indicator (Pi.single w 1)) hv
    simp only [mul_sub] at h
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, N.sum_uniformizedTransition,
      one_mul, Set.indicator_of_mem hv] at h
    exact h.symm
  · simp [hv, killedMassGenerator]

lemma killedHeatMatrix_isSubstochastic (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {t : ℝ} (ht : 0 ≤ t) :
    MeshOnlyHeat.IsSubstochastic (N.killedHeatMatrix m S t) := by
  let r : ℝ≥0 := NNReal.mk (t * N.uniformizationRate m)
    (mul_nonneg ht (N.uniformizationRate_pos m hm).le)
  have h := (N.killedUniformizationMatrix_isSubstochastic m hm S).poisson_exp r
  rw [MeshOnlyHeat.poisson_exp_eq_exp_smul_sub_one] at h
  simpa only [r, NNReal.coe_mk, killedHeatMatrix, N.killedGeneratorMatrix_eq_uniformization m hm S,
    smul_smul] using h


lemma killedHeatMatrix_diagonal_pos (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {t : ℝ} (ht : 0 ≤ t) (v : V) : 0 < N.killedHeatMatrix m S t v v := by
  let r : ℝ≥0 := NNReal.mk (t * N.uniformizationRate m)
    (mul_nonneg ht (N.uniformizationRate_pos m hm).le)
  have h := (N.killedUniformizationMatrix_isSubstochastic m hm S).exp_neg_le_poisson_exp_diagonal r v
  rw [MeshOnlyHeat.poisson_exp_eq_exp_smul_sub_one] at h
  have hp := lt_of_lt_of_le (Real.exp_pos (-(r : ℝ))) h
  simpa only [r, NNReal.coe_mk, killedHeatMatrix, N.killedGeneratorMatrix_eq_uniformization m hm S,
    smul_smul] using hp

end BouRabeeGwynne.FiniteConductanceNetwork
