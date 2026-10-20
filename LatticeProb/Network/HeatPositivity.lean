/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyHeatPositivity.lean.
-/
import LatticeProb.Network.HeatUniformization
import LatticeProb.Network.KilledHeat
import LatticeProb.Analysis.MatrixHeat

/-!
# Positivity of the killed heat matrix on a finite network

The killed heat matrix `killedHeatMatrix c m S t` is the matrix exponential of `t` times the killed
generator matrix `killedGeneratorMatrix c m S`. With the uniformization rate
`Λ = uniformizationRate G c m` and the killed uniformized transition matrix
`P = killedUniformizationMatrix G c m S`, the generator is `Λ (P - 1)`, and the Poisson
uniformization identity writes the killed heat matrix as a Poisson mixture of powers of `P`.

The file proves that `P` is substochastic, that it acts on vectors as the killed uniformized step,
that the killed generator matrix equals `Λ (P - 1)`, and that for every time `t ≥ 0` the killed heat
matrix is substochastic with strictly positive diagonal entries. These statements use the
conductance hypothesis `IsCond G c` and positive masses `m` on all of `V`.
-/

open Matrix
open scoped BigOperators NNReal Matrix Matrix.Norms.Operator

namespace LatticeProb.Network

variable {V : Type*} [Fintype V] [DecidableEq V]

section Positivity

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- The killed uniformized transition matrix: on `S` it is the uniformized transition
`uniformizedTransition G c m S` restricted to `S`, and the rows outside `S` are identity rows. -/
noncomputable def killedUniformizationMatrix (c : V → V → ℝ) (m : V → ℝ) (S : Set V) :
    Matrix V V ℝ := by
  classical
  exact Matrix.of fun v w => if v ∈ S then
    if w ∈ S then uniformizedTransition G c m S v w else 0
  else if w = v then 1 else 0

/-- The killed uniformized transition matrix is substochastic: its entries are nonnegative and its
rows sum to at most one. -/
theorem killedUniformizationMatrix_isSubstochastic {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) : IsSubstochastic (killedUniformizationMatrix G c m S) := by
  classical
  constructor
  · intro v w
    simp only [killedUniformizationMatrix, Matrix.of_apply]
    split_ifs <;> first | exact uniformizedTransition_nonneg G hc m hm S v w | positivity
  · intro v
    by_cases hv : v ∈ S
    · simp only [killedUniformizationMatrix, Matrix.of_apply, hv, ↓reduceIte]
      calc
        _ ≤ ∑ w, uniformizedTransition G c m S v w := by
          apply Finset.sum_le_sum
          intro w _
          split_ifs <;> first | exact le_rfl | exact uniformizedTransition_nonneg G hc m hm S v w
        _ = 1 := sum_uniformizedTransition G hc m S v
    · simp [killedUniformizationMatrix, hv]

open scoped Classical in
/-- The killed uniformized transition matrix acts on a vector `f`: inside `S` it averages the
zero extension of `f` to `S` against the uniformized transitions, and outside `S` it fixes `f`. -/
theorem killedUniformizationMatrix_mulVec (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (f : V → ℝ)
    (v : V) :
    (killedUniformizationMatrix G c m S *ᵥ f) v =
      if v ∈ S then ∑ w, uniformizedTransition G c m S v w * S.indicator f w else f v := by
  classical
  by_cases hv : v ∈ S
  · simp only [Matrix.mulVec, dotProduct, killedUniformizationMatrix, Matrix.of_apply,
      hv, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ S <;> simp [hw]
  · simp [Matrix.mulVec, dotProduct, killedUniformizationMatrix, hv]

/-- The killed generator matrix is the uniformization rate times `P - 1`, where `P` is the killed
uniformized transition matrix. -/
theorem killedGeneratorMatrix_eq_uniformization {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) :
    killedGeneratorMatrix c m S =
      uniformizationRate G c m • (killedUniformizationMatrix G c m S - 1) := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro w
  ext v
  rw [killedGeneratorMatrix_mulVec G hc]
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec,
    Pi.sub_apply, Matrix.one_mulVec, killedUniformizationMatrix_mulVec]
  by_cases hv : v ∈ S
  · simp only [hv, ↓reduceIte, killedMassGenerator, Set.indicator_of_mem hv]
    have h := uniformizedTransition_generator G hc m hm S
      (S.indicator (Pi.single w 1)) hv
    simp only [mul_sub] at h
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_uniformizedTransition G hc m S,
      one_mul, Set.indicator_of_mem hv] at h
    exact h.symm
  · simp [hv, killedMassGenerator]

/-- For a nonnegative time the killed heat matrix is substochastic. The Poisson mixture of powers
of the killed uniformized transition matrix is substochastic, and it equals the killed heat matrix
at rate `Λ` by `killedGeneratorMatrix_eq_uniformization`. -/
theorem killedHeatMatrix_isSubstochastic {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {t : ℝ} (ht : 0 ≤ t) :
    IsSubstochastic (killedHeatMatrix c m S t) := by
  let r : ℝ≥0 := NNReal.mk (t * uniformizationRate G c m)
    (mul_nonneg ht (uniformizationRate_pos G hc m hm).le)
  have h := (killedUniformizationMatrix_isSubstochastic G hc m hm S).poisson_exp r
  rw [poisson_exp_eq_exp_smul_sub_one] at h
  simpa only [r, NNReal.coe_mk, killedHeatMatrix,
    killedGeneratorMatrix_eq_uniformization G hc m hm S, smul_smul] using h

/-- For a nonnegative time every diagonal entry of the killed heat matrix is strictly positive. The
diagonal entries of the Poisson mixture at rate `Λ t` are at least `exp (-Λ t)`, the zero-jump
term. -/
theorem killedHeatMatrix_diagonal_pos {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) {t : ℝ} (ht : 0 ≤ t) (v : V) :
    0 < killedHeatMatrix c m S t v v := by
  let r : ℝ≥0 := NNReal.mk (t * uniformizationRate G c m)
    (mul_nonneg ht (uniformizationRate_pos G hc m hm).le)
  have h := (killedUniformizationMatrix_isSubstochastic G hc m hm S).exp_neg_le_poisson_exp_diagonal
    r v
  rw [poisson_exp_eq_exp_smul_sub_one] at h
  have hp := lt_of_lt_of_le (Real.exp_pos (-(r : ℝ))) h
  simpa only [r, NNReal.coe_mk, killedHeatMatrix,
    killedGeneratorMatrix_eq_uniformization G hc m hm S, smul_smul] using hp

end Positivity

namespace KilledPositivityExample

open SimpleGraph

attribute [local instance] HeatGeneratorExample.pathLocallyFinite

/-- On the path `0 – 1 – 2` with unit conductance, unit mass and `S = {0, 1}`, the killed
uniformized transition matrix is substochastic, so the hypotheses of
`killedUniformizationMatrix_isSubstochastic` are jointly satisfiable. -/
example :
    IsSubstochastic (killedUniformizationMatrix (pathGraph 3) (unitCond (pathGraph 3))
      (fun _ => (1 : ℝ)) {0, 1}) :=
  killedUniformizationMatrix_isSubstochastic (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) {0, 1}

/-- On the same path, the killed generator matrix is the uniformization rate times `P - 1`, so the
hypotheses of `killedGeneratorMatrix_eq_uniformization` are jointly satisfiable. -/
example (S : Set (Fin 3)) :
    killedGeneratorMatrix (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) S =
      uniformizationRate (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) •
        (killedUniformizationMatrix (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) S
          - 1) :=
  killedGeneratorMatrix_eq_uniformization (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) S

/-- On the same path, the killed heat matrix at a nonnegative time is substochastic, so the
hypotheses of `killedHeatMatrix_isSubstochastic` are jointly satisfiable. -/
example {t : ℝ} (ht : 0 ≤ t) :
    IsSubstochastic (killedHeatMatrix (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} t) :=
  killedHeatMatrix_isSubstochastic (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) {0, 1} ht

/-- On the same path, the diagonal entries of the killed heat matrix at a nonnegative time are
strictly positive, so the hypotheses of `killedHeatMatrix_diagonal_pos` are jointly satisfiable. -/
example {t : ℝ} (ht : 0 ≤ t) (v : Fin 3) :
    0 < killedHeatMatrix (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} t v v :=
  killedHeatMatrix_diagonal_pos (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) {0, 1} ht v

end KilledPositivityExample

end LatticeProb.Network
