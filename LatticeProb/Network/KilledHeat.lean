/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyHeatSemigroup.lean.
-/
import LatticeProb.Network.HeatGenerator
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The killed heat semigroup on a finite network

The killed mass generator `killedMassGenerator G c m S` of a finite network is written as a
matrix, `killedGeneratorMatrix c m S`. Its matrix exponential `killedHeatMatrix c m S t` gives the
killed heat flow `killedHeatFlow c m S f t` of the zero extension of a datum `f` to `S`.

The file proves that the killed heat matrices satisfy the semigroup law in the time variable, that
the killed heat flow starts at the zero extension of its datum, and that it solves the killed heat
equation `d/dt u = killedMassGenerator G c m S u`.
-/

open Matrix
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace LatticeProb.Network

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The diagonal projection onto the vertex set `S`. -/
noncomputable def killingProjection (S : Set V) : Matrix V V ℝ :=
  Matrix.diagonal (S.indicator (fun _ => 1))

/-- Applying the projection onto `S` to a vector gives its zero extension to `S`. -/
theorem killingProjection_mulVec (S : Set V) (f : V → ℝ) :
    killingProjection S *ᵥ f = S.indicator f := by
  ext v
  by_cases hv : v ∈ S <;> simp [killingProjection, Matrix.mulVec_diagonal, hv]

/-- The matrix of the killed mass generator with conductance `c` and mass `m`: the zero extension
to `S`, the generator `m⁻¹ (c - diag (∑ w, c v w))`, and the restriction to `S`. -/
noncomputable def killedGeneratorMatrix (c : V → V → ℝ) (m : V → ℝ) (S : Set V) :
    Matrix V V ℝ :=
  killingProjection S * Matrix.diagonal (fun v => (m v)⁻¹) *
    (Matrix.of c - Matrix.diagonal (fun v => ∑ w, c v w)) * killingProjection S

section Heat

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- The killed generator matrix acts on vectors as the killed mass generator. -/
theorem killedGeneratorMatrix_mulVec {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ) (S : Set V)
    (f : V → ℝ) :
    killedGeneratorMatrix c m S *ᵥ f = killedMassGenerator G c m S f := by
  unfold killedGeneratorMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    killingProjection_mulVec, killingProjection_mulVec]
  ext v
  by_cases hv : v ∈ S
  · simp only [killedMassGenerator, Set.indicator_of_mem hv, Matrix.mulVec_diagonal,
      Matrix.sub_mulVec, Pi.sub_apply]
    simp only [massGenerator, netLaplacian_eq_sum_univ G hc, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Set.indicator_of_mem hv]
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub, div_eq_mul_inv]
    ring
  · simp [killedMassGenerator, hv]

end Heat

/-- The killed heat matrix at time `t`: the matrix exponential of `t` times the killed generator
matrix. -/
noncomputable def killedHeatMatrix (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (t : ℝ) :
    Matrix V V ℝ :=
  NormedSpace.exp (t • killedGeneratorMatrix c m S)

/-- At time `0` the killed heat matrix is the identity. -/
@[simp] theorem killedHeatMatrix_zero (c : V → V → ℝ) (m : V → ℝ) (S : Set V) :
    killedHeatMatrix c m S 0 = 1 := by
  simp [killedHeatMatrix]

/-- The killed heat matrices satisfy the semigroup law in the time variable. -/
theorem killedHeatMatrix_add (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (s t : ℝ) :
    killedHeatMatrix c m S (s + t) = killedHeatMatrix c m S s * killedHeatMatrix c m S t := by
  unfold killedHeatMatrix
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

/-- The killed heat matrix solves the matrix equation `d/dt P_t = Q P_t`, where `Q` is the killed
generator matrix. -/
theorem hasDerivAt_killedHeatMatrix (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (t : ℝ) :
    HasDerivAt (killedHeatMatrix c m S)
      (killedGeneratorMatrix c m S * killedHeatMatrix c m S t) t :=
  hasDerivAt_exp_smul_const' _ _

/-- The killed heat flow of the datum `f`: the killed heat matrix applied to the zero extension of
`f` to `S`. -/
noncomputable def killedHeatFlow (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (f : V → ℝ) (t : ℝ) :
    V → ℝ :=
  killedHeatMatrix c m S t *ᵥ S.indicator f

/-- At time `0` the killed heat flow is the zero extension of the datum to `S`. -/
@[simp] theorem killedHeatFlow_zero (c : V → V → ℝ) (m : V → ℝ) (S : Set V) (f : V → ℝ) :
    killedHeatFlow c m S f 0 = S.indicator f := by
  simp [killedHeatFlow]

/-- Applying a fixed vector to a matrix, as a continuous linear map on matrices. -/
private noncomputable def matrixApplyCLM (f : V → ℝ) :
    Matrix V V ℝ →L[ℝ] (V → ℝ) :=
  (Matrix.mulVecBilin (R := ℝ) (S := ℝ)).flip f |>.toContinuousLinearMap

section Heat

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- The killed heat flow solves the killed heat equation `d/dt u = killedMassGenerator G c m S u`. -/
theorem hasDerivAt_killedHeatFlow {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ) (S : Set V)
    (f : V → ℝ) (t : ℝ) :
    HasDerivAt (killedHeatFlow c m S f)
      (killedMassGenerator G c m S (killedHeatFlow c m S f t)) t := by
  have h := (matrixApplyCLM (S.indicator f)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_killedHeatMatrix c m S t)
  change HasDerivAt (fun s => killedHeatMatrix c m S s *ᵥ S.indicator f)
    ((killedGeneratorMatrix c m S * killedHeatMatrix c m S t) *ᵥ S.indicator f) t at h
  rw [← Matrix.mulVec_mulVec, killedGeneratorMatrix_mulVec G hc] at h
  exact h

end Heat

namespace KilledHeatExample

open SimpleGraph

attribute [local instance] HeatGeneratorExample.pathLocallyFinite

/-- On the path `0 – 1 – 2` with unit conductance, unit mass and `S = {0, 1}`, the killed heat flow
at time `0` is the zero extension of the datum to `S`. -/
example (f : Fin 3 → ℝ) :
    killedHeatFlow (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} f 0 =
      ({0, 1} : Set (Fin 3)).indicator f :=
  killedHeatFlow_zero _ _ _ _

/-- On the same path, the killed heat flow solves the killed heat equation, so the derivative
statement `hasDerivAt_killedHeatFlow` applies. -/
example (f : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (killedHeatFlow (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} f)
      (killedMassGenerator (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1}
        (killedHeatFlow (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) {0, 1} f t)) t :=
  hasDerivAt_killedHeatFlow (pathGraph 3) isCond_unitCond _ _ _ _

end KilledHeatExample

end LatticeProb.Network
