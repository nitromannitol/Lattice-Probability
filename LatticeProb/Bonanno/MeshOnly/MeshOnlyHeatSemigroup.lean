/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatSemigroup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyHeatGenerator
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! The finite killed heat evolution is the exponential of the actual
tile-mass generator. The exterior coordinates are kept only to express zero
extension on a fixed ambient finite state space. -/

open Matrix
open scoped BigOperators Matrix Matrix.Norms.Operator

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [DecidableEq V] (N : FiniteConductanceNetwork V)

/-- Diagonal projection to the active vertices. -/
noncomputable def killingProjection (S : Set V) : Matrix V V ℝ :=
  Matrix.diagonal (S.indicator (fun _ => 1))

lemma killingProjection_mulVec (S : Set V) (f : V → ℝ) :
    killingProjection S *ᵥ f = S.indicator f := by
  ext v
  by_cases hv : v ∈ S <;> simp [killingProjection, Matrix.mulVec_diagonal, hv]

/-- Matrix of `m⁻¹ Δa`, with zero extension and killing outside `S`. -/
noncomputable def killedGeneratorMatrix (m : V → ℝ) (S : Set V) : Matrix V V ℝ :=
  killingProjection S * Matrix.diagonal (fun v => (m v)⁻¹) *
    ((Matrix.of N.a) - Matrix.diagonal (fun v => ∑ w, N.a v w)) * killingProjection S

lemma killedGeneratorMatrix_mulVec (m : V → ℝ) (S : Set V) (f : V → ℝ) :
    N.killedGeneratorMatrix m S *ᵥ f = N.killedMassGenerator m S f := by
  unfold killedGeneratorMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    killingProjection_mulVec, killingProjection_mulVec]
  ext v
  by_cases hv : v ∈ S
  · simp only [killedMassGenerator, Set.indicator_of_mem hv, Matrix.mulVec_diagonal,
      Matrix.sub_mulVec, Pi.sub_apply]
    simp only [massGenerator, laplacian, Matrix.mulVec,
      dotProduct, Matrix.of_apply, Set.indicator_of_mem hv]
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub, div_eq_mul_inv]
    ring
  · simp [killedMassGenerator, hv]

/-- The actual finite matrix exponential, with no assumed heat equation. -/
noncomputable def killedHeatMatrix (m : V → ℝ) (S : Set V) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp (t • N.killedGeneratorMatrix m S)

@[simp] lemma killedHeatMatrix_zero (m : V → ℝ) (S : Set V) :
    N.killedHeatMatrix m S 0 = 1 := by
  simp [killedHeatMatrix]

lemma killedHeatMatrix_add (m : V → ℝ) (S : Set V) (s t : ℝ) :
    N.killedHeatMatrix m S (s + t) = N.killedHeatMatrix m S s * N.killedHeatMatrix m S t := by
  unfold killedHeatMatrix
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

lemma hasDerivAt_killedHeatMatrix (m : V → ℝ) (S : Set V) (t : ℝ) :
    HasDerivAt (N.killedHeatMatrix m S)
      (N.killedGeneratorMatrix m S * N.killedHeatMatrix m S t) t :=
  hasDerivAt_exp_smul_const' _ _

/-- Evolve the zero extension of the initial data. -/
noncomputable def killedHeatFlow (m : V → ℝ) (S : Set V) (f : V → ℝ) (t : ℝ) : V → ℝ :=
  N.killedHeatMatrix m S t *ᵥ S.indicator f

@[simp] lemma killedHeatFlow_zero (m : V → ℝ) (S : Set V) (f : V → ℝ) :
    N.killedHeatFlow m S f 0 = S.indicator f := by
  simp [killedHeatFlow]

private noncomputable def matrixApplyCLM (f : V → ℝ) :
    Matrix V V ℝ →L[ℝ] (V → ℝ) :=
  (Matrix.mulVecBilin (R := ℝ) (S := ℝ)).flip f |>.toContinuousLinearMap

lemma hasDerivAt_killedHeatFlow (m : V → ℝ) (S : Set V) (f : V → ℝ) (t : ℝ) :
    HasDerivAt (N.killedHeatFlow m S f)
      (N.killedMassGenerator m S (N.killedHeatFlow m S f t)) t := by
  have h := (matrixApplyCLM (S.indicator f)).hasFDerivAt.comp_hasDerivAt t
    (N.hasDerivAt_killedHeatMatrix m S t)
  change HasDerivAt (fun s => N.killedHeatMatrix m S s *ᵥ S.indicator f)
    ((N.killedGeneratorMatrix m S * N.killedHeatMatrix m S t) *ᵥ S.indicator f) t at h
  rw [← Matrix.mulVec_mulVec, N.killedGeneratorMatrix_mulVec] at h
  exact h

end BouRabeeGwynne.FiniteConductanceNetwork
