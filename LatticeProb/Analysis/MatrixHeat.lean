/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyHeatMatrixBounds.lean.
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Finite matrix facts for heat semigroups

Elementary facts about real matrices indexed by a finite type. A matrix is
substochastic when its entries are nonnegative and its row sums are at most one;
this property is preserved by products and powers. The Poisson-weighted matrix
exponential `exp(-r) • exp(r • P)` of a substochastic matrix is substochastic, its
diagonal entries are at least `exp(-r)`, and it equals `exp(r • (P - 1))`. Detailed
balance with respect to a vector of masses is preserved by the matrix exponential.
The file closes with a weighted Cauchy–Schwarz inequality in squared form.
-/

open scoped BigOperators NNReal Matrix Matrix.Norms.Operator

namespace LatticeProb

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A real matrix is substochastic if its entries are nonnegative and every row
sums to at most one. -/
def IsSubstochastic (P : Matrix V V ℝ) : Prop :=
  (∀ v w, 0 ≤ P v w) ∧ ∀ v, ∑ w, P v w ≤ 1

/-- The identity matrix is substochastic. -/
theorem isSubstochastic_one : IsSubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro v w
    by_cases h : v = w <;> simp [Matrix.one_apply, h]
  · intro v
    simp [Matrix.one_apply]

omit [DecidableEq V] in
/-- Products of substochastic matrices are substochastic. -/
theorem IsSubstochastic.mul {P Q : Matrix V V ℝ}
    (hP : IsSubstochastic P) (hQ : IsSubstochastic Q) : IsSubstochastic (P * Q) := by
  constructor
  · intro v w
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hP.1 v k) (hQ.1 k w)
  · intro v
    calc
      (∑ w, (P * Q) v w) = ∑ k, P v k * ∑ w, Q k w := by
        simp only [Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ k, P v k * 1 :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hQ.2 k) (hP.1 v k)
      _ ≤ 1 := by simpa using hP.2 v

/-- Powers of a substochastic matrix are substochastic. -/
theorem IsSubstochastic.pow {P : Matrix V V ℝ} (hP : IsSubstochastic P) (n : ℕ) :
    IsSubstochastic (P ^ n) := by
  induction n with
  | zero => simpa using (isSubstochastic_one (V := V))
  | succ n ih => simpa only [pow_succ] using ih.mul hP

/-- The Poisson-weighted power series converges to the actual exponential.
This is the finite-time uniformization identity before substituting a generator. -/
theorem hasSum_poisson_powers (P : Matrix V V ℝ) (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) • P^n)
      (Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P)) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((r : ℝ) • P)).const_smul
    (Real.exp (-(r : ℝ)))
  convert! h using 1
  funext n
  rw [smul_pow, smul_smul, smul_smul]
  congr 1
  simp only [div_eq_mul_inv]
  ring

/-- A Poisson mixture of substochastic powers is substochastic. -/
theorem IsSubstochastic.poisson_exp {P : Matrix V V ℝ} (hP : IsSubstochastic P)
    (r : ℝ≥0) :
    IsSubstochastic (Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P)) := by
  have hentry (v w : V) := Pi.hasSum.mp (Pi.hasSum.mp (hasSum_poisson_powers P r) v) w
  have hweight (n : ℕ) : 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial := by positivity
  constructor
  · intro v w
    exact HasSum.nonneg (fun n => mul_nonneg (hweight n) ((hP.pow n).1 v w)) (hentry v w)
  · intro v
    have hrow := hasSum_sum (s := Finset.univ) (fun w _ => hentry v w)
    apply hasSum_le (fun n => ?_) hrow (ProbabilityTheory.hasSum_one_poissonMeasure r)
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    simpa using mul_le_mul_of_nonneg_left ((hP.pow n).2 v) (hweight n)

/-- The diagonal entries of the Poisson-weighted exponential of a substochastic
matrix are at least `exp(-r)`, obtained by keeping only the zero-jump term. -/
theorem IsSubstochastic.exp_neg_le_poisson_exp_diagonal {P : Matrix V V ℝ}
    (hP : IsSubstochastic P) (r : ℝ≥0) (v : V) :
    Real.exp (-(r : ℝ)) ≤
      (Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P)) v v := by
  have he := Pi.hasSum.mp (Pi.hasSum.mp (hasSum_poisson_powers P r) v) v
  have h := le_hasSum he 0 (fun n _ =>
    mul_nonneg (by positivity : 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial)
      ((hP.pow n).1 v v))
  simpa using h

/-- The Poisson-weighted exponential of `P` equals the exponential of `r • (P - 1)`. -/
theorem poisson_exp_eq_exp_smul_sub_one (P : Matrix V V ℝ) (r : ℝ≥0) :
    Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P) =
      NormedSpace.exp ((r : ℝ) • (P - 1)) := by
  have he : NormedSpace.exp ((-(r : ℝ)) • (1 : Matrix V V ℝ)) =
      Real.exp (-(r : ℝ)) • (1 : Matrix V V ℝ) := by
    have h := (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix V V ℝ) (-(r : ℝ))).symm
    simp only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] at h
    exact h
  have ha : (r : ℝ) • (P - 1) = (-(r : ℝ)) • (1 : Matrix V V ℝ) + (r : ℝ) • P := by
    rw [smul_sub, neg_smul]
    abel
  have hc : Commute ((-(r : ℝ)) • (1 : Matrix V V ℝ)) ((r : ℝ) • P) :=
    ((Commute.one_left P).smul_left (-(r : ℝ))).smul_right (r : ℝ)
  calc
    Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P)
        = NormedSpace.exp ((-(r : ℝ)) • (1 : Matrix V V ℝ)) * NormedSpace.exp ((r : ℝ) • P) := by
          rw [he, smul_mul_assoc, one_mul]
      _ = NormedSpace.exp ((-(r : ℝ)) • (1 : Matrix V V ℝ) + (r : ℝ) • P) :=
          (NormedSpace.exp_add_of_commute hc).symm
      _ = NormedSpace.exp ((r : ℝ) • (P - 1)) := by rw [ha]

/-- Detailed balance with respect to the masses `m`: `m v * P v w = m w * P w v`
for all `v` and `w`. The definition does not need positivity of `m`. -/
def IsMassReversible (m : V → ℝ) (P : Matrix V V ℝ) : Prop :=
  ∀ v w, m v * P v w = m w * P w v

/-- Detailed balance with respect to `m` is equivalent to `diagonal m` semiconjugating
`P` to its transpose. -/
theorem isMassReversible_iff_semiconj (m : V → ℝ) (P : Matrix V V ℝ) :
    IsMassReversible m P ↔ SemiconjBy (Matrix.diagonal m) P P.transpose := by
  constructor
  · intro h
    change Matrix.diagonal m * P = P.transpose * Matrix.diagonal m
    ext v w
    simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply,
      mul_comm (P w v)] using h v w
  · intro h v w
    have hh := congrArg (fun A : Matrix V V ℝ => A v w) h.eq
    simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply,
      mul_comm (P w v)] using hh

omit [Fintype V] [DecidableEq V] in
/-- Scaling a detailed-balance matrix by a real number preserves detailed balance. -/
theorem IsMassReversible.smul {m : V → ℝ} {P : Matrix V V ℝ}
    (hP : IsMassReversible m P) (t : ℝ) : IsMassReversible m (t • P) := by
  intro v w
  change m v * (t * P v w) = m w * (t * P w v)
  calc
    _ = t * (m v * P v w) := by ring
    _ = t * (m w * P w v) := congrArg (fun x : ℝ => t * x) (hP v w)
    _ = _ := by ring

/-- The matrix exponential preserves detailed balance. -/
theorem IsMassReversible.exp {m : V → ℝ} {P : Matrix V V ℝ}
    (hP : IsMassReversible m P) : IsMassReversible m (NormedSpace.exp P) := by
  apply (isMassReversible_iff_semiconj m _).mpr
  have h := ((isMassReversible_iff_semiconj m P).mp hP).exp_right
  have ht : (NormedSpace.exp P)ᵀ = NormedSpace.exp Pᵀ := (Matrix.exp_transpose P).symm
  exact ht ▸ h

omit [DecidableEq V] in
/-- Cauchy–Schwarz inequality for a nonnegative weight `m`, in the squared form
`(∑ m f) ^ 2 ≤ (∑ m) * ∑ m f ^ 2`. -/
theorem weighted_sum_sq_le (m f : V → ℝ) (hm : ∀ v, 0 ≤ m v) :
    (∑ v, m v * f v) ^ 2 ≤ (∑ v, m v) * ∑ v, m v * (f v) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun v _ => hm v) (fun v _ => mul_nonneg (hm v) (sq_nonneg _))
  intro v _
  exact le_of_eq (by ring)

end LatticeProb

namespace IsSubstochasticExample

/-- The identity matrix on a two-point index set is substochastic, so the
substochastic hypotheses above are not vacuous. -/
example : LatticeProb.IsSubstochastic (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  LatticeProb.isSubstochastic_one

/-- The Poisson-weighted exponential of the identity matrix on a two-point index set
is substochastic. -/
example (r : ℝ≥0) :
    LatticeProb.IsSubstochastic
      (Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) :=
  LatticeProb.IsSubstochastic.poisson_exp
    (LatticeProb.isSubstochastic_one (V := Fin 2)) r

end IsSubstochasticExample
