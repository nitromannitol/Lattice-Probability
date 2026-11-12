/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyHeatMatrixBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Poisson.Basic

/-! Elementary finite-matrix facts used by uniformization: positivity and
subprobability row sums persist under powers, and detailed balance persists
under the actual matrix exponential. -/

open scoped BigOperators NNReal Matrix Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.MeshOnlyHeat

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSubstochastic (P : Matrix V V ℝ) : Prop :=
  (∀ v w, 0 ≤ P v w) ∧ ∀ v, ∑ w, P v w ≤ 1

lemma isSubstochastic_one : IsSubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro v w
    by_cases h : v = w <;> simp [Matrix.one_apply, h]
  · intro v
    simp [Matrix.one_apply]

lemma IsSubstochastic.mul {P Q : Matrix V V ℝ}
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

lemma IsSubstochastic.pow {P : Matrix V V ℝ} (hP : IsSubstochastic P) (n : ℕ) :
    IsSubstochastic (P ^ n) := by
  induction n with
  | zero => simpa using (isSubstochastic_one (V := V))
  | succ n ih => simpa only [pow_succ] using ih.mul hP


/-- The Poisson-weighted power series converges to the actual exponential.
This is the finite-time uniformization identity before substituting a generator. -/
lemma hasSum_poisson_powers (P : Matrix V V ℝ) (r : ℝ≥0) :
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
lemma IsSubstochastic.poisson_exp {P : Matrix V V ℝ} (hP : IsSubstochastic P)
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

/-- Keeping only the zero-jump term gives a strictly positive diagonal. -/
lemma IsSubstochastic.exp_neg_le_poisson_exp_diagonal {P : Matrix V V ℝ}
    (hP : IsSubstochastic P) (r : ℝ≥0) (v : V) :
    Real.exp (-(r : ℝ)) ≤
      (Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P)) v v := by
  have he := Pi.hasSum.mp (Pi.hasSum.mp (hasSum_poisson_powers P r) v) v
  have h := le_hasSum he 0 (fun n _ =>
    mul_nonneg (by positivity : 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial)
      ((hP.pow n).1 v v))
  simpa using h

/-- The uniformization series is exactly the exponential of `r(P-I)`. -/
lemma poisson_exp_eq_exp_smul_sub_one (P : Matrix V V ℝ) (r : ℝ≥0) :
    Real.exp (-(r : ℝ)) • NormedSpace.exp ((r : ℝ) • P) =
      NormedSpace.exp ((r : ℝ) • (P - 1)) := by
  have he : NormedSpace.exp ((-(r : ℝ)) • (1 : Matrix V V ℝ)) =
      Real.exp (-(r : ℝ)) • (1 : Matrix V V ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix V V ℝ) (-(r : ℝ))).symm
  have ha : (r : ℝ) • (P - 1) = (-(r : ℝ)) • (1 : Matrix V V ℝ) + (r : ℝ) • P := by
    rw [smul_sub, neg_smul]
    abel
  rw [ha, NormedSpace.exp_add_of_commute
    (((Commute.one_left P).smul_left (-(r : ℝ))).smul_right (r : ℝ)), he,
    smul_mul_assoc, one_mul]

/-- Detailed balance with respect to the positive tile masses. The definition
itself does not need positivity. -/
def IsMassReversible (m : V → ℝ) (P : Matrix V V ℝ) : Prop :=
  ∀ v w, m v * P v w = m w * P w v

lemma isMassReversible_iff_semiconj (m : V → ℝ) (P : Matrix V V ℝ) :
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

lemma IsMassReversible.smul {m : V → ℝ} {P : Matrix V V ℝ}
    (hP : IsMassReversible m P) (t : ℝ) : IsMassReversible m (t • P) := by
  intro v w
  change m v * (t * P v w) = m w * (t * P w v)
  calc
    _ = t * (m v * P v w) := by ring
    _ = t * (m w * P w v) := congrArg (fun x : ℝ => t * x) (hP v w)
    _ = _ := by ring

lemma IsMassReversible.exp {m : V → ℝ} {P : Matrix V V ℝ}
    (hP : IsMassReversible m P) : IsMassReversible m (NormedSpace.exp P) := by
  apply (isMassReversible_iff_semiconj m _).mpr
  have h := ((isMassReversible_iff_semiconj m P).mp hP).exp_right
  rw [Matrix.exp_transpose P] at h
  exact h

/-- Cauchy–Schwarz in the tile-mass measure, in the squared form needed for
the survival estimate. -/
lemma weighted_sum_sq_le (m f : V → ℝ) (hm : ∀ v, 0 ≤ m v) :
    (∑ v, m v * f v) ^ 2 ≤ (∑ v, m v) * ∑ v, m v * (f v) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun v _ => hm v) (fun v _ => mul_nonneg (hm v) (sq_nonneg _))
  intro v _
  exact le_of_eq (by ring)

end BouRabeeGwynne.MeshOnlyHeat
