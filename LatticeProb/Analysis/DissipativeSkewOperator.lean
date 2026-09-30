/-
# Coercive resolvents of a dissipative-skew generator

Moved from `manhattan-formalization` (`Manhattan.Operator.Variational`), where
it formalized the abstract half of the paper's Section 2.2 variational
argument. Nothing here refers to the paper's directed lattice: `E` is an
arbitrary complex Hilbert space, and the only structure used is a bounded
generator `G = S + A` split into a self-adjoint dissipative part `S`
(`re ⟪S x, x⟫ ≤ 0`) and a skew-adjoint part `A` (`A† = -A`).

For `lambda > 0`, `H := lambda • id - S` and its perturbations `H ± A` are
each shown coercive as real bilinear forms (via `IsCoercive`, so
Lax–Milgram applies) and hence bijective. The main theorem,
`variational_bound`, is the one-sided variational formula: for every
competitor vector `g`, the "resolvent energy" of `lambda I - G` at any vector
`V` is squeezed between `0` and `‖g‖₊² + ‖V - A g‖₋²`, where `‖·‖₊`/`‖·‖₋` are
the energy norms of `H`. This is the standard route to resolvent bounds for a
generator with an antisymmetric (transport) perturbation of a symmetric
dissipative part, independent of any particular lattice or model.
-/
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open ComplexConjugate InnerProductSpace RCLike
open scoped ComplexConjugate InnerProduct

namespace LatticeProb.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The abstract hypotheses on the symmetric and antisymmetric parts of a
bounded generator `G = S + A`: `S` self-adjoint and dissipative, `A`
skew-adjoint. -/
structure DissipativeSkewPair (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  /-- The symmetric part. -/
  S : E →L[ℂ] E
  /-- The antisymmetric part. -/
  A : E →L[ℂ] E
  selfAdjoint_S : IsSelfAdjoint S
  nonpositive_S : ∀ x, re ⟪S x, x⟫_ℂ ≤ 0
  skewAdjoint_A : A† = -A

end LatticeProb.Analysis

namespace LatticeProb.Analysis.DissipativeSkewPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (P : DissipativeSkewPair E)

/-- The complex space read as a real normed space. -/
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
/-- The real inner product is the real part of the complex one. -/
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- `H = lambda I - S`. -/
def H (lambda : ℝ) : E →L[ℂ] E :=
  (lambda : ℂ) • ContinuousLinearMap.id ℂ E - P.S

/-- `H + A = lambda I - (S - A)`. -/
def plus (lambda : ℝ) : E →L[ℂ] E := P.H lambda + P.A

/-- `H - A = lambda I - (S + A) = lambda I - G`, the resolvent of the full
generator. -/
def minus (lambda : ℝ) : E →L[ℂ] E := P.H lambda - P.A

/-- The real bilinear form associated with a complex-linear operator. -/
def realForm (T : E →L[ℂ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    ((innerₗ E).comp (T.restrictScalars ℝ).toLinearMap) ‖T‖ fun x y ↦ by
      calc
        |⟪T x, y⟫_ℝ| ≤ ‖T x‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg y)
        _ = ‖T‖ * ‖x‖ * ‖y‖ := rfl

omit [CompleteSpace E] in
/-- `realForm` computes the real part of the complex inner product. -/
@[simp]
theorem realForm_apply (T : E →L[ℂ] E) (x y : E) :
    realForm T x y = re ⟪T x, y⟫_ℂ := rfl

/-- Skew-adjointness makes `A` invisible to the real part of the inner
product against itself. -/
theorem re_inner_A_self (x : E) : re ⟪P.A x, x⟫_ℂ = 0 := by
  have h := congrArg re (P.A.adjoint_inner_left x x)
  rw [P.skewAdjoint_A] at h
  simp only [neg_apply, inner_neg_left, map_neg] at h
  rw [inner_re_symm] at h
  rw [inner_re_symm]
  linarith

/-- `H`'s quadratic form splits into the shift `lambda ‖x‖²` and the
(nonpositive) contribution of `S`. -/
theorem re_inner_H_apply (lambda : ℝ) (x : E) :
    re ⟪P.H lambda x, x⟫_ℂ =
      lambda * ‖x‖ ^ 2 - re ⟪P.S x, x⟫_ℂ := by
  rw [H, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, map_sub]
  congr 1
  calc
    re ⟪(lambda : ℂ) • x, x⟫_ℂ =
        re ((starRingEnd ℂ) (lambda : ℂ) * ⟪x, x⟫_ℂ) := by
      rw [inner_smul_left]
    _ = lambda * re ⟪x, x⟫_ℂ := by simp
    _ = lambda * ‖x‖ ^ 2 := by rw [inner_self_eq_norm_sq]

/-- The lower bound `lambda ‖x‖² ≤ re ⟪Hx, x⟫`, from dissipativity of `S`. -/
theorem hEnergy_lower (lambda : ℝ) (x : E) :
    lambda * ‖x‖ ^ 2 ≤ re ⟪P.H lambda x, x⟫_ℂ := by
  rw [P.re_inner_H_apply]
  linarith [P.nonpositive_S x]

/-- `H`'s quadratic form is nonnegative for `lambda ≥ 0`. -/
theorem hEnergy_nonneg {lambda : ℝ} (hlambda : 0 ≤ lambda) (x : E) :
    0 ≤ re ⟪P.H lambda x, x⟫_ℂ :=
  le_trans (mul_nonneg hlambda (sq_nonneg ‖x‖)) (P.hEnergy_lower lambda x)

/-- `H + A`'s real form is coercive with constant `lambda`. -/
theorem realForm_plus_coercive {lambda : ℝ} (hlambda : 0 < lambda) :
    IsCoercive (realForm (P.plus lambda)) := by
  refine ⟨lambda, hlambda, fun x ↦ ?_⟩
  rw [realForm_apply]
  simp only [plus, add_apply, inner_add_left, map_add,
    P.re_inner_A_self, add_zero]
  simpa only [pow_two, mul_assoc] using P.hEnergy_lower lambda x

/-- `H - A`'s real form is coercive with constant `lambda`. -/
theorem realForm_minus_coercive {lambda : ℝ} (hlambda : 0 < lambda) :
    IsCoercive (realForm (P.minus lambda)) := by
  refine ⟨lambda, hlambda, fun x ↦ ?_⟩
  rw [realForm_apply]
  simp only [minus, sub_apply, inner_sub_left, map_sub,
    P.re_inner_A_self, sub_zero]
  simpa only [pow_two, mul_assoc] using P.hEnergy_lower lambda x

/-- `H`'s real form is coercive with constant `lambda`. -/
theorem realForm_H_coercive {lambda : ℝ} (hlambda : 0 < lambda) :
    IsCoercive (realForm (P.H lambda)) := by
  refine ⟨lambda, hlambda, fun x ↦ ?_⟩
  rw [realForm_apply]
  simpa only [pow_two, mul_assoc] using P.hEnergy_lower lambda x

private theorem bijective_of_realForm_coercive (T : E →L[ℂ] E)
    (hT : IsCoercive (realForm T)) : Function.Bijective T := by
  let e : E ≃L[ℝ] E := hT.continuousLinearEquivOfBilin
  have he (x : E) : e x = T x := by
    apply ext_inner_right ℝ
    intro y
    rw [IsCoercive.continuousLinearEquivOfBilin_apply]
    rfl
  constructor
  · intro x y hxy
    apply e.injective
    simpa only [he] using hxy
  · intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, by simpa only [he] using hx⟩

/-- `H + A = lambda I - (S - A)` is bijective for `lambda > 0`. -/
theorem plus_bijective {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Bijective (P.plus lambda) :=
  bijective_of_realForm_coercive (P.plus lambda) (P.realForm_plus_coercive hlambda)

/-- `H - A = lambda I - G` is bijective for `lambda > 0`: the resolvent of the
full generator exists and is a bounded inverse. -/
theorem minus_bijective {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Bijective (P.minus lambda) :=
  bijective_of_realForm_coercive (P.minus lambda) (P.realForm_minus_coercive hlambda)

/-- `H = lambda I - S` is bijective for `lambda > 0`. -/
theorem H_bijective {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Bijective (P.H lambda) :=
  bijective_of_realForm_coercive (P.H lambda) (P.realForm_H_coercive hlambda)

/-- The bounded equivalence induced by `H + A`. -/
def plusEquiv {lambda : ℝ} (hlambda : 0 < lambda) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective (P.plus lambda)
    (LinearMap.ker_eq_bot.mpr (P.plus_bijective hlambda).1)
    (LinearMap.range_eq_top.mpr (P.plus_bijective hlambda).2)

/-- The bounded equivalence induced by `H - A`; its inverse is the resolvent
of the full generator. -/
def minusEquiv {lambda : ℝ} (hlambda : 0 < lambda) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective (P.minus lambda)
    (LinearMap.ker_eq_bot.mpr (P.minus_bijective hlambda).1)
    (LinearMap.range_eq_top.mpr (P.minus_bijective hlambda).2)

/-- The bounded equivalence induced by `H`. -/
def hEquiv {lambda : ℝ} (hlambda : 0 < lambda) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective (P.H lambda)
    (LinearMap.ker_eq_bot.mpr (P.H_bijective hlambda).1)
    (LinearMap.range_eq_top.mpr (P.H_bijective hlambda).2)

/-- `plusEquiv` really inverts `plus`. -/
@[simp]
theorem plus_apply_inverse {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    P.plus lambda ((P.plusEquiv hlambda).symm x) = x :=
  (P.plusEquiv hlambda).apply_symm_apply x

/-- `minusEquiv` really inverts `minus`. -/
@[simp]
theorem minus_apply_inverse {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    P.minus lambda ((P.minusEquiv hlambda).symm x) = x :=
  (P.minusEquiv hlambda).apply_symm_apply x

/-- `hEquiv` really inverts `H`. -/
@[simp]
theorem H_apply_inverse {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    P.H lambda ((P.hEquiv hlambda).symm x) = x :=
  (P.hEquiv hlambda).apply_symm_apply x

/-- `H` is self-adjoint, being `lambda I` minus the self-adjoint `S`. -/
theorem H_selfAdjoint (lambda : ℝ) : IsSelfAdjoint (P.H lambda) := by
  rw [IsSelfAdjoint]
  change (P.H lambda)† = P.H lambda
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [(P.H lambda).adjoint_inner_right]
  have hS : ⟪P.S y, x⟫_ℂ = ⟪y, P.S x⟫_ℂ := by
    rw [← P.S.adjoint_inner_right y x]
    exact congrArg (fun T : E →L[ℂ] E ↦ ⟪y, T x⟫_ℂ) P.selfAdjoint_S
  simp only [H, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hS]
  simp

/-- Self-adjointness of `H`, spelled out as symmetry of its quadratic form. -/
theorem re_inner_H_symm (lambda : ℝ) (x y : E) :
    re ⟪P.H lambda x, y⟫_ℂ = re ⟪x, P.H lambda y⟫_ℂ := by
  rw [← (P.H lambda).adjoint_inner_right x y,
    show (P.H lambda)† = P.H lambda from P.H_selfAdjoint lambda]

/-- The positive energy quadratic form `‖g‖_{1,lambda}² := re ⟪Hg, g⟫`. -/
def hEnergy (lambda : ℝ) (g : E) : ℝ := re ⟪P.H lambda g, g⟫_ℂ

/-- The dual energy quadratic form `‖u‖_{-1,lambda}² := re ⟪u, H⁻¹u⟫`. -/
def hMinusEnergy {lambda : ℝ} (hlambda : 0 < lambda) (u : E) : ℝ :=
  re ⟪u, (P.hEquiv hlambda).symm u⟫_ℂ

/-- The fixed-frequency resolvent quadratic form `re ⟪V, (lambda I - G)⁻¹ V⟫`.
The sign convention matches `G = S + A`, hence `lambda I - G = H - A`. -/
def resolventQuadratic {lambda : ℝ} (hlambda : 0 < lambda) (V : E) : ℝ :=
  re ⟪V, (P.minusEquiv hlambda).symm V⟫_ℂ

private theorem young_H {lambda : ℝ} (hlambda : 0 < lambda) (q d : E) :
    2 * re ⟪q, d⟫_ℂ - P.hEnergy lambda d ≤ P.hMinusEnergy hlambda q := by
  let y := (P.hEquiv hlambda).symm q
  have hqy : P.H lambda y = q := P.H_apply_inverse hlambda q
  have hnonneg : 0 ≤ P.hEnergy lambda (y - d) := by
    exact P.hEnergy_nonneg hlambda.le (y - d)
  rw [hEnergy] at hnonneg
  rw [hEnergy, hMinusEnergy]
  change 2 * re ⟪q, d⟫_ℂ - re ⟪P.H lambda d, d⟫_ℂ ≤ re ⟪q, y⟫_ℂ
  rw [← hqy]
  simp only [map_sub, inner_sub_left, inner_sub_right, map_sub] at hnonneg
  have hcross : re ⟪P.H lambda d, y⟫_ℂ = re ⟪P.H lambda y, d⟫_ℂ :=
    (P.re_inner_H_symm lambda d y).trans (inner_re_symm d (P.H lambda y))
  linarith

/-- The resolvent quadratic form is nonnegative: writing `x` for the exact
resolvent vector, skew-adjointness of `A` turns the form into the energy
of `x`. -/
theorem resolventQuadratic_nonneg {lambda : ℝ} (hlambda : 0 < lambda) (V : E) :
    0 ≤ P.resolventQuadratic hlambda V := by
  let x := (P.minusEquiv hlambda).symm V
  have hx : P.H lambda x - P.A x = V := P.minus_apply_inverse hlambda V
  have hxenergy : P.resolventQuadratic hlambda V = P.hEnergy lambda x := by
    rw [resolventQuadratic, hEnergy]
    change re ⟪V, x⟫_ℂ = re ⟪P.H lambda x, x⟫_ℂ
    rw [← hx, inner_sub_left, map_sub, P.re_inner_A_self, sub_zero]
  rw [hxenergy]
  exact P.hEnergy_nonneg hlambda.le x

/-- The one-sided variational formula: every competitor `g` gives an upper
bound on the resolvent quadratic form. -/
theorem resolventQuadratic_le {lambda : ℝ} (hlambda : 0 < lambda) (V g : E) :
    P.resolventQuadratic hlambda V ≤
      P.hEnergy lambda g + P.hMinusEnergy hlambda (V - P.A g) := by
  let x := (P.minusEquiv hlambda).symm V
  let d := x + g
  let q := V - P.A g
  have hx : P.H lambda x - P.A x = V := by
    exact P.minus_apply_inverse hlambda V
  have hq : q = P.H lambda x - P.A d := by
    dsimp [q, d]
    rw [← hx]
    simp only [map_add]
    module
  have hqd : re ⟪q, d⟫_ℂ = re ⟪P.H lambda x, d⟫_ℂ := by
    rw [hq, inner_sub_left, map_sub, P.re_inner_A_self]
    simp
  have hxenergy : P.resolventQuadratic hlambda V = P.hEnergy lambda x := by
    rw [resolventQuadratic, hEnergy]
    change re ⟪V, x⟫_ℂ = re ⟪P.H lambda x, x⟫_ℂ
    rw [← hx, inner_sub_left, map_sub, P.re_inner_A_self, sub_zero]
  have hparallelogram :
      P.hEnergy lambda x = P.hEnergy lambda g +
        (2 * re ⟪q, d⟫_ℂ - P.hEnergy lambda d) := by
    rw [hqd]
    dsimp [d]
    simp only [hEnergy, map_add, inner_add_left, inner_add_right, Complex.add_re]
    have hcross : re ⟪P.H lambda g, x⟫_ℂ = re ⟪P.H lambda x, g⟫_ℂ :=
      (P.re_inner_H_symm lambda g x).trans (inner_re_symm g (P.H lambda x))
    rw [hcross]
    norm_num
    ring
  rw [hxenergy, hparallelogram]
  simpa only [q, add_comm] using
    add_le_add_left (P.young_H hlambda q d) (P.hEnergy lambda g)

/-- **The variational bound.** For every `lambda > 0`, every `V`, and every
competitor `g` in the Hilbert space,

  `0 ≤ resolventQuadratic V ≤ ‖g‖₊² + ‖V - A g‖₋²`.

The two halves are `resolventQuadratic_nonneg` and `resolventQuadratic_le`.
There is no hypothesis on `g`: the bound needs no normalization. -/
theorem variational_bound {lambda : ℝ} (hlambda : 0 < lambda) (V g : E) :
    0 ≤ P.resolventQuadratic hlambda V ∧
      P.resolventQuadratic hlambda V ≤
        P.hEnergy lambda g + P.hMinusEnergy hlambda (V - P.A g) :=
  ⟨P.resolventQuadratic_nonneg hlambda V, P.resolventQuadratic_le hlambda V g⟩

/-- The variational bound specialized to the driftless competitor `g = 0`. -/
theorem resolventQuadratic_le_hMinusEnergy {lambda : ℝ} (hlambda : 0 < lambda) (V : E) :
    P.resolventQuadratic hlambda V ≤ P.hMinusEnergy hlambda V := by
  simpa [hEnergy, hMinusEnergy] using P.resolventQuadratic_le hlambda V 0

end LatticeProb.Analysis.DissipativeSkewPair
