/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/PolynomialDirichlet.lean.
-/
import LatticeProb.Analysis.Polynomial.Analytic
import LatticeProb.Analysis.Polynomial.BallVanishing
import LatticeProb.Analysis.Polynomial.Degree
import LatticeProb.Analysis.Polynomial.Laplacian
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Prob.BrownianPathHarmonicExit
import LatticeProb.Prob.BrownianPathSpace
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Harmonic polynomial extensions from a sphere

For a ball `Metric.ball c r` in `EuclideanSpace ℝ (Fin d)`, the ball factor
`B = r ^ 2 - ∑ᵢ (xᵢ - cᵢ) ^ 2` is a polynomial of total degree at most two which vanishes on
`Metric.sphere c r`. The file shows that the linear map `q ↦ Δ (B q)` on polynomials of degree at
most `m` is injective, assuming a standard Brownian law in dimension `d`. Finite dimensionality then
gives, for every polynomial `p`, a harmonic polynomial `p - B q` that agrees with `p` on the sphere.

The injectivity proof applies the Brownian exit representation of harmonic functions to `B q`, which
is harmonic when `Δ (B q) = 0`. The exit position from the ball lies on the sphere, where `B` vanishes,
so the expected value of `B q` at the exit position is zero. Hence `B(z) q(z) = 0` at every point `z`
of the ball, and `B(z) > 0` there forces `q(z) = 0`.

The existence statement without a Brownian hypothesis is not part of this file.
-/

open MvPolynomial MeasureTheory Set

namespace LatticeProb

/-- The ball factor `r ^ 2 - ∑ᵢ (xᵢ - cᵢ) ^ 2` of the ball of radius `r` about `c`, as a polynomial
in `d` variables. Its evaluation at `x` is `r ^ 2 - ‖x - c‖ ^ 2`, see `polynomialEval_ballFactor`. -/
noncomputable def polynomialBallFactor {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    MvPolynomial (Fin d) ℝ := C (r ^ 2) - ∑ i : Fin d, (X i - C (c i)) ^ 2

/-- The ball factor has total degree at most two. -/
lemma polynomialBallFactor_degree_le {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (polynomialBallFactor c r).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, Nat.zero_le]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    have hi : (X i - C (c i) : MvPolynomial (Fin d) ℝ).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub_C_le _ _).trans_eq (MvPolynomial.totalDegree_X i)
    exact (MvPolynomial.totalDegree_pow _ 2).trans (by omega)

/-- The ball factor evaluates to `r ^ 2 - ‖x - c‖ ^ 2` at a point `x`. -/
lemma polynomialEval_ballFactor {d : ℕ} (c x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    polynomialEval (polynomialBallFactor c r) x = r ^ 2 - ‖x - c‖ ^ 2 := by
  simp [polynomialEval, polynomialBallFactor, EuclideanSpace.real_norm_sq_eq,
    PiLp.sub_apply]

/-- The linear map `q ↦ Δ (B q)` on the polynomials of total degree at most `m`, where `B` is the
ball factor of the ball of radius `r` about `c` and `Δ` is the formal Laplacian. The map encodes no
boundary condition; the Dirichlet problem is solved through its injectivity, see
`ballDirichletOperator_injective`. -/
noncomputable def ballDirichletOperator {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) (m : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ m →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree (Fin d) ℝ m :=
  quadraticLaplacianOnDegree (polynomialBallFactor c r) (polynomialBallFactor_degree_le c r) m

/-- Assuming a standard Brownian law `μ` in dimension `d ≥ 1` as a hypothesis, the map
`ballDirichletOperator c r m` is injective for every positive radius `r` and every degree bound `m`. -/
theorem ballDirichletOperator_injective {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c : Euc d) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Function.Injective (ballDirichletOperator c r m) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hformal : polynomialLaplacian (polynomialBallFactor c r * q.val) = 0 := by
    have hv := congrArg Subtype.val hq
    exact hv
  let f := polynomialEval (polynomialBallFactor c r * q.val)
  have hh : HarmonicNearClosure f (Metric.ball c r) :=
    ⟨Set.univ, isOpen_univ, subset_univ _,
      isHarmonicOn_polynomialEval_of_laplacian_eq_zero _ hformal Set.univ⟩
  have hmul (x : Euc d) : f x =
      polynomialEval (polynomialBallFactor c r) x * polynomialEval q.val x := by
    simp only [f, polynomialEval, map_mul]
  have hfrontier (x : Euc d) (hx : x ∈ frontier (Metric.ball c r)) : f x = 0 := by
    have hnorm : ‖x - c‖ = r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using Metric.frontier_ball_subset_sphere hx
    rw [hmul, polynomialEval_ballFactor, hnorm, sub_self, zero_mul]
  have hbdd : Bornology.IsBounded (Metric.ball c r) := Metric.isBounded_ball
  apply Subtype.ext
  change q.val = 0
  apply polynomial_eq_zero_of_eval_zero_on_ball q.val c hr
  intro z hz
  have hae : ∀ᵐ ω ∂μ, z + ω (continuousExitTime (Metric.ball c r) z ω).toNNReal ∈
      frontier (Metric.ball c r) := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
      standardBrownianLaw_ae_finiteExit hd hμ hbdd z] with ω h0 hfin
    refine continuousExitTime_mem_frontier Metric.isOpen_ball ?_ hfin
    rw [h0, add_zero]
    exact hz
  have heq : f z = 0 := by
    calc
      f z = ∫ ω, f (z + ω (continuousExitTime (Metric.ball c r) z ω).toNNReal) ∂μ :=
        (standardBrownianLaw_integral_exit_harmonicNearClosure hd hμ Metric.isOpen_ball
          hbdd hh hz).symm
      _ = ∫ _ω, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hae] with ω hω
        exact hfrontier _ hω
      _ = 0 := by simp
  have hpos : 0 < polynomialEval (polynomialBallFactor c r) z := by
    rw [polynomialEval_ballFactor]
    have hnorm : ‖z - c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    nlinarith [norm_nonneg (z - c)]
  rw [hmul] at heq
  exact (mul_eq_zero.mp heq).resolve_left hpos.ne'

/-- Assuming a standard Brownian law `μ` in dimension `d ≥ 1` as a hypothesis, every polynomial `p`
agrees on the sphere `Metric.sphere c r` with a polynomial `P` whose formal Laplacian vanishes. -/
theorem exists_harmonic_polynomial_on_sphere_of_brownianLaw {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c : Euc d) {r : ℝ} (hr : 0 < r) (p : MvPolynomial (Fin d) ℝ) :
    ∃ P : MvPolynomial (Fin d) ℝ, polynomialLaplacian P = 0 ∧
      EqOn (polynomialEval P) (polynomialEval p) (Metric.sphere c r) := by
  have hdeg : (polynomialLaplacian p).totalDegree ≤ p.totalDegree := by
    simpa only [polynomialLaplacian, one_mul] using
      (totalDegree_laplacian_mul_le (A := (1 : MvPolynomial (Fin d) ℝ))
        (p := p) (by simp) le_rfl)
  let target : MvPolynomial.restrictTotalDegree (Fin d) ℝ p.totalDegree :=
    ⟨polynomialLaplacian p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdeg⟩
  obtain ⟨q, hq⟩ := (LinearMap.surjective_of_injective
    (ballDirichletOperator_injective hd hμ c hr p.totalDegree)) target
  have hqformal : polynomialLaplacian (polynomialBallFactor c r * q.val) =
      polynomialLaplacian p := congrArg Subtype.val hq
  refine ⟨p - polynomialBallFactor c r * q.val, ?_, ?_⟩
  · simp only [polynomialLaplacian, map_sub, Finset.sum_sub_distrib]
    change polynomialLaplacian p - polynomialLaplacian (polynomialBallFactor c r * q.val) = 0
    rw [hqformal, sub_self]
  · intro x hx
    have hnorm : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
    have hfactor : polynomialEval (polynomialBallFactor c r) x = 0 := by
      rw [polynomialEval_ballFactor, hnorm, sub_self]
    change MvPolynomial.eval (fun i => x i) _ = _
    rw [map_sub, map_mul]
    change polynomialEval p x - polynomialEval (polynomialBallFactor c r) x *
      polynomialEval q.val x = polynomialEval p x
    rw [hfactor, zero_mul, sub_zero]

namespace PolynomialDirichletExample

/-- The ball factor of the unit ball about the origin in dimension one has total degree at most
two. -/
example : (polynomialBallFactor (0 : EuclideanSpace ℝ (Fin 1)) 1).totalDegree ≤ 2 :=
  polynomialBallFactor_degree_le _ _

/-- The hypothesis `hμ` of `ballDirichletOperator_injective` is satisfiable in dimension one, so the
injectivity statement applies there. -/
example (m : ℕ) : Function.Injective (ballDirichletOperator (0 : Euc 1) 1 m) := by
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  exact ballDirichletOperator_injective (d := 1) le_rfl hμ 0 one_pos m

/-- The hypothesis `hμ` of `exists_harmonic_polynomial_on_sphere_of_brownianLaw` is satisfiable in
dimension one. For the concrete polynomial `X 0 ^ 2`, the statement gives a harmonic polynomial that
agrees with it on the unit sphere about the origin. -/
example : ∃ P : MvPolynomial (Fin 1) ℝ, polynomialLaplacian P = 0 ∧
    EqOn (polynomialEval P) (polynomialEval (X 0 ^ 2 : MvPolynomial (Fin 1) ℝ))
      (Metric.sphere (0 : Euc 1) 1) := by
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  exact exists_harmonic_polynomial_on_sphere_of_brownianLaw (d := 1) le_rfl hμ 0 one_pos
    (X 0 ^ 2)

end PolynomialDirichletExample

end LatticeProb
