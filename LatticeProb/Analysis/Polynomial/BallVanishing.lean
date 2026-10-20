/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/PolynomialBallIdentity.lean.
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Interval.Set.Infinite

/-!
# Real polynomials vanishing on a Euclidean ball

A real polynomial in `d` variables that vanishes on a nonempty open Euclidean ball is the zero
polynomial. The file proves the coordinate bound `‖x‖ ≤ ∑ᵢ |xᵢ|` for the Euclidean norm, and uses
it to find an open box inside the ball on which the polynomial vanishes, so that
`MvPolynomial.funext_set` applies.
-/

namespace LatticeProb

/-- The Euclidean norm of a vector in `ℝ^d` is at most the sum of the absolute values of its
coordinates. -/
lemma norm_le_sum_abs_coordinates {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ ∑ i : Fin d, |x i| := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hx : x = ∑ i : Fin d, x i • b i := by
    simpa only [b, EuclideanSpace.basisFun_repr] using (b.sum_repr x).symm
  calc
    ‖x‖ = ‖∑ i : Fin d, x i • b i‖ := congrArg norm hx
    _ ≤ ∑ i : Fin d, ‖x i • b i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, b.norm_eq_one, mul_one, Real.norm_eq_abs]

/-- A real polynomial in `d` variables that vanishes at every point of a nonempty open ball
`Metric.ball c r` in `ℝ^d` is the zero polynomial. -/
theorem polynomial_eq_zero_of_eval_zero_on_ball {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (hp : ∀ x ∈ Metric.ball c r, MvPolynomial.eval (fun i => x i) p = 0) : p = 0 := by
  classical
  let a : ℝ := r / ((d : ℝ) + 1)
  have ha : 0 < a := div_pos hr (by positivity)
  have hda : (d : ℝ) * a < r := by
    have heq : a * ((d : ℝ) + 1) = r := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply MvPolynomial.funext_set (fun i : Fin d => Set.Ioo (c i - a) (c i + a))
    (fun i => Set.Ioo_infinite (by linarith))
  intro x hx
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hcoord (i : Fin d) : |(y - c) i| ≤ a := by
    have hi := hx i (Set.mem_univ i)
    change |x i - c i| ≤ a
    exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hy : y ∈ Metric.ball c r := by
    apply Metric.mem_ball.mpr
    calc
      dist y c = ‖y - c‖ := dist_eq_norm _ _
      _ ≤ ∑ i : Fin d, |(y - c) i| := norm_le_sum_abs_coordinates _
      _ ≤ ∑ _i : Fin d, a := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (d : ℝ) * a := by simp
      _ < r := hda
  have hyzero := hp y hy
  change MvPolynomial.eval x p = 0 at hyzero
  simpa only [map_zero] using hyzero

namespace BallVanishingExample

-- The hypothesis of `polynomial_eq_zero_of_eval_zero_on_ball` holds for the zero polynomial in two
-- variables on the unit ball centred at `0`.
example : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
    MvPolynomial.eval (fun i => x i) (0 : MvPolynomial (Fin 2) ℝ) = 0 :=
  fun _ _ => map_zero _

-- Applying `polynomial_eq_zero_of_eval_zero_on_ball` to that data, with `d = 2`, `c = 0`, `r = 1`.
example : (0 : MvPolynomial (Fin 2) ℝ) = 0 :=
  polynomial_eq_zero_of_eval_zero_on_ball (d := 2) 0 0 one_pos
    (fun _ _ => map_zero _)

end BallVanishingExample

end LatticeProb
