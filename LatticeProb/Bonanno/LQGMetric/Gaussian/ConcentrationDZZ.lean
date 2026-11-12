/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.ConcentrationDZZ at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationLip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Borell–TIS for finite maxima and Ding–Zeitouni–Zhang Lemma 2.1 (Gram form)

A centered Gaussian vector `X = (X_1, …, X_n)` is represented as `X_i = ⟪v i, Z⟫` with `Z` a
standard Gaussian vector and `‖v i‖² = Var X_i` (DZZ's `X = A Z`; the rows of `A` are the `v i`).
In this representation we prove:

* `borellTIS_finiteMax` (Adler–Taylor, *Random Fields and Geometry*, Thm 2.1.1 for finite `T`,
  p. 56): `P(max_i X_i - E max_i X_i ≥ u) ≤ exp (-u² / (2σ²))` when `‖v i‖ ≤ σ`; proof as there:
  `z ↦ max_i ⟪v i, z⟫` is `σ`-Lipschitz, then Lemma 2.1.6 (`GaussConc.tail_le_of_lipschitz`).
* `dzz_lemma21_gram`: J. Ding, O. Zeitouni, F. Zhang, *Heat kernel for Liouville Brownian motion
  and Liouville graph distance* (arXiv:1807.00422), Lemma 2.1 (LaTeX lines 326–348): for every
  `c > 0` there is `C > 0` such that `P(X ∈ B) ≥ c` implies, for `λ ≥ Cσ`,
  `P(inf_{x ∈ B} |X - x|_∞ ≥ λ) ≤ exp (-(λ - Cσ)² / (2σ²))` (this is DFGPS Lemma 4.2's form; the
  DZZ form with prefactor `C ≥ 1` follows).

Proof of the DZZ lemma: as in DZZ, `z ↦ inf_{x∈B} |Az - x|_∞` is `σ`-Lipschitz in `z`
(Cauchy–Schwarz on each row, DFGPS comment at line 2562). Deviation: DZZ then cite the
Borell–Sudakov–Tsirelson isoperimetric inequality (Ledoux (2.9)); we use instead Gaussian
concentration for Lipschitz functions (Adler–Taylor Lemma 2.1.6, both tails): the lower tail and
`P(d = 0) ≥ c` give `E d ≤ σ √(2 log (1/c))`, and the upper tail gives the claim with
`C = max 1 √(2 log (1/c))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The vector `(⟪v i, z⟫)_i` (`= A z` for the matrix `A` with rows `v i`). -/
def gramVec {n : ℕ} (v : Fin n → E) (z : E) : Fin n → ℝ := fun i => ⟪v i, z⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `z ↦ A z` is `σ`-Lipschitz into `(ℝⁿ, |·|_∞)` when every row has norm `≤ σ`. -/
lemma lipschitzWith_gramVec {n : ℕ} {v : Fin n → E} {σ : ℝ≥0} (hv : ∀ i, ‖v i‖ ≤ σ) :
    LipschitzWith σ (gramVec v) :=
  LipschitzWith.of_dist_le_mul fun z w => (dist_pi_le_iff (by positivity)).2 fun i => by
    rw [Real.dist_eq, gramVec, gramVec, ← inner_sub_right, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _))

/-- The finite maximum is `1`-Lipschitz for the sup distance. -/
lemma lipschitzWith_sup' {n : ℕ} (hn : (Finset.univ : Finset (Fin n)).Nonempty) :
    LipschitzWith 1 fun x : Fin n → ℝ => Finset.univ.sup' hn x := by
  have key : ∀ x y : Fin n → ℝ, Finset.univ.sup' hn x ≤ Finset.univ.sup' hn y + dist x y := by
    intro x y
    refine Finset.sup'_le _ _ fun i _ => ?_
    have h1 := dist_le_pi_dist x y i
    rw [Real.dist_eq] at h1
    have h2 : y i ≤ Finset.univ.sup' hn y := Finset.le_sup' _ (Finset.mem_univ i)
    linarith [le_abs_self (x i - y i)]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_le_iff]
  constructor
  · linarith [key x y]
  · linarith [key y x, dist_comm x y]

/-- **Borell–TIS inequality for finite maxima** (Adler–Taylor, Theorem 2.1.1, finite `T`):
for `X_i = ⟪v i, Z⟫` with `‖v i‖ ≤ σ` (so `max_i Var X_i ≤ σ²`) and `u ≥ 0`,
`P(max_i X_i - E max_i X_i ≥ u) ≤ exp (-u² / (2σ²))`. -/
theorem borellTIS_finiteMax {n : ℕ} (hn : (Finset.univ : Finset (Fin n)).Nonempty)
    (v : Fin n → E) {σ : ℝ≥0} (hv : ∀ i, ‖v i‖ ≤ σ) {u : ℝ} (hu : 0 ≤ u) :
    (stdGaussian E).real {z | u ≤ Finset.univ.sup' hn (gramVec v z) -
        ∫ z', Finset.univ.sup' hn (gramVec v z') ∂(stdGaussian E)} ≤
      exp (-u ^ 2 / (2 * (σ : ℝ) ^ 2)) := by
  have h := ((lipschitzWith_sup' hn).comp (lipschitzWith_gramVec hv))
  rw [one_mul] at h
  exact tail_le_of_lipschitz h hu

end GaussConc

end LQGMetric
