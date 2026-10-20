/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/PolynomialBoundaryApproximation.lean.
-/
import LatticeProb.Analysis.Polynomial.Analytic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Polynomial approximation of continuous functions on compact sets

Coordinate polynomials separate the points of `EuclideanSpace ℝ (Fin d)`. The real
Stone–Weierstrass theorem therefore applies on every compact set `K` in that space: real polynomials
in `d` variables are uniformly dense in the continuous real functions on `K`.

The file builds the restriction homomorphism from polynomials to `C(K, ℝ)`, proves that its range
separates points, and derives uniform approximation of an arbitrary continuous function on `K` by
the evaluation of a single polynomial.
-/

open MvPolynomial
namespace LatticeProb

/-- The restriction of real polynomials in `d` variables to a set `K ⊆ ℝ^d`, as a real algebra
homomorphism into the continuous real functions on `K`. -/
noncomputable def polynomialRestrictionAlgHom {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] C(K, ℝ) where
  toFun p := ⟨fun x ↦ polynomialEval p x.1,
    (contDiff_polynomialEval p (n := 0)).continuous.comp continuous_subtype_val⟩
  map_zero' := by ext x; simp [polynomialEval]
  map_one' := by ext x; simp [polynomialEval]
  map_add' p q := by ext x; simp [polynomialEval]
  map_mul' p q := by ext x; simp [polynomialEval]
  commutes' c := by ext x; simp [polynomialEval]

/-- The restriction homomorphism evaluates a polynomial pointwise on `K`. -/
@[simp] lemma polynomialRestrictionAlgHom_apply {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (p : MvPolynomial (Fin d) ℝ) (x : K) :
    polynomialRestrictionAlgHom K p x = polynomialEval p x.1 := rfl

/-- The range of the restriction homomorphism separates the points of `K`, because the coordinate
polynomials do: two distinct points of `ℝ^d` differ in some coordinate. -/
lemma polynomialRestriction_separatesPoints {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) :
    (polynomialRestrictionAlgHom K).range.SeparatesPoints := by
  classical
  intro x y hxy
  have hcoord : ∃ i : Fin d, x.1 i ≠ y.1 i := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨polynomialRestrictionAlgHom K (X i),
    ⟨polynomialRestrictionAlgHom K (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa [polynomialEval] using hi

/-- Uniform polynomial approximation on a compact set `K ⊆ ℝ^d`: for every continuous `f : K → ℝ`
and every `ε > 0` there is a real polynomial `p` in `d` variables with `|p(x) - f(x)| < ε` for all
`x ∈ K`. No regularity of `K` beyond compactness is needed. -/
theorem exists_polynomial_near_continuous_on_compact {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (f : K → ℝ) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin d) ℝ, ∀ x : K, |polynomialEval p x.1 - f x| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨⟨g, hg⟩, hnear⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (polynomialRestrictionAlgHom K).range (polynomialRestriction_separatesPoints K)
      f hf ε hε
  obtain ⟨p, hp⟩ := hg
  refine ⟨p, fun x ↦ ?_⟩
  have hx := hnear x
  change ‖g x - f x‖ < ε at hx
  rw [← hp] at hx
  change ‖polynomialEval p x.1 - f x‖ < ε at hx
  simpa only [Real.norm_eq_abs] using hx

namespace BoundaryApproximationExample

/-- Nonvacuity: on the closed unit ball of `ℝ²`, which is compact, the continuous function
`x ↦ exp ‖x‖` is approximated within `1/10` by a single real polynomial in two variables. -/
example : ∃ p : MvPolynomial (Fin 2) ℝ,
    ∀ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      |polynomialEval p x.1 - Real.exp ‖x.1‖| < 1 / 10 :=
  exists_polynomial_near_continuous_on_compact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (fun x ↦ Real.exp ‖x.1‖) (by fun_prop) (by norm_num)

end BoundaryApproximationExample

end LatticeProb
