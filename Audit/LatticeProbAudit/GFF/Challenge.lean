import Mathlib

/-!
# The discrete Gaussian free field: comparator challenge

Mathlib-only comparator challenge for the discrete Gaussian free field with zero
boundary values, as the library builds it in `LatticeProb/Network/GFF.lean`:
`LatticeProb.Network.killedGreenMatrix_posSemidef`, `LatticeProb.Network.integral_gff`
and `LatticeProb.Network.covariance_gff`.

Content: let `G` be a connected locally finite graph and `C` a finite set of its
vertices that misses some vertex `q`.  The killed Green function `g_C(x, y)` of
simple random walk on `G`, restricted to `C × C`, is a positive semidefinite
matrix, and there is a centred Gaussian measure on `ℝ^C` whose covariance is
`g_C`: the Gaussian free field on `C` with zero boundary values.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and
`VOCABULARY-END` rebuilds the killed Green function from Mathlib primitives: the
averaging operator of simple random walk, the killed transition kernel by its
one-step recursion, and the Green function as the sum over time of the kernel,
divided by the degree of the target.  It is a statement-level copy of the
definitions `walkOp`, `killedHeat`, `killedGreen` and `killedGreenReal` of
`LatticeProb/Graph/Basic.lean`.  The sole intentional `sorry` is the proof of
the final theorem.

## Presentation deltas

The library names the field `gff G C := multivariateGaussian 0 (killedGreenMatrix G C)`;
the challenge asserts that some Gaussian measure with these moments exists, and
states the positive semidefiniteness, on which the construction rests, as a
separate conjunct.
-/

-- VOCABULARY-BEGIN
namespace LatticeProbAudit

open scoped ENNReal

variable {V : Type*}

/-- The one-step averaging operator `(P f)(x) = deg(x)⁻¹ ∑_{y ∼ x} f(y)` of simple
random walk on a locally finite graph. -/
noncomputable def walkOp (G : SimpleGraph V) [G.LocallyFinite] (f : V → ℝ) (x : V) : ℝ :=
  (∑ y ∈ G.neighborFinset x, f y) / G.degree x

open scoped Classical in
/-- The `k`-step transition probability `P_x(X_k = y, X_0, …, X_k ∈ C)` of simple
random walk killed on leaving `C`, by the recursion in the starting point. -/
noncomputable def killedHeat (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) :
    ℕ → V → V → ℝ
  | 0 => fun x y => if x ∈ C then (if x = y then 1 else 0) else 0
  | k + 1 => fun x y => if x ∈ C then walkOp G (fun z => killedHeat G C k z y) x else 0

/-- The killed Green function `g_C(y, v) = E_y[number of visits to v before leaving C] / deg(v)`,
valued in `[0, ∞]`. -/
noncomputable def killedGreen (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y v : V) :
    ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal (killedHeat G C k y v)) / (G.degree v : ℝ≥0∞)

/-- The killed Green function as a real number. -/
noncomputable def killedGreenReal (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (y v : V) :
    ℝ :=
  (killedGreen G C y v).toReal

end LatticeProbAudit
-- VOCABULARY-END

namespace LatticeProbAudit

open MeasureTheory ProbabilityTheory

universe u

/-- The Gaussian free field on a finite set `C` with zero boundary values: the killed
Green function is positive semidefinite on `C`, and it is the covariance of a centred
Gaussian measure on `ℝ^C`. -/
theorem gff {V : Type u} {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (C : Finset V) {q : V} (hq : q ∉ C) :
    (Matrix.of fun x y : C => killedGreenReal G (C : Set V) x y).PosSemidef ∧
      ∃ μ : Measure (EuclideanSpace ℝ C), IsGaussian μ ∧ ∫ φ, φ ∂μ = 0 ∧
        ∀ x y : C, cov[fun φ : EuclideanSpace ℝ C => φ x, fun φ => φ y; μ]
          = killedGreenReal G (C : Set V) x y := by
  sorry

end LatticeProbAudit
