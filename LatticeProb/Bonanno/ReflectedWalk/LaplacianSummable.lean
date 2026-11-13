/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.LaplacianSummable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Harmonic
import Mathlib.Data.Prod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Absolute convergence of the Laplacian sum (Gwynne–Sung, p. 14)

Footnote 2 of Gwynne–Sung requires the discrete Laplacian sum of Definition 1.2 to
converge absolutely.  In the proof of Proposition 1.3 (p. 14) this is discharged by the
Cauchy–Schwarz inequality together with (1.2):

  `∑_{y ∼ x} c(x,y) |h(y) − h(x)| ≤ √(π(x) · Energy(h)) < ∞`.

With our convention `Energy = ½ ∑_{ordered pairs}` the bound reads
`√(π(x) · 2 · Energy(h))`.  The proof factors
`c(x,y)|h(y)−h(x)| = √(c(x,y)) · √(c(x,y)(h(y)−h(x))²)` and applies the finite
Cauchy–Schwarz inequality to every finite partial sum.  The partial sums of the two
squared families are bounded by `π(x)` (by `summable_c`, i.e. (1.2)) and by
`2 · Energy(h)` (because `y ↦ c(x,y)(h(y)−h(x))²` is a slice of the summable family
`gradSq h` on `V × V`).  Summability and the `tsum` bound then both follow from the
uniform bound on partial sums of a nonnegative family.
-/

namespace ReflectedWalk

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- Nonnegativity of the ordered-pair energy summand.  Local helper: the Energy
package's own nonnegativity lemma is not part of the frozen interface, so this file
does not consume it. -/
private lemma gradSq_nonneg' (f : V → ℝ) (p : V × V) : 0 ≤ G.gradSq f p :=
  mul_nonneg (G.c_nonneg _ _) (sq_nonneg _)

/-- For fixed `x`, the slice `y ↦ gradSq h (x, y)` of a finite-energy function is
summable: the inner sum `∑_{y∼x} c(x,y)|h(y)−h(x)|²` on p. 14 of Gwynne–Sung is finite. -/
lemma summable_gradSq_slice {h : V → ℝ} (hh : G.HasFiniteEnergy h) (x : V) :
    Summable fun y => G.gradSq h (x, y) :=
  hh.comp_injective (Prod.mk_right_injective x)

/-- The slice sum `∑_{y} gradSq h (x, y)` is bounded by the full energy sum
`2 · Energy h` (Gwynne–Sung p. 14, the inner sum is at most the total energy). -/
lemma tsum_gradSq_slice_le {h : V → ℝ} (hh : G.HasFiniteEnergy h) (x : V) :
    ∑' y, G.gradSq h (x, y) ≤ 2 * G.Energy h := by
  rw [← G.tsum_gradSq_eq h]
  exact Summable.tsum_le_tsum_of_inj (fun y => (x, y)) (Prod.mk_right_injective x)
    (fun p _ => gradSq_nonneg' G h p) (fun _ => le_rfl) (G.summable_gradSq_slice hh x) hh

/-- The pointwise factorisation `c(x,y)|h(y)−h(x)| = √(c(x,y)) · √(gradSq h (x,y))`
behind the Cauchy–Schwarz step on p. 14 of Gwynne–Sung. -/
lemma c_mul_abs_eq_sqrt_mul_sqrt (h : V → ℝ) (x y : V) :
    G.c x y * |h y - h x| = Real.sqrt (G.c x y) * Real.sqrt (G.gradSq h (x, y)) := by
  show G.c x y * |h y - h x| = Real.sqrt (G.c x y) * Real.sqrt (G.c x y * (h y - h x) ^ 2)
  rw [Real.sqrt_mul (G.c_nonneg x y), Real.sqrt_sq_eq_abs, ← mul_assoc,
    Real.mul_self_sqrt (G.c_nonneg x y)]

/-- **Cauchy–Schwarz for finite partial sums** (Gwynne–Sung p. 14): every finite partial
sum of `∑_{y∼x} c(x,y)|h(y)−h(x)|` is bounded by `√(π(x) · 2 · Energy h)`. -/
lemma sum_c_mul_abs_le {h : V → ℝ} (hh : G.HasFiniteEnergy h) (x : V) (s : Finset V) :
    ∑ y ∈ s, G.c x y * |h y - h x| ≤ Real.sqrt (G.pi x * (2 * G.Energy h)) := by
  have hcs : ∑ y ∈ s, G.c x y * |h y - h x|
      ≤ Real.sqrt (∑ y ∈ s, G.c x y) * Real.sqrt (∑ y ∈ s, G.gradSq h (x, y)) := by
    simp_rw [G.c_mul_abs_eq_sqrt_mul_sqrt h x]
    exact Real.sum_sqrt_mul_sqrt_le s (fun y => G.c_nonneg x y)
      (fun y => gradSq_nonneg' G h (x, y))
  have h1 : ∑ y ∈ s, G.c x y ≤ G.pi x :=
    (G.summable_c x).sum_le_tsum s (fun y _ => G.c_nonneg x y)
  have h2 : ∑ y ∈ s, G.gradSq h (x, y) ≤ 2 * G.Energy h :=
    ((G.summable_gradSq_slice hh x).sum_le_tsum s (fun y _ => gradSq_nonneg' G h (x, y))).trans
      (G.tsum_gradSq_slice_le hh x)
  refine hcs.trans ?_
  rw [Real.sqrt_mul (G.pi_nonneg x)]
  exact mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- Finite energy forces the Definition 1.2 sum to converge absolutely, with the
Cauchy–Schwarz bound `∑_{y∼x} c(x,y)|h(y)−h(x)| ≤ √(π(x) · 2 · Energy h)` used on
p. 14 of the paper (proof of Proposition 1.3; this discharges footnote 2). -/
theorem absSummableAt_of_hasFiniteEnergy {h : V → ℝ} (hh : G.HasFiniteEnergy h) (x : V) :
    G.AbsSummableAt h x := by
  unfold AbsSummableAt
  exact summable_of_sum_le (fun y => mul_nonneg (G.c_nonneg x y) (abs_nonneg (h y - h x)))
    (G.sum_c_mul_abs_le hh x)

/-- The Cauchy–Schwarz bound of Gwynne–Sung p. 14 (proof of Proposition 1.3):
`∑_{y∼x} c(x,y)|h(y)−h(x)| ≤ √(π(x) · 2 · Energy h)`, with `2 · Energy h` the ordered-pair
energy sum. -/
theorem tsum_abs_lapTerm_le {h : V → ℝ} (hh : G.HasFiniteEnergy h) (x : V) :
    ∑' y, G.c x y * |h y - h x| ≤ Real.sqrt (G.pi x * (2 * G.Energy h)) :=
  Real.tsum_le_of_sum_le (fun y => mul_nonneg (G.c_nonneg x y) (abs_nonneg (h y - h x)))
    (G.sum_c_mul_abs_le hh x)

end ConductanceGraph

end ReflectedWalk
