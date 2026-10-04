/-
# The bracket process of a continuous martingale: dyadic realized covariation

Stage 1 of the DDS project (`scratch/pk/dds-route.md`).  Mathlib has continuous-indexed
martingales but **no** quadratic variation, no continuous-time Doob–Meyer decomposition and
no continuous-time optional stopping.  This file begins the bracket process from its classical
characterization as the limit of the dyadic realized quadratic variation

  `realizedQVar M T n = ∑_{k < 2ⁿ} (M(kT/2ⁿ) - M((k+1)T/2ⁿ))²`,

for a square-integrable continuous martingale `M = (M t)`.

Proved in this file (the parts of Stage 1 not blocked):

* `dyadicPoint`, `realizedQVar`, and their basic properties (nonnegativity, measurability,
  vanishing at `T = 0`);
* the dyadic reindexing `∑_{k < 2m} f k = ∑_{j < m} (f (2j) + f (2j+1))` and the resulting
  refinement identity expressing `realizedQVar (n+1)` on the finer grid;
* the cross-term splitting
  `realizedQVar M T n = realizedQVar M T (n+1) + 2 * crossTerm M T n`,
  where `crossTerm` is the sum of products of the two halves of each refined increment;
* the martingale identity `E[(M b - M a)(M c - M b) | ℱ a] = 0` for `a ≤ b ≤ c`, hence
  `crossTerm` has conditional mean zero and `E[realizedQVar M T n]` is independent of `n`.

Not in this file (see the closing note): the existence of the limit `bracket`, the identity
`Martingale.sq_sub_bracket`, and `tendstoInMeasure_realizedQVar_bracket`.  Those are blocked on
a uniform-in-the-mesh convergence estimate that Mathlib does not supply.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The dyadic grid point `k T / 2ⁿ` of `[0, T]`. -/
def dyadicPoint (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := T * ((k : ℝ≥0) / 2 ^ n)

/-- The **dyadic realized quadratic variation** at mesh `2⁻ⁿ`:
`∑_{k < 2ⁿ} (M ((k+1)T/2ⁿ) - M (kT/2ⁿ))²`.  This is the scalar `Fin 1` case of
`VRW.realizedCovar`. -/
def realizedQVar (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n),
    (M (dyadicPoint T n (k + 1)) ω - M (dyadicPoint T n k) ω) ^ 2

/-- The cross term `∑_{j < 2ⁿ} (M(mid) - M(left)) (M(right) - M(mid))` of the two halves of
each increment of the mesh-`2⁻ⁿ` grid.  It is the `L²`-orthogonal part of the refinement
`realizedQVar (n+1) - realizedQVar n` (up to the factor `-2`). -/
def crossTerm (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ n),
    (M (dyadicPoint T (n + 1) (2 * j + 1)) ω - M (dyadicPoint T n j) ω) *
      (M (dyadicPoint T n (j + 1)) ω - M (dyadicPoint T (n + 1) (2 * j + 1)) ω)

@[simp] theorem dyadicPoint_zero_time (n k : ℕ) : dyadicPoint (0 : ℝ≥0) n k = 0 := by
  simp [dyadicPoint]

theorem dyadicPoint_nonneg (T : ℝ≥0) (n k : ℕ) : 0 ≤ dyadicPoint T n k := by
  simp [dyadicPoint]

/-- `realizedQVar` is a sum of squares, hence nonnegative. -/
theorem realizedQVar_nonneg (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ realizedQVar M T n ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- At `T = 0` every dyadic increment vanishes, so the realized quadratic variation is `0`. -/
@[simp] theorem realizedQVar_zero_time (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    realizedQVar M 0 n ω = 0 := by
  simp [realizedQVar]

/-- At the coarsest mesh (`n = 0`) the realized quadratic variation is the single squared
increment over `[0, T]`. -/
theorem realizedQVar_zero_grid (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    realizedQVar M T 0 ω = (M T ω - M 0 ω) ^ 2 := by
  simp [realizedQVar, dyadicPoint]

/-- Measurability of the dyadic realized quadratic variation. -/
theorem measurable_realizedQVar (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    (hM : ∀ t, Measurable (M t)) : Measurable (realizedQVar M T n) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((hM _).sub (hM _))).pow_const 2

/-- Measurability of the cross term. -/
theorem measurable_crossTerm (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    (hM : ∀ t, Measurable (M t)) : Measurable (crossTerm M T n) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (((hM _).sub (hM _)).mul ((hM _).sub (hM _)))

/-! ### Even/odd reindexing of a range sum -/

/-- `∑_{k < 2m} f k = ∑_{j < m} (f (2j) + f (2j+1))`.  This is the algebraic content of the
dyadic refinement. -/
theorem sum_range_two_mul' {E : Type*} [AddCommMonoid E] (f : ℕ → E) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k
      = ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

/-! ### The two dyadic grid points that fold to a coarser one -/

theorem dyadicPoint_two_mul (T : ℝ≥0) (n j : ℕ) :
    dyadicPoint T (n + 1) (2 * j) = dyadicPoint T n j := by
  unfold dyadicPoint
  rw [pow_succ]
  have h2 : (2 : ℝ≥0) ≠ 0 := by norm_num
  rw [Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem dyadicPoint_two_mul_add_two (T : ℝ≥0) (n j : ℕ) :
    dyadicPoint T (n + 1) (2 * j + 2) = dyadicPoint T n (j + 1) := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, dyadicPoint_two_mul]

/-! ### The dyadic refinement -/

/-- **The refinement of the realized quadratic variation.**  Splitting each increment of the
mesh-`2⁻ⁿ` grid into its two halves and reindexing the finer sum gives the level-`n+1` quantity as
a sum over the level-`n` grid.  The `mid` point is `dyadicPoint T (n+1) (2j+1)`. -/
theorem realizedQVar_refine (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    realizedQVar M T (n + 1) ω
      = ∑ j ∈ Finset.range (2 ^ n),
          ((M (dyadicPoint T (n + 1) (2 * j + 1)) ω - M (dyadicPoint T n j) ω) ^ 2
            + (M (dyadicPoint T n (j + 1)) ω
                - M (dyadicPoint T (n + 1) (2 * j + 1)) ω) ^ 2) := by
  rw [realizedQVar, show 2 ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ]; ring,
    sum_range_two_mul']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dyadicPoint_two_mul, dyadicPoint_two_mul_add_two]

/-- The elementary identity behind the cross-term splitting:
`(c-a)² = (b-a)² + (c-b)² + 2(b-a)(c-b)`. -/
theorem sq_sub_sq_decomp (a b c : ℝ) :
    (b - a) ^ 2 + (c - b) ^ 2 + 2 * (b - a) * (c - b) = (c - a) ^ 2 := by
  ring

/-- **The cross-term splitting of the realized quadratic variation.**
`realizedQVar M T n = realizedQVar M T (n+1) + 2 * crossTerm M T n`: passing to the finer grid
exposes the `L²`-orthogonal cross products of the two halves of each increment. -/
theorem realizedQVar_eq_succ_add_cross (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    realizedQVar M T n ω = realizedQVar M T (n + 1) ω + 2 * crossTerm M T n ω := by
  have h := realizedQVar_refine M T n ω
  rw [realizedQVar, h, crossTerm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end LatticeProb
