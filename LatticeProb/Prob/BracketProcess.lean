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
  `crossTerm` has conditional mean zero and `E[realizedQVar M T n]` is independent of `n`
  (`integral_crossTerm_eq_zero`, `integral_realizedQVar_succ_eq`).

Not in this file (see the closing note): the existence of the limit `bracket`, the identity
`Martingale.sq_sub_bracket`, and `tendstoInMeasure_realizedQVar_bracket`.  Those are blocked on
a uniform-in-the-mesh convergence estimate that Mathlib does not supply.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*}

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

/-- The `j`-th summand of `crossTerm`: the product of the two halves of the `j`-th refined
increment.  It is the unit whose conditional expectation `condExp_dyadic_cross_eq_zero` kills. -/
def crossIncrement (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n j : ℕ) (ω : Ω) : ℝ :=
  (M (dyadicPoint T (n + 1) (2 * j + 1)) ω - M (dyadicPoint T n j) ω) *
    (M (dyadicPoint T n (j + 1)) ω - M (dyadicPoint T (n + 1) (2 * j + 1)) ω)

/-- `crossTerm` is the sum of its summands. -/
theorem crossTerm_eq_sum (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    crossTerm M T n ω = ∑ j ∈ Finset.range (2 ^ n), crossIncrement M T n j ω := rfl

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
theorem measurable_realizedQVar [MeasurableSpace Ω] (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    (hM : ∀ t, Measurable (M t)) : Measurable (realizedQVar M T n) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((hM _).sub (hM _))).pow_const 2

/-- Measurability of the cross term. -/
theorem measurable_crossTerm [MeasurableSpace Ω] (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
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

/-- The left endpoint precedes the midpoint of a refined increment. -/
theorem dyadicPoint_le_mid (T : ℝ≥0) (n j : ℕ) :
    dyadicPoint T n j ≤ dyadicPoint T (n + 1) (2 * j + 1) := by
  unfold dyadicPoint
  rw [pow_succ]
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have h : (j : ℝ≥0) / 2 ^ n ≤ ((2 * j + 1 : ℕ) : ℝ≥0) / (2 ^ n * 2) := by
    rw [div_le_div_iff₀ h2 (by positivity)]
    push_cast
    nlinarith
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The midpoint of a refined increment precedes the right endpoint. -/
theorem dyadicPoint_mid_le (T : ℝ≥0) (n j : ℕ) :
    dyadicPoint T (n + 1) (2 * j + 1) ≤ dyadicPoint T n (j + 1) := by
  unfold dyadicPoint
  rw [pow_succ]
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have h : ((2 * j + 1 : ℕ) : ℝ≥0) / (2 ^ n * 2) ≤ ((j + 1 : ℕ) : ℝ≥0) / 2 ^ n := by
    rw [div_le_div_iff₀ (by positivity) h2]
    push_cast
    nlinarith
  exact mul_le_mul_of_nonneg_left h (by positivity)

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

/-! ### The martingale cross-term identity -/

/-- **The cross term has conditional mean zero.**  For a martingale `M` and `a ≤ b ≤ c`, the two
halves `(M b - M a)` and `(M c - M b)` of the increment over `[a, c]` are `L²`-orthogonal: the
first is `ℱ b`-measurable, the second is a martingale increment after `b`.  This is the
conditional-mean-zero input of the dyadic convergence argument. -/
theorem condExp_cross_eq_zero [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c)
    (hfg : Integrable ((fun ω => M b ω - M a ω) * fun ω => M c ω - M b ω) μ)
    (hg : Integrable (fun ω => M c ω - M b ω) μ) :
    μ[(fun ω => M b ω - M a ω) * fun ω => M c ω - M b ω | ℱ a] =ᵐ[μ] 0 := by
  have hgb : μ[fun ω => M c ω - M b ω | ℱ b] =ᵐ[μ] 0 := by
    have hsub := condExp_sub (μ := μ) (hM.integrable c) (hM.integrable b) (ℱ b)
    have hcb := hM.condExp_ae_eq hbc
    have hbb : μ[M b | ℱ b] =ᵐ[μ] M b :=
      Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable (ℱ.le b) (hM.stronglyMeasurable b) (hM.integrable b))
    have h : μ[fun ω => M c ω - M b ω | ℱ b] =ᵐ[μ] (M b - M b) :=
      hsub.trans (hcb.sub hbb)
    rw [show (M b - M b) = (0 : Ω → ℝ) from by funext ω; simp] at h
    exact h
  have hf : StronglyMeasurable[ℱ b] (fun ω => M b ω - M a ω) :=
    (hM.stronglyMeasurable b).sub ((hM.stronglyMeasurable a).mono (ℱ.mono hab))
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := ℱ b) hf hfg hg
  have hmid : μ[(fun ω => M b ω - M a ω) * fun ω => M c ω - M b ω | ℱ b] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hgb] with ω e1 e2
    simp only [Pi.mul_apply, Pi.zero_apply] at e1 e2 ⊢
    rw [e1, e2, mul_zero]
  have h0 : μ[μ[(fun ω => M b ω - M a ω) * fun ω => M c ω - M b ω | ℱ b] | ℱ a] =ᵐ[μ] 0 := by
    have h1 := condExp_congr_ae (μ := μ) (m := ℱ a) hmid
    simpa using h1
  exact (condExp_condExp_of_le (μ := μ) (ℱ.mono hab) (ℱ.le b)).symm.trans h0

/-- The `j`-th summand of `crossTerm` has conditional mean zero with respect to the past
σ-algebra `ℱ (dyadicPoint T n j)` at the left endpoint of its increment. -/
theorem condExp_dyadic_cross_eq_zero [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (T : ℝ≥0) (n j : ℕ)
    (hfg : Integrable ((fun ω => M (dyadicPoint T (n + 1) (2 * j + 1)) ω
          - M (dyadicPoint T n j) ω)
        * fun ω => M (dyadicPoint T n (j + 1)) ω
          - M (dyadicPoint T (n + 1) (2 * j + 1)) ω) μ)
    (hg : Integrable (fun ω => M (dyadicPoint T n (j + 1)) ω
          - M (dyadicPoint T (n + 1) (2 * j + 1)) ω) μ) :
    μ[(fun ω => M (dyadicPoint T (n + 1) (2 * j + 1)) ω - M (dyadicPoint T n j) ω)
        * fun ω => M (dyadicPoint T n (j + 1)) ω
          - M (dyadicPoint T (n + 1) (2 * j + 1)) ω
      | ℱ (dyadicPoint T n j)] =ᵐ[μ] 0 :=
  condExp_cross_eq_zero (μ := μ) hM (dyadicPoint_le_mid T n j) (dyadicPoint_mid_le T n j) hfg hg

/-! ### The constant-mean corollary -/

/-- **The cross term integrates to zero.**  Every summand of `crossTerm M T n` has conditional
mean zero for `ℱ (dyadicPoint T n j)` (`condExp_dyadic_cross_eq_zero`), so `∫ crossTerm = 0`. -/
theorem integral_crossTerm_eq_zero [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (T : ℝ≥0) (n : ℕ)
    (hint : ∀ j ∈ Finset.range (2 ^ n), Integrable (crossIncrement M T n j) μ)
    (hintg : ∀ j ∈ Finset.range (2 ^ n),
      Integrable (fun ω => M (dyadicPoint T n (j + 1)) ω
        - M (dyadicPoint T (n + 1) (2 * j + 1)) ω) μ) :
    ∫ ω, crossTerm M T n ω ∂μ = 0 := by
  simp_rw [crossTerm_eq_sum]
  rw [integral_finsetSum _ (fun j hj => hint j hj)]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hcond := condExp_dyadic_cross_eq_zero (μ := μ) hM T n j (hint j hj) (hintg j hj)
  rw [← integral_condExp (μ := μ) (m := ℱ (dyadicPoint T n j)) (ℱ.le _)
    (f := crossIncrement M T n j)]
  exact integral_eq_zero_of_ae hcond

/-- **The mean of the realized quadratic variation is independent of the mesh.**  From the
cross-term splitting and `integral_crossTerm_eq_zero`. -/
theorem integral_realizedQVar_succ_eq [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (T : ℝ≥0) (n : ℕ)
    (hQ : Integrable (realizedQVar M T (n + 1)) μ)
    (hcross : Integrable (crossTerm M T n) μ)
    (hint : ∀ j ∈ Finset.range (2 ^ n), Integrable (crossIncrement M T n j) μ)
    (hintg : ∀ j ∈ Finset.range (2 ^ n),
      Integrable (fun ω => M (dyadicPoint T n (j + 1)) ω
        - M (dyadicPoint T (n + 1) (2 * j + 1)) ω) μ) :
    ∫ ω, realizedQVar M T n ω ∂μ = ∫ ω, realizedQVar M T (n + 1) ω ∂μ := by
  have hcross0 := integral_crossTerm_eq_zero (μ := μ) hM T n hint hintg
  calc ∫ ω, realizedQVar M T n ω ∂μ
      = ∫ ω, (realizedQVar M T (n + 1) ω + 2 * crossTerm M T n ω) ∂μ :=
        integral_congr_ae
          (Filter.Eventually.of_forall fun ω => realizedQVar_eq_succ_add_cross M T n ω)
    _ = ∫ ω, realizedQVar M T (n + 1) ω ∂μ + ∫ ω, 2 * crossTerm M T n ω ∂μ :=
        integral_add hQ (hcross.const_mul 2)
    _ = ∫ ω, realizedQVar M T (n + 1) ω ∂μ + 2 * ∫ ω, crossTerm M T n ω ∂μ := by
        rw [integral_const_mul]
    _ = ∫ ω, realizedQVar M T (n + 1) ω ∂μ := by rw [hcross0, mul_zero, add_zero]

end LatticeProb

/-!
## The obstruction to `bracket`, `sq_sub_bracket` and the in-measure convergence

Nothing above produces the limit `bracket M ℱ P T`, the martingale identity
`fun t ω => M t ω ^ 2 - bracket M ℱ P t ω`, or the convergence
`realizedQVar M T n →ᵢ bracket M ℱ P T`.  Those are blocked on the same missing estimate.

What is proved here is the algebraic and conditional-moment backbone:

* `realizedQVar_eq_succ_add_cross`: `Q_n = Q_{n+1} + 2 * crossTerm_n`;
* `condExp_cross_eq_zero` and `condExp_dyadic_cross_eq_zero`: every summand of `crossTerm_n`
  has conditional mean zero, so `∫ crossTerm_n = 0` (given integrability) and the **mean of `Q_n`
  is independent of `n`** — the martingale property of the level sums.

What is missing is the estimate that upgrades "constant mean" to "convergent".  The standard
route for a bounded continuous martingale `M` is

  `E[(Q_{n+1} - Q_n)²] = 4 ∑_j E[(Δ₁ Δ₂)²] ≤ C E[Q_{n+1} · osc_n²]`,

where `osc_n = sup_j |M(mid_j) - M(left_j)|` is the mesh oscillation, `osc_n → 0` almost surely
by uniform continuity of the paths on `[0, T]`, and `Q_{n+1}` is bounded (for bounded `M`).  The
crude bound `E[(Δ₁ Δ₂)²] ≤ 4K² E[Δ₁²]` is independent of `n` and does **not** suffice.

The precise missing lemmas:

```
theorem tendsto_zero_sq_increment_realizedQVar {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hcont : ∀ ω, Continuous fun t => M t ω)
    (hbound : ∃ K, ∀ t ω, |M t ω| ≤ K) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (realizedQVar M T (n + 1) ω - realizedQVar M T n ω) ^ 2 ∂μ)
      atTop (𝓝 0)

theorem exists_bracket ... : ∃ A : ℝ≥0 → Ω → ℝ, (∀ t, A t =ᵐ[μ] limUnder atTop (realizedQVar M t ·)) ∧ ...

theorem Martingale.sq_sub_bracket ... : Martingale (fun t ω => M t ω ^ 2 - bracket M ℱ μ t ω) ℱ μ
```

Mathlib supplies neither a continuous-time Doob–Meyer decomposition nor the uniform-in-the-mesh
moment estimate, and has no continuous-time optional stopping; the first lemma above is the
research-level bottleneck.  Until it is available, `bracket` cannot be defined without junk.
-/
