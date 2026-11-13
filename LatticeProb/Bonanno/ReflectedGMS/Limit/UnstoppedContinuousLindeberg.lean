/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.UnstoppedContinuousLindeberg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ConditionalGaussianIdentification
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact

/-!
# The Lindeberg condition for the unstopped continuous limit martingale

`ReflectedGMS.MartingaleLimit.map_increment_eq_gaussianReal_of_square_martingale`
identifies the increment law of a square-compensated martingale from the exact
deterministic conditional variance (already unlocalized) together with the
vanishing of the Lindeberg sums `lindebergSum P M δ s t n`.  Every existing
supplier of that last input, namely
`ReflectedGMS.MartingaleLimit.continuous_martingale_lindeberg_tendsto_zero`,
carries a *uniform path bound* `|M u ω| ≤ K`, so it only applies to a stopped
process.

This file removes the path bound.  The localization is performed **on the grid
itself**, which avoids continuous-time hitting times, optional sampling and any
stopped-process martingale theory: with
`A i = {ω | ∀ k ≤ i, |M (g k) ω - M (g 0) ω| ≤ K}`
(an `𝔽 (g i)`-event) one splits `1 = 1_{A (i+1)} + 1_{A i \ A (i+1)} + 1_{A iᶜ}`.

* on `A iᶜ` the exact set-integral identity
  `setIntegral_increment_sq_eq_of_square_martingale` gives
  `∑ᵢ E[Δᵢ² 1_{A iᶜ}] = C (t-s) P(A iᶜ)`, with no path bound at all;
* the exit steps `A i \ A (i+1)` are **pairwise disjoint**, and on them
  `Δᵢ² ≤ 4 (M (g (i+1)) - M (g 0))²` because the cap fails exactly at `i+1`;
  the orthogonality identity `setIntegral_increment_sq_split` then dominates
  each of them by `(M (g n) - M (g 0))²` on the same set, and the telescoping
  of the indicators sums them to `E[(M t - M s)² 1_{A nᶜ}]`.  The same
  computation is the sharp maximal inequality `K² P(A nᶜ) ≤ E[X² 1_{A nᶜ}]`.
  This is the uniform integrability that a constant expected quadratic sum
  cannot provide, obtained here with **no fourth moment**;
* on `A (i+1)` both endpoints are capped, so the truncated increments
  `Q i = Δᵢ² 1_{A (i+1)}` are bounded by `4 K²` and the exact conditional
  variance gives the partition-uniform `L²` bound
  `E[(∑ᵢ Q i)²] ≤ C² (t-s)² + 4 K² C (t-s)`, which the elementary
  `S 1_B ≤ lam 1_B + S²/lam` device converts into a Lindeberg bound driven by
  the probability of a large increment; that probability vanishes by uniform
  continuity of the paths on the compact interval `[s, t]`.

No stopping time, no localizing sequence, no Lévy characterisation, no assumed
uniform integrability and no assumed Lindeberg premise are used.

## Main results

* `setIntegral_increment_sq_split` — orthogonality of martingale increments in
  set-integral form.
* `gridCapSet` and its measurability/monotonicity API.
* `sum_setIntegral_exit_step_le` — the disjoint exit-step estimate.
* `gridCap_exit_measure_sq_le` — the sharp grid maximal inequality.
* `truncated_grid_quadratic_sq_integral_le` — the partition-uniform `L²` bound
  for the capped realized quadratic sum.
* `gridLindebergSum_le` — the full one-partition estimate.
* `unstopped_grid_lindeberg_tendsto_zero` — the Lindeberg condition along
  arbitrary deterministic mesh-refining grids of `[s, t]`.
* `unstopped_lindebergSum_tendsto_zero` — the same in the exact
  `lindebergSum` form consumed by the Gaussian identification.
* `map_increment_eq_gaussianReal_of_continuous_square_martingale` — the
  resulting unconditional Gaussian increment law.
-/

-- Merged from `ReflectedGMS/Limit/GaussianIdentificationUnlocalization.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_GaussianIdentificationUnlocalization

/-!
# Exact conditional increment variance for the unstopped limit martingale

`ReflectedGMS.MartingaleLimit.map_increment_eq_gaussianReal` identifies the law
of a martingale increment `M t - M s` as `gaussianReal 0 (C (t - s))` from three
inputs: square integrability of the increments, the **exact deterministic**
conditional second moment `P[(M b - M a)² | 𝔽 a] = C (b - a)`, and the vanishing
of the Lindeberg sums along the uniform partitions of `[s, t]`.

Every existing supplier of a conditional second moment in this development is
*localized*: `ReflectedGMS.MartingaleLimit.increment_sq_integral_le` and the
whole of `ContinuousMartingaleLindeberg` only ever assume the one-sided bound
`P[(M u - M s)² | 𝔽 s] ≤ C (u - s)`, which is what stopping a process with a
deterministic bracket produces, and they additionally carry a uniform path bound
`|M u| ≤ K`.  A one-sided bound can never be fed to
`map_increment_eq_gaussianReal`, whose conditional variance is used as an
identity and not as a bound.

This file closes exactly that gap.  It derives the **exact** conditional
increment variance from the square-martingale (square-compensated) property

`Martingale (fun u ω ↦ M u ω ^ 2 - C u) 𝔽 P`,

for the *unstopped* process and **without any path bound, stopping time or
localizing sequence**.  The only extra hypothesis is the honest square
integrability `∀ u, MemLp (M u) 2 P`, which is already implied by the
square-martingale hypothesis itself in every use in this development: the
compensated process `M u ² - C u` is integrable by `Martingale.integrable`, so
`M u ²` is integrable, i.e. `M u ∈ L²`.  (It is kept as a hypothesis rather than
rederived because the `MemLp` form is what the pull-out lemma consumes and what
the callers already have.)

## Main results

* `condExp_sub_sq_eq_of_condExp_sq`: the abstract two-variable identity
  `P[(Y - X)² | m] = c` from `P[Y | m] = X` and `P[Y² | m] = X² + c`.  Only the
  pull-out property of the conditional expectation is used.
* `condExp_increment_sq_eq_of_square_martingale`: the **exact deterministic
  conditional increment variance** `P[(M b - M a)² | 𝔽 a] = C (b - a)` for a
  square-compensated martingale.  No localization.
* `integrable_increment_sq_of_memLp`: the square integrability input.
* `setIntegral_increment_sq_eq_of_square_martingale`: the exact set-integral form
  `∫_A (M b - M a)² = P(A) · C (b - a)` for `A ∈ 𝔽 a`, the unlocalized estimate
  for the part of a Lindeberg sum carried by an already-realized past event.
* `zero_le_rate_of_square_martingale`: the rate `C` is automatically nonnegative.
* `condExp_cexp_increment_eq_exp_of_square_martingale`,
  `indepFun_increment_of_square_martingale` and
  `map_increment_eq_gaussianReal_of_square_martingale`: the resulting unstopped
  Gaussian identification, whose only remaining probabilistic input is the
  Lindeberg condition.

Nothing here assumes Gaussian increments, a Lévy characterisation, independence,
or the Lindeberg conclusion itself.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.MartingaleLimit

/-! ### The abstract conditional-variance identity -/

/-! ### The exact conditional increment variance of a square-compensated
martingale -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝔽 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- Square integrability of the increments, from square integrability of the
process.  This is the `hsq` input of `map_increment_eq_gaussianReal`. -/
theorem integrable_increment_sq_of_memLp (h2 : ∀ u : ℝ≥0, MemLp (M u) 2 P) (a b : ℝ≥0) :
    Integrable (fun ω => (M b ω - M a ω) ^ 2) P :=
  ((h2 b).sub (h2 a)).integrable_sq

/-! ### The unstopped Gaussian identification -/

end ReflectedGMS.MartingaleLimit

end Merged_GaussianIdentificationUnlocalization

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝔽 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-! ### Orthogonality of martingale increments -/

/-- A later increment is orthogonal to every square-integrable variable measured
at its left endpoint.  Only the pull-out property of the conditional expectation
is used. -/
theorem integral_mul_increment_eq_zero [IsFiniteMeasure P]
    (hM : Martingale M 𝔽 P) (h2 : ∀ v : ℝ≥0, MemLp (M v) 2 P)
    {u b : ℝ≥0} (hub : u ≤ b) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝔽 u] Z) (hZ2 : MemLp Z 2 P) :
    (∫ ω, Z ω * (M b ω - M u ω) ∂P) = 0 := by
  have hdiff : MemLp (fun ω => M b ω - M u ω) 2 P := (h2 b).sub (h2 u)
  have hgint : Integrable (fun ω => M b ω - M u ω) P :=
    (hM.integrable b).sub (hM.integrable u)
  have hfg : Integrable (fun ω => Z ω * (M b ω - M u ω)) P := hZ2.integrable_mul hdiff
  have hpull : P[fun ω => Z ω * (M b ω - M u ω) | 𝔽 u] =ᵐ[P]
      fun ω => Z ω * (P[fun ω => M b ω - M u ω | 𝔽 u]) ω :=
    condExp_mul_of_stronglyMeasurable_left hZ hfg hgint
  have hzero : P[fun ω => M b ω - M u ω | 𝔽 u] =ᵐ[P] fun _ => (0 : ℝ) := by
    have hsub : P[(M b - M u : Ω → ℝ) | 𝔽 u] =ᵐ[P] P[M b | 𝔽 u] - P[M u | 𝔽 u] :=
      condExp_sub (hM.integrable b) (hM.integrable u) (𝔽 u)
    filter_upwards [hsub, hM.condExp_ae_eq hub, hM.condExp_ae_eq (le_refl u)] with ω e1 e2 e3
    simp only [Pi.sub_apply] at e1
    show (P[fun ω => M b ω - M u ω | 𝔽 u]) ω = 0
    have e1' : (P[fun ω => M b ω - M u ω | 𝔽 u]) ω
        = (P[M b | 𝔽 u]) ω - (P[M u | 𝔽 u]) ω := e1
    rw [e1', e2, e3, sub_self]
  calc (∫ ω, Z ω * (M b ω - M u ω) ∂P)
      = ∫ ω, (P[fun ω => Z ω * (M b ω - M u ω) | 𝔽 u]) ω ∂P :=
        (integral_condExp (𝔽.le u)).symm
    _ = ∫ _ω : Ω, (0 : ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hzero] with ω e1 e2
        rw [e1, e2, mul_zero]
    _ = 0 := integral_zero _ _

/-! ### The grid cap sets -/

/-- The event that the process, sampled along the grid `g`, has stayed within
distance `K` of its starting value up to the `i`-th grid point. -/
def gridCapSet (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (K : ℝ) (i : ℕ) : Set Ω :=
  {ω | ∀ k, k ≤ i → |M (g k) ω - M (g 0) ω| ≤ K}

theorem gridCapSet_eq_biInter (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (K : ℝ) (i : ℕ) :
    gridCapSet M g K i
      = ⋂ k ∈ Finset.range (i + 1), {ω | |M (g k) ω - M (g 0) ω| ≤ K} := by
  ext ω
  simp only [gridCapSet, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]

theorem gridCapSet_subset (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (K : ℝ) {i j : ℕ} (hij : i ≤ j) :
    gridCapSet M g K j ⊆ gridCapSet M g K i :=
  fun _ hω k hk => hω k (hk.trans hij)

theorem gridCapSet_zero (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) {K : ℝ} (hK : 0 ≤ K) :
    gridCapSet M g K 0 = (Set.univ : Set Ω) := by
  ext ω
  simp only [gridCapSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro k hk
  obtain rfl : k = 0 := Nat.le_zero.1 hk
  simpa using hK

theorem measurableSet_gridCapSet (hM : Martingale M 𝔽 P) {g : ℕ → ℝ≥0}
    (hg : Monotone g) (K : ℝ) (i : ℕ) :
    MeasurableSet[𝔽 (g i)] (gridCapSet M g K i) := by
  rw [gridCapSet_eq_biInter]
  refine Finset.measurableSet_biInter _ fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h1 : StronglyMeasurable[𝔽 (g i)] (M (g k)) :=
    (hM.stronglyMeasurable (g k)).mono (𝔽.mono (hg hk'))
  have h0 : StronglyMeasurable[𝔽 (g i)] (M (g 0)) :=
    (hM.stronglyMeasurable (g 0)).mono (𝔽.mono (hg (Nat.zero_le i)))
  have hmeas : Measurable[𝔽 (g i)] fun ω => |M (g k) ω - M (g 0) ω| :=
    continuous_abs.measurable.comp ((h1.sub h0).measurable)
  exact hmeas measurableSet_Iic

/-- Inside the cap at step `i + 1` both endpoints of the `i`-th increment are
within `K` of the starting value, so the increment is bounded by `2 K`. -/
theorem abs_increment_le_of_mem_gridCapSet {M : ℝ≥0 → Ω → ℝ} {g : ℕ → ℝ≥0} {K : ℝ}
    {i : ℕ} {ω : Ω} (hω : ω ∈ gridCapSet M g K (i + 1)) :
    |M (g (i + 1)) ω - M (g i) ω| ≤ 2 * K := by
  have h1 : |M (g (i + 1)) ω - M (g 0) ω| ≤ K := hω (i + 1) le_rfl
  have h2 : |M (g i) ω - M (g 0) ω| ≤ K := hω i (Nat.le_succ i)
  have hsplit : M (g (i + 1)) ω - M (g i) ω
      = (M (g (i + 1)) ω - M (g 0) ω) - (M (g i) ω - M (g 0) ω) := by ring
  rw [hsplit]
  calc |(M (g (i + 1)) ω - M (g 0) ω) - (M (g i) ω - M (g 0) ω)|
      ≤ |M (g (i + 1)) ω - M (g 0) ω| + |M (g i) ω - M (g 0) ω| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-- On an exit step the cap fails exactly at the right endpoint. -/
theorem sq_le_of_mem_exit_step {M : ℝ≥0 → Ω → ℝ} {g : ℕ → ℝ≥0} {K : ℝ}
    {i : ℕ} {ω : Ω} (hω : ω ∈ gridCapSet M g K i \ gridCapSet M g K (i + 1)) :
    K ^ 2 ≤ (M (g (i + 1)) ω - M (g 0) ω) ^ 2 ∧
      (M (g (i + 1)) ω - M (g i) ω) ^ 2 ≤ 4 * (M (g (i + 1)) ω - M (g 0) ω) ^ 2 := by
  have hfail : ¬ |M (g (i + 1)) ω - M (g 0) ω| ≤ K := by
    intro hle
    refine hω.2 ?_
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk' | rfl
    · exact hω.1 k (Nat.lt_succ_iff.1 hk')
    · exact hle
  have hKlt : K < |M (g (i + 1)) ω - M (g 0) ω| := lt_of_not_ge hfail
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (M (g i) ω - M (g 0) ω)) (hω.1 i le_rfl)
  have h1 : K ^ 2 ≤ (M (g (i + 1)) ω - M (g 0) ω) ^ 2 := by
    nlinarith [sq_abs (M (g (i + 1)) ω - M (g 0) ω), abs_nonneg (M (g (i + 1)) ω - M (g 0) ω)]
  refine ⟨h1, ?_⟩
  have hbd : |M (g i) ω - M (g 0) ω| ≤ K := hω.1 i le_rfl
  have h2 : (M (g i) ω - M (g 0) ω) ^ 2 ≤ K ^ 2 := by
    nlinarith [sq_abs (M (g i) ω - M (g 0) ω), abs_nonneg (M (g i) ω - M (g 0) ω)]
  nlinarith [h1, h2,
    sq_nonneg (M (g (i + 1)) ω - M (g 0) ω + (M (g i) ω - M (g 0) ω))]

/-! ### The disjoint exit-step estimate -/

/-! ### The capped realized quadratic sum -/

/-- The `i`-th squared increment, truncated to the event that the sampled path is
still capped at step `i + 1`.  Both endpoints are then within `K` of the starting
value, so this is bounded by `4 K²` without any assumption on the paths of `M`. -/
noncomputable def cappedIncrementSq (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (K : ℝ) (i : ℕ) :
    Ω → ℝ :=
  Set.indicator (gridCapSet M g K (i + 1)) (fun ω => (M (g (i + 1)) ω - M (g i) ω) ^ 2)

theorem cappedIncrementSq_nonneg (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (K : ℝ) (i : ℕ) (ω : Ω) :
    0 ≤ cappedIncrementSq M g K i ω :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω

theorem cappedIncrementSq_le_sq (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0) (K : ℝ) (i : ℕ) (ω : Ω) :
    cappedIncrementSq M g K i ω ≤ (M (g (i + 1)) ω - M (g i) ω) ^ 2 := by
  by_cases hω : ω ∈ gridCapSet M g K (i + 1)
  · rw [cappedIncrementSq, Set.indicator_of_mem hω]
  · rw [cappedIncrementSq, Set.indicator_of_notMem hω]
    exact sq_nonneg _

theorem cappedIncrementSq_le_bound {K : ℝ} (hK : 0 ≤ K) (M : ℝ≥0 → Ω → ℝ) (g : ℕ → ℝ≥0)
    (i : ℕ) (ω : Ω) : cappedIncrementSq M g K i ω ≤ 4 * K ^ 2 := by
  by_cases hω : ω ∈ gridCapSet M g K (i + 1)
  · rw [cappedIncrementSq, Set.indicator_of_mem hω]
    have hb := abs_increment_le_of_mem_gridCapSet hω
    nlinarith [abs_nonneg (M (g (i + 1)) ω - M (g i) ω),
      sq_abs (M (g (i + 1)) ω - M (g i) ω)]
  · rw [cappedIncrementSq, Set.indicator_of_notMem hω]
    positivity

theorem stronglyMeasurable_cappedIncrementSq (hM : Martingale M 𝔽 P) {g : ℕ → ℝ≥0}
    (hg : Monotone g) (K : ℝ) (i : ℕ) :
    StronglyMeasurable[𝔽 (g (i + 1))] (cappedIncrementSq M g K i) := by
  refine StronglyMeasurable.indicator ?_ (measurableSet_gridCapSet hM hg K (i + 1))
  exact ((hM.stronglyMeasurable (g (i + 1))).sub
    ((hM.stronglyMeasurable (g i)).mono (𝔽.mono (hg (Nat.le_succ i))))).pow 2

theorem integrable_cappedIncrementSq [IsFiniteMeasure P] (hM : Martingale M 𝔽 P)
    {g : ℕ → ℝ≥0} (hg : Monotone g) {K : ℝ} (hK : 0 ≤ K) (i : ℕ) :
    Integrable (cappedIncrementSq M g K i) P := by
  refine Integrable.of_bound
    (((stronglyMeasurable_cappedIncrementSq hM hg K i).mono
      (𝔽.le (g (i + 1)))).aestronglyMeasurable) (4 * K ^ 2) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (cappedIncrementSq_nonneg M g K i ω)]
  exact cappedIncrementSq_le_bound hK M g i ω

theorem integrable_cappedIncrementSq_mul [IsFiniteMeasure P] (hM : Martingale M 𝔽 P)
    {g : ℕ → ℝ≥0} (hg : Monotone g) {K : ℝ} (hK : 0 ≤ K) (i j : ℕ) :
    Integrable (fun ω => cappedIncrementSq M g K i ω * cappedIncrementSq M g K j ω) P := by
  refine Integrable.of_bound
    (((((stronglyMeasurable_cappedIncrementSq hM hg K i).mono (𝔽.le (g (i + 1)))).mul
      ((stronglyMeasurable_cappedIncrementSq hM hg K j).mono
        (𝔽.le (g (j + 1))))).aestronglyMeasurable)) (4 * K ^ 2 * (4 * K ^ 2)) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cappedIncrementSq_nonneg M g K i ω)
    (cappedIncrementSq_nonneg M g K j ω))]
  exact mul_le_mul (cappedIncrementSq_le_bound hK M g i ω)
    (cappedIncrementSq_le_bound hK M g j ω) (cappedIncrementSq_nonneg M g K j ω)
    (by positivity)

/-! ### The one-partition Lindeberg estimate -/

/-! ### The Lindeberg condition for the unstopped process -/

/-- Choice of a cap level making a fixed nonnegative budget small. -/
theorem exists_cap_level {V η : ℝ} (hV : 0 ≤ V) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ 0 < K ^ 2 ∧ V / K ^ 2 ≤ η / 4 := by
  have hdiv : (0 : ℝ) ≤ 4 * V / η := div_nonneg (by linarith) hη.le
  have harg : (0 : ℝ) ≤ 4 * V / η + 1 := by linarith
  refine ⟨Real.sqrt (4 * V / η + 1), Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Real.sq_sqrt harg]; linarith
  · have hpos : (0 : ℝ) < Real.sqrt (4 * V / η + 1) ^ 2 := by
      rw [Real.sq_sqrt harg]; linarith
    rw [div_le_iff₀ hpos, Real.sq_sqrt harg]
    have hid : η / 4 * (4 * V / η + 1) = V + η / 4 := by
      field_simp
      try ring
    rw [hid]
    linarith

/-- Choice of a truncation parameter making a fixed nonnegative budget small. -/
theorem exists_truncation_level {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ lam : ℝ, 0 < lam ∧ B / lam ≤ η / 4 := by
  have hdiv : (0 : ℝ) ≤ 4 * B / η := div_nonneg (by linarith) hη.le
  refine ⟨4 * B / η + 1, by linarith, ?_⟩
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * B / η + 1)]
  have hid : η / 4 * (4 * B / η + 1) = B + η / 4 := by
    field_simp
    try ring
  rw [hid]
  linarith

/-! ### The unconditional Gaussian identification -/

end ReflectedGMS.MartingaleLimit
