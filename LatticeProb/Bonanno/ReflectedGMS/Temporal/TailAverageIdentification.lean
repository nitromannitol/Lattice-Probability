/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TailAverageIdentification at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Identifying the tail conditional expectation of `p:lem:timeconverge` with `𝔼[F]`

`ReflectedGMS/Temporal/ConditionalTemporalAveraging.lean` proves
`tendsto_setAverageReal_chain_ae`: along the root dyadic ancestor chain the block averages
converge almost surely to

```
L = P[F | ⨅ r : ℚ, reRootSigma θ (blkFam r)],
```

the conditional expectation given the tail of the decreasing re-rooting σ-fields.  The
`chain` field of `ReflectedGMS.GridBlockTransfer.GridChainData` needs that limit to be the
**constant** `𝔼[F]` (in the application `𝔼[Γ]`).  The manuscript closes that gap in the
proof of `p:prop:timeergodic` (tex:1519-1534) in four steps:

1. average the auxiliary time grid out of a bounded test of the limit,
   `B(Ω) = 𝔼_{𝒟}[ψ(L(Ω,𝒟))]`;
2. `p:lem:regeninvariant` plus environment ergodicity make `B` a deterministic constant;
3. because `F` is **unmarked** — a function of the trajectory alone — step 2 turns into the
   product rule `𝔼[F ψ(L)] = 𝔼[F] 𝔼[ψ(L)]`;
4. because `L` is a conditional expectation of `F`, `𝔼[F ψ(L)] = 𝔼[L ψ(L)]`; hence
   `𝔼[(L - 𝔼[F]) ψ(L)] = 0` for every bounded `ψ`, and a sign test gives `L = 𝔼[F]` a.s.

**This module proves steps 1, 3 and 4 outright and isolates step 2 as the single named
input `GridAveragedConstant`.**  Nothing here proves `p:lem:regeninvariant`, environment
ergodicity, `p:prop:timeergodic`, `p:thm:areaclt` or either main theorem.

## What is proved

* `integral_mul_comp_condExp` — step 4's pull-out: for bounded measurable `ψ`,
  `∫ F · ψ(P[F|𝒢]) = ∫ P[F|𝒢] · ψ(P[F|𝒢])`.  This is the only place the conditional
  expectation is used, and it needs no property of `𝒢` beyond `𝒢 ≤ m0`.
* `ae_eq_const_of_condExp_uncorrelated` — steps 3+4: a version `L` of `P[F|𝒢]` that is
  uncorrelated with every bounded measurable test of itself equals the constant `𝔼[F]`.
  The test used is `signTest`, so the hypothesis is consumed for **one** explicit `ψ`.
* `GridAveragedConstant` — step 2 as data, on a product space `Ω × D` of trajectories and
  grids.  It says: for every bounded measurable `ψ` the grid average
  `ω ↦ ∫ ψ(L(ω,d)) dν(d)` is `P`-a.e. equal to a constant.  Equivalently, the conditional
  law of `L` given the trajectory does not depend on the trajectory.  This is **strictly
  weaker** than the conclusion: `gridAveragedConstant_of_grid` exhibits non-constant `L`
  satisfying it (any `L` measurable for the grid alone).
* `uncorrelated_of_gridAveragedConstant` — step 1, the Fubini step, and
  `ae_eq_const_of_gridAveragedConstant` — the packaged conclusion
  `L =ᵐ[P ⊗ ν] 𝔼_P[F]`.
* `exists_threshold_of_tendsto` — the length-indexed re-reading of a sequential limit that
  the `chain` field is stated in: a convergent sequence indexed by a monotone family of
  finite block lengths is uniformly close to its limit for all blocks longer than some
  threshold.

## What is *not* proved

`GridAveragedConstant` itself.  In the manuscript it is the conjunction of
`p:lem:regeninvariant` (whose own open inputs are reversal invariance of the complete
stopped return-cycle law, the size-biased entrance/age decomposition, and `v`-independence)
and the environment-ergodicity hypothesis.  None of that is touched here.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace ReflectedGMS.TailAverageIdentification

/-! ### The bounded sign test of the manuscript's last step -/

/-- The bounded Borel test `ψ(x) = sign (x - c)` used to convert
`𝔼[(L - c) ψ(L)] = 0` into `𝔼|L - c| = 0`. -/
noncomputable def signTest (c x : ℝ) : ℝ :=
  if c < x then 1 else if x < c then -1 else 0

theorem measurable_signTest (c : ℝ) : Measurable (signTest c) := by
  unfold signTest
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    measurable_const

theorem abs_signTest_le_one (c x : ℝ) : |signTest c x| ≤ 1 := by
  unfold signTest
  split_ifs <;> norm_num

/-- `(x - c) · sign (x - c) = |x - c|`: the identity that turns the vanishing of the
correlations into the vanishing of an `L¹` norm. -/
theorem sub_mul_signTest (c x : ℝ) : (x - c) * signTest c x = |x - c| := by
  unfold signTest
  split_ifs with h1 h2
  · rw [mul_one, abs_of_pos (sub_pos.2 h1)]
  · rw [mul_neg_one, abs_of_neg (sub_lt_zero.2 h2)]
  · have hx : x = c := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    rw [hx, sub_self, mul_zero, abs_zero]

/-! ### Step 4: the conditional-expectation pull-out -/

/-- **`𝔼[F ψ(L)] = 𝔼[L ψ(L)]` for `L = 𝔼[F|𝒢]`** (the manuscript's "`L` is the reverse
conditional expectation limit", tex:1529).

Only `𝒢 ≤ m0` is used: no ergodicity, no triviality of `𝒢`, and no property of the block
system. -/
theorem integral_mul_comp_condExp {Ω : Type*} {𝒢 m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (h𝒢 : 𝒢 ≤ m0) {F : Ω → ℝ}
    (hF : Integrable F P) {ψ : ℝ → ℝ} (hψm : Measurable ψ) {C : ℝ}
    (hψb : ∀ x : ℝ, |ψ x| ≤ C) :
    ∫ ω, F ω * ψ ((P[F|𝒢]) ω) ∂P = ∫ ω, (P[F|𝒢]) ω * ψ ((P[F|𝒢]) ω) ∂P := by
  have : IsFiniteMeasure (P.trim h𝒢) := by
    refine ⟨?_⟩
    rw [trim_measurableSet_eq h𝒢 (@MeasurableSet.univ Ω 𝒢)]
    exact measure_lt_top P Set.univ
  have hcm : Measurable[𝒢] (P[F|𝒢]) := stronglyMeasurable_condExp.measurable
  have hum : Measurable[𝒢] fun ω => ψ ((P[F|𝒢]) ω) := hψm.comp hcm
  have husm : StronglyMeasurable[𝒢] fun ω => ψ ((P[F|𝒢]) ω) := hum.stronglyMeasurable
  have hum0 : Measurable fun ω => ψ ((P[F|𝒢]) ω) := hum.mono h𝒢 le_rfl
  have hbound : ∀ ω : Ω, ‖ψ ((P[F|𝒢]) ω)‖ ≤ C := by
    intro ω
    rw [Real.norm_eq_abs]
    exact hψb _
  have hUF : Integrable ((fun ω => ψ ((P[F|𝒢]) ω)) * F) P := by
    refine (hF.bdd_mul hum0.aestronglyMeasurable (Eventually.of_forall hbound)).congr ?_
    exact Eventually.of_forall fun ω => rfl
  have hpull : P[(fun ω => ψ ((P[F|𝒢]) ω)) * F|𝒢]
      =ᵐ[P] (fun ω => ψ ((P[F|𝒢]) ω)) * P[F|𝒢] :=
    condExp_mul_of_stronglyMeasurable_left husm hUF hF
  have e1 : ∫ ω, F ω * ψ ((P[F|𝒢]) ω) ∂P
      = ∫ ω, ((fun ω => ψ ((P[F|𝒢]) ω)) * F) ω ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show F ω * ψ ((P[F|𝒢]) ω) = ψ ((P[F|𝒢]) ω) * F ω
    exact mul_comm _ _
  have e2 : ∫ ω, ((fun ω => ψ ((P[F|𝒢]) ω)) * F) ω ∂P
      = ∫ ω, (P[(fun ω => ψ ((P[F|𝒢]) ω)) * F|𝒢]) ω ∂P :=
    (integral_condExp (f := (fun ω => ψ ((P[F|𝒢]) ω)) * F) h𝒢).symm
  have e3 : ∫ ω, (P[(fun ω => ψ ((P[F|𝒢]) ω)) * F|𝒢]) ω ∂P
      = ∫ ω, ((fun ω => ψ ((P[F|𝒢]) ω)) * P[F|𝒢]) ω ∂P := integral_congr_ae hpull
  have e4 : ∫ ω, ((fun ω => ψ ((P[F|𝒢]) ω)) * P[F|𝒢]) ω ∂P
      = ∫ ω, (P[F|𝒢]) ω * ψ ((P[F|𝒢]) ω) ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show ψ ((P[F|𝒢]) ω) * (P[F|𝒢]) ω = (P[F|𝒢]) ω * ψ ((P[F|𝒢]) ω)
    exact mul_comm _ _
  rw [e1, e2, e3, e4]

/-! ### The sign test -/

/-- If the correlation of `g - c` with the sign test at `c` vanishes, then `g` is a.e. `c`. -/
theorem ae_eq_const_of_integral_sub_mul_signTest_eq_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {g : Ω → ℝ} {c : ℝ} (hgi : Integrable g P)
    (h : ∫ ω, (g ω - c) * signTest c (g ω) ∂P = 0) :
    g =ᵐ[P] fun _ => c := by
  have hcongr : ∫ ω, (g ω - c) * signTest c (g ω) ∂P = ∫ ω, |g ω - c| ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => sub_mul_signTest c (g ω))
  have habs : ∫ ω, |g ω - c| ∂P = 0 := hcongr.symm.trans h
  have hint : Integrable (fun ω => |g ω - c|) P := (hgi.sub (integrable_const c)).abs
  have hzero : (fun ω => |g ω - c|) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun ω => abs_nonneg (g ω - c)) hint).1 habs
  filter_upwards [hzero] with ω hω
  have h1 : |g ω - c| = 0 := hω
  have h2 : g ω - c = 0 := abs_eq_zero.1 h1
  linarith

/-! ### Steps 3 and 4 combined: the limit is the mean -/

/-- **The manuscript's deterministic-limit step** (tex:1526-1534).

If `L` is a version of `P[F|𝒢]` and `F` is uncorrelated with every bounded measurable test
of `L`, then `L` is almost surely the constant `𝔼[F]`.

The hypothesis is consumed for the single explicit test `signTest (∫ F)`, so any producer
that supplies it for that one function suffices.

CONDITIONAL on `huncorr`; nothing here certifies `p:lem:regeninvariant`, environment
ergodicity or `p:prop:timeergodic`. -/
theorem ae_eq_const_of_condExp_uncorrelated {Ω : Type*} {𝒢 m0 : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ m0)
    {F L : Ω → ℝ} (hF : Integrable F P) (hL : L =ᵐ[P] P[F|𝒢])
    (huncorr : ∀ ψ : ℝ → ℝ, Measurable ψ → (∀ x : ℝ, |ψ x| ≤ 1) →
      ∫ ω, F ω * ψ (L ω) ∂P = (∫ ω, F ω ∂P) * ∫ ω, ψ (L ω) ∂P) :
    L =ᵐ[P] fun _ => ∫ ω, F ω ∂P := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∫ ω, F ω ∂P = c := ⟨_, rfl⟩
  rw [hc] at huncorr ⊢
  have hgm : Measurable (P[F|𝒢]) := (stronglyMeasurable_condExp.mono h𝒢).measurable
  have hgi : Integrable (P[F|𝒢]) P := integrable_condExp
  have hψm : Measurable (signTest c) := measurable_signTest c
  have hψb : ∀ x : ℝ, |signTest c x| ≤ 1 := abs_signTest_le_one c
  have hnorm : ∀ ω : Ω, ‖signTest c ((P[F|𝒢]) ω)‖ ≤ 1 := by
    intro ω
    rw [Real.norm_eq_abs]
    exact hψb _
  have e1 : ∫ ω, F ω * signTest c (L ω) ∂P
      = ∫ ω, F ω * signTest c ((P[F|𝒢]) ω) ∂P := by
    refine integral_congr_ae (hL.mono fun ω hω => ?_)
    show F ω * signTest c (L ω) = F ω * signTest c ((P[F|𝒢]) ω)
    rw [hω]
  have e2 : ∫ ω, signTest c (L ω) ∂P = ∫ ω, signTest c ((P[F|𝒢]) ω) ∂P := by
    refine integral_congr_ae (hL.mono fun ω hω => ?_)
    show signTest c (L ω) = signTest c ((P[F|𝒢]) ω)
    rw [hω]
  have e3 : ∫ ω, F ω * signTest c ((P[F|𝒢]) ω) ∂P
      = ∫ ω, (P[F|𝒢]) ω * signTest c ((P[F|𝒢]) ω) ∂P :=
    integral_mul_comp_condExp h𝒢 hF hψm hψb
  have e4 := huncorr (signTest c) hψm hψb
  have hψint : Integrable (fun ω => signTest c ((P[F|𝒢]) ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hψm.comp hgm).aestronglyMeasurable
      (Eventually.of_forall hnorm)
  have hgψint : Integrable (fun ω => (P[F|𝒢]) ω * signTest c ((P[F|𝒢]) ω)) P :=
    hgi.mul_bdd (hψm.comp hgm).aestronglyMeasurable (Eventually.of_forall hnorm)
  have hsplit : ∫ ω, ((P[F|𝒢]) ω - c) * signTest c ((P[F|𝒢]) ω) ∂P
      = (∫ ω, (P[F|𝒢]) ω * signTest c ((P[F|𝒢]) ω) ∂P)
        - c * ∫ ω, signTest c ((P[F|𝒢]) ω) ∂P := by
    rw [← integral_const_mul c fun ω => signTest c ((P[F|𝒢]) ω),
      ← integral_sub hgψint (hψint.const_mul c)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    ring
  have hzero : ∫ ω, ((P[F|𝒢]) ω - c) * signTest c ((P[F|𝒢]) ω) ∂P = 0 := by
    rw [hsplit, ← e3, ← e1, e4, e2]
    ring
  exact hL.trans (ae_eq_const_of_integral_sub_mul_signTest_eq_zero hgi hzero)

/-! ### Step 1 and step 2: averaging out the independent time grid -/

/-- **The output of `p:lem:regeninvariant` together with environment ergodicity**, in the
exact form the manuscript's final step consumes (tex:1526-1528).

The sample space is a product: `Ω` carries the trajectory and the environment, `D` carries
the independent time grid, and `L` is the tail limit of `p:lem:timeconverge`, which depends
on both.  The field `const` says that for every bounded Borel `ψ` the **grid average**
`B_ψ(ω) = ∫ ψ(L(ω,d)) dν(d)` is `P`-almost surely a constant — the manuscript's

> `B(Ω) = 𝔼_{𝒟}[ψ(L(Ω,𝒟))]` … Lemma `p:lem:regeninvariant` makes it a similarity-invariant
> function of `H`.  Environment ergodicity makes it the constant `𝔼[ψ(L)]`.

Equivalently: the conditional law of `L` given the trajectory does not depend on the
trajectory.  This is genuinely weaker than the conclusion `L` is constant —
`gridAveragedConstant_of_grid` satisfies it with an arbitrary non-constant `L` that happens
to be a function of the grid alone.

Nothing in this structure asserts it. -/
structure GridAveragedConstant {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    (P : Measure Ω) (ν : Measure D) (L : Ω × D → ℝ) : Prop where
  /-- The limit is jointly measurable in the trajectory and the grid. -/
  measurable : Measurable L
  /-- Every bounded Borel test of the limit has an almost surely constant grid average. -/
  const : ∀ ψ : ℝ → ℝ, Measurable ψ → (∀ x : ℝ, |ψ x| ≤ 1) →
    ∃ c : ℝ, ∀ᵐ ω ∂P, ∫ d, ψ (L (ω, d)) ∂ν = c

/-- The expectation of an unmarked functional is the same on the trajectory space and on
the product with the grid space. -/
theorem integral_comp_fst {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure D} [IsProbabilityMeasure ν]
    {F₀ : Ω → ℝ} (hF₀ : Integrable F₀ P) :
    ∫ p : Ω × D, F₀ p.1 ∂(P.prod ν) = ∫ ω, F₀ ω ∂P := by
  have hFp : Integrable (fun p : Ω × D => F₀ p.1) (P.prod ν) :=
    (MeasureTheory.measurePreserving_fst (μ := P) (ν := ν)).integrable_comp_of_integrable hF₀
  have hstep : ∫ p : Ω × D, F₀ p.1 ∂(P.prod ν) = ∫ ω, (∫ _d : D, F₀ ω ∂ν) ∂P :=
    integral_prod _ hFp
  rw [hstep]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show ∫ _d : D, F₀ ω ∂ν = F₀ ω
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- **Step 1 of the manuscript's argument, the Fubini step**: because `F` is unmarked, the
almost sure constancy of the grid averages is exactly the product rule
`𝔼[F ψ(L)] = 𝔼[F] 𝔼[ψ(L)]` on the product space.

CONDITIONAL on `GridAveragedConstant`. -/
theorem uncorrelated_of_gridAveragedConstant {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure D}
    [IsProbabilityMeasure ν] {F₀ : Ω → ℝ} (hF₀ : Integrable F₀ P) {L : Ω × D → ℝ}
    (hgrid : GridAveragedConstant P ν L) (ψ : ℝ → ℝ) (hψm : Measurable ψ)
    (hψb : ∀ x : ℝ, |ψ x| ≤ 1) :
    ∫ p : Ω × D, F₀ p.1 * ψ (L p) ∂(P.prod ν)
      = (∫ p : Ω × D, F₀ p.1 ∂(P.prod ν)) * ∫ p : Ω × D, ψ (L p) ∂(P.prod ν) := by
  obtain ⟨c, hc⟩ := hgrid.const ψ hψm hψb
  have hLm : Measurable L := hgrid.measurable
  have hbound : ∀ p : Ω × D, ‖ψ (L p)‖ ≤ 1 := by
    intro p
    rw [Real.norm_eq_abs]
    exact hψb _
  have hFp : Integrable (fun p : Ω × D => F₀ p.1) (P.prod ν) :=
    (MeasureTheory.measurePreserving_fst (μ := P) (ν := ν)).integrable_comp_of_integrable hF₀
  have hψp : Integrable (fun p : Ω × D => ψ (L p)) (P.prod ν) :=
    (integrable_const (1 : ℝ)).mono' (hψm.comp hLm).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hmixp : Integrable (fun p : Ω × D => F₀ p.1 * ψ (L p)) (P.prod ν) :=
    hFp.mul_bdd (hψm.comp hLm).aestronglyMeasurable (Eventually.of_forall hbound)
  have hmix : ∫ p : Ω × D, F₀ p.1 * ψ (L p) ∂(P.prod ν) = (∫ ω, F₀ ω ∂P) * c := by
    have hstep : ∫ p : Ω × D, F₀ p.1 * ψ (L p) ∂(P.prod ν)
        = ∫ ω, (∫ d, F₀ ω * ψ (L (ω, d)) ∂ν) ∂P := integral_prod _ hmixp
    have hinner : ∀ᵐ ω ∂P, (∫ d, F₀ ω * ψ (L (ω, d)) ∂ν) = F₀ ω * c := by
      filter_upwards [hc] with ω hω
      rw [integral_const_mul, hω]
    rw [hstep, integral_congr_ae hinner, integral_mul_const]
  have hψi : ∫ p : Ω × D, ψ (L p) ∂(P.prod ν) = c := by
    have hstep : ∫ p : Ω × D, ψ (L p) ∂(P.prod ν) = ∫ ω, (∫ d, ψ (L (ω, d)) ∂ν) ∂P :=
      integral_prod _ hψp
    rw [hstep, integral_congr_ae hc, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul]
  rw [hmix, hψi, integral_comp_fst hF₀]

/-- **The tail conditional expectation of `p:lem:timeconverge` is the constant `𝔼[F]`**,
from the single named input `GridAveragedConstant`.

This is the whole of the manuscript's "why the unmarked limit is deterministic"
(`p:sec:regeneration`) apart from `p:lem:regeninvariant` and environment ergodicity, which
enter only through `hgrid`.

CONDITIONAL on `hgrid`.  Nothing here certifies `p:lem:regeninvariant`, environment
ergodicity, `p:prop:timeergodic`, `p:thm:areaclt` or either main theorem. -/
theorem ae_eq_const_of_gridAveragedConstant {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure D}
    [IsProbabilityMeasure ν] {𝒢 : MeasurableSpace (Ω × D)}
    (h𝒢 : 𝒢 ≤ Prod.instMeasurableSpace) {F₀ : Ω → ℝ}
    (hF₀ : Integrable F₀ P) {L : Ω × D → ℝ}
    (hL : L =ᵐ[P.prod ν] (P.prod ν)[fun p : Ω × D => F₀ p.1|𝒢])
    (hgrid : GridAveragedConstant P ν L) :
    L =ᵐ[P.prod ν] fun _ => ∫ ω, F₀ ω ∂P := by
  have hFp : Integrable (fun p : Ω × D => F₀ p.1) (P.prod ν) :=
    (MeasureTheory.measurePreserving_fst (μ := P) (ν := ν)).integrable_comp_of_integrable hF₀
  have hmain := ae_eq_const_of_condExp_uncorrelated h𝒢 hFp hL
    fun ψ hψm hψb => uncorrelated_of_gridAveragedConstant hF₀ hgrid ψ hψm hψb
  rw [integral_comp_fst hF₀] at hmain
  exact hmain

/-! ### The length-indexed re-reading of a sequential limit -/

/-- **From a sequential limit along the ancestor chain to "all sufficiently long blocks".**

If the lengths `v n` are monotone and finite and the averages `a n` converge to `μ`, then
for every tolerance there is a length threshold beyond which *every* member of the chain is
within the tolerance.  This is the shape the `chain` field of
`ReflectedGMS.GridBlockTransfer.GridChainData` is stated in. -/
theorem exists_threshold_of_tendsto {v : ℕ → ℝ≥0∞} (hmono : Monotone v)
    (hfin : ∀ n : ℕ, v n ≠ ⊤) {a : ℕ → ℝ} {μ : ℝ}
    (hconv : Tendsto a atTop (𝓝 μ)) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ n : ℕ, ENNReal.ofReal R ≤ v n → |a n - μ| ≤ η := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hconv η hη
  refine ⟨(v N).toReal + 1, fun n hn => ?_⟩
  rcases le_or_gt N n with hnN | hnN
  · have hd := hN n hnN
    rw [Real.dist_eq] at hd
    exact hd.le
  · exfalso
    have h1 : v n ≤ v N := hmono hnN.le
    have h2 : ENNReal.ofReal ((v N).toReal + 1) ≤ v N := le_trans hn h1
    rw [ENNReal.ofReal_le_iff_le_toReal (hfin N)] at h2
    linarith

end ReflectedGMS.TailAverageIdentification
