/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TrajectoryCoding at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRight
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The measurable trajectory coding of `p:sec:temporalmtp`

The manuscript builds the temporal mass-transport identity `p:lem:timeMTP` on a
*coding* of the two-sided area-clock trajectory:

> A common measurable trajectory coding is obtained by labeling cells by positive
> integers and using the one-point compactification `ℕ ∪ {∞}`, with all nonvertex
> states collapsed to `∞`.  The fixed-finite-vertex-set continuity properties in
> Gwynne--Sung Lemmas 3.11--3.13 and Proposition 5.3 make this collapsed path
> càdlàg; homeomorphic time change preserves this fact.  **Its rational-time
> values determine it**, its holding intervals, and its end labels.  **Reindexing
> the cells and scaling time are measurable operations on this coding.**

This file constructs exactly that coding and proves exactly those sentences.

## Why the raw product space does not work, and what this file supplies

The handoff `outputs/opus-annealed-temporal-transport-handoff.md` records the
precise obstacle that stopped the instantiation of
`ReflectedGMS.AnnealedTemporalTransport.ConditionalPathIntegral`:

> on the full product path space `ℝ → Option CompactCell` neither `(ω,t) ↦ ω t`
> nor `ω ↦ ∫⁻ t, 1_{ω t = L} V ω 0 t dt` is measurable, and an individual `ω`
> need not be Borel, so `lintegral_map` and the change of variables have no
> hypotheses to run on.

On the raw product σ-algebra of `ℝ → S` the evaluation map *is* measurable in
`ω` for each fixed `t`, but the joint map `(ω, t) ↦ ω t` is not: a set in the
product σ-algebra is determined by countably many coordinates, while the diagonal
`{(ω,t) | ω t ∈ A}` is not.  Restricting to **càdlàg** paths and generating the
σ-algebra by the **rational** times repairs this, because a càdlàg path is the
pointwise limit of its own dyadic right-approximations, each of which is jointly
measurable for a trivial reason (it factors through `ℤ`, a countable space).

`CadlagPath S` is that space.  The results below are, in the manuscript's order:

* `CadlagPath.measurable_eval_uncurry` — `(ω, t) ↦ X_t(ω)` is **jointly**
  measurable.  This is the statement whose absence blocked the previous packet.
* `CadlagPath.eq_of_ratEval_eq` — "its rational-time values determine it",
  and its measure-theoretic form `CadlagPath.eq_of_map_ratEval_eq`: a law on the
  coding is determined by its rational-time finite-dimensional distributions.
* `CadlagPath.timeShift` and `CadlagPath.parabolicDilate` (the latter also
  reindexes the cells by a continuous `φ`) — "reindexing the cells and scaling
  time are measurable operations on this coding", with the flow laws
  `timeShift_zero` / `timeShift_add` and joint measurability
  `measurable_uncurry_timeShift` of the flow.
* `CadlagPath.measurePreserving_timeShift_of_ratEval_law` — the criterion that
  reduces real time-shift invariance of a law to its finite-dimensional
  distributions.  This is the shape the `p:eq:sigmapath` step needs; it does
  **not** assert that any law satisfies it.
* `pathNumerator_parabolicDilate` — the manuscript's scaling bookkeeping
  `dt` gains `C²` and `V` gains `C^{-2}`, carried out as one honest change of
  variables `t = C² r`, and giving the **similarity invariance of the conditional
  path integral** pathwise.
* `lintegral_pathNumerator_parabolicDilate` — the same statement after taking
  `E_H^v`, i.e. the field `scaleInvariant` of `ConditionalPathIntegral`, from the
  law-level dilation covariance `(P_H^v).map S_C = P_{CH}^{Cv}` alone.

## Scope, and what is *not* claimed

Nothing here is probabilistic apart from the last two results, whose measure
hypotheses are stated explicitly.  In particular this file does **not** construct
the fixed-environment laws `P_H^v`, does not assume any time-shift invariance of
any law, and proves nothing about the annealed rooted probability law.  Its only
role is to remove the measurability obstruction above.

## Reuse

Right-continuity and the càdlàg property are mathlib's `IsRightContinuous` and
`IsCadlag` (`Mathlib/Topology/Order/Cadlag.lean`); they are not redefined.  The
limit argument is mathlib's `measurable_of_tendsto_metrizable`, the countable
factorisation is `measurable_from_prod_countable_left`, and the change of
variables is `Real.smul_map_volume_mul_left` together with
`MeasureTheory.lintegral_map_equiv` for `MeasurableEquiv.mulLeft₀`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ReflectedGMS.TrajectoryCoding

/-! ## The coding space -/

/-- **The manuscript's trajectory coding.**  A two-sided càdlàg path with values
in the coded state space `S` (for the manuscript, `S = ℕ ∪ {∞}` with every
nonvertex state collapsed to `∞`). -/
structure CadlagPath (S : Type*) [TopologicalSpace S] where
  /-- The underlying trajectory `t ↦ X_t`. -/
  toFun : ℝ → S
  /-- Right-continuity with left limits, as supplied by Gwynne--Sung. -/
  isCadlag' : IsCadlag toFun

namespace CadlagPath

variable {S : Type*} [TopologicalSpace S]

theorem ext' {ω ω' : CadlagPath S} (h : ω.toFun = ω'.toFun) : ω = ω' := by
  obtain ⟨f, hf⟩ := ω
  obtain ⟨g, hg⟩ := ω'
  change f = g at h
  subst h
  rfl

/-- Right-continuity of a coded trajectory, in the `Ici` form. -/
theorem continuousWithinAt_Ici (ω : CadlagPath S) (t : ℝ) :
    ContinuousWithinAt ω.toFun (Set.Ici t) t :=
  continuousWithinAt_Ioi_iff_Ici.mp (ω.isCadlag'.isRightContinuous t)

/-- **Right-continuity, sequential form.**  Any approach to `t` from the right
(weakly, so the approximating times may equal `t`) transports to the values. -/
theorem tendsto_eval_of_tendsto_ge (ω : CadlagPath S) {ι : Type*} {l : Filter ι} {u : ι → ℝ}
    {t : ℝ} (hu : Tendsto u l (𝓝 t)) (hge : ∀ i, t ≤ u i) :
    Tendsto (fun i => ω.toFun (u i)) l (𝓝 (ω.toFun t)) :=
  (ω.continuousWithinAt_Ici t).tendsto.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu (Eventually.of_forall hge))

/-! ## The σ-algebra generated by the rational times -/

variable [MeasurableSpace S]

/-- The rational-time coordinates of a coded trajectory. -/
def ratEval (ω : CadlagPath S) : ℚ → S := fun q => ω.toFun (q : ℝ)

/-- **The coding σ-algebra**: generated by the rational-time values, exactly the
manuscript's "its rational-time values determine it". -/
instance instMeasurableSpace : MeasurableSpace (CadlagPath S) :=
  MeasurableSpace.comap ratEval inferInstance

theorem measurable_ratEval : Measurable (ratEval : CadlagPath S → ℚ → S) :=
  fun _u hu => ⟨_, hu, rfl⟩

theorem measurable_eval_rat (q : ℚ) :
    Measurable fun ω : CadlagPath S => ω.toFun (q : ℝ) :=
  (measurable_pi_apply q).comp measurable_ratEval

/-- A map into the coding space is measurable as soon as all its rational-time
values are. -/
theorem measurable_of_ratEval {α : Type*} [MeasurableSpace α] {f : α → CadlagPath S}
    (h : ∀ q : ℚ, Measurable fun a => (f a).toFun (q : ℝ)) : Measurable f := by
  have hm : Measurable fun a => ratEval (f a) := Measurable.of_eval h
  intro s hs
  obtain ⟨u, hu, rfl⟩ := hs
  exact hm hu

/-- **A law on the coding is determined by its rational-time finite-dimensional
distributions.**  Every measurable set of the coding is by construction the
pullback of a measurable set of `ℚ → S`, so no π-system or Polish-space argument
is needed: equality of the pushforwards under `ratEval` *is* equality of the
laws.  This is the measure-theoretic form of the manuscript's "its rational-time
values determine it". -/
theorem eq_of_map_ratEval_eq {μ ν : Measure (CadlagPath S)}
    (h : μ.map ratEval = ν.map ratEval) : μ = ν := by
  ext s hs
  obtain ⟨u, hu, rfl⟩ := hs
  rw [← Measure.map_apply measurable_ratEval hu, ← Measure.map_apply measurable_ratEval hu, h]

end CadlagPath

/-! ## Dyadic right-approximation of a real time

These are the level-`n` dyadic rationals `⌈t·2ⁿ⌉/2ⁿ ≥ t`.  They are rational
(so the coding σ-algebra sees them), they decrease to `t` from the right (so
right-continuity applies), and for fixed `n` they take countably many values in a
measurable way (so the approximants are *jointly* measurable). -/

/-- The smallest level-`n` dyadic rational `≥ t`. -/
noncomputable def dyadicCeilRat (n : ℕ) (t : ℝ) : ℚ := ((⌈t * 2 ^ n⌉ : ℤ) : ℚ) / 2 ^ n

theorem dyadicCeilRat_cast (n : ℕ) (t : ℝ) :
    ((dyadicCeilRat n t : ℚ) : ℝ) = ((⌈t * 2 ^ n⌉ : ℤ) : ℝ) / 2 ^ n := by
  unfold dyadicCeilRat
  push_cast
  ring

theorem self_le_dyadicCeilRat (n : ℕ) (t : ℝ) : t ≤ ((dyadicCeilRat n t : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicCeilRat_cast, le_div_iff₀ hpos]
  exact Int.le_ceil _

theorem dyadicCeilRat_lt (n : ℕ) (t : ℝ) :
    ((dyadicCeilRat n t : ℚ) : ℝ) < t + ((2 : ℝ) ^ n)⁻¹ := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicCeilRat_cast, div_lt_iff₀ hpos]
  have hceil : ((⌈t * 2 ^ n⌉ : ℤ) : ℝ) < t * 2 ^ n + 1 := Int.ceil_lt_add_one _
  have hrw : (t + ((2 : ℝ) ^ n)⁻¹) * 2 ^ n = t * 2 ^ n + 1 := by
    field_simp
  rw [hrw]
  exact hceil

theorem tendsto_dyadicCeilRat (t : ℝ) :
    Tendsto (fun n : ℕ => ((dyadicCeilRat n t : ℚ) : ℝ)) atTop (𝓝 t) := by
  have h0 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
    simpa [inv_pow] using this
  have hupper : Tendsto (fun n : ℕ => t + ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t) (f := atTop (α := ℕ))).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => self_le_dyadicCeilRat n t) (fun n => (dyadicCeilRat_lt n t).le)

namespace CadlagPath

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]

/-- Evaluation at a fixed level-`n` dyadic point is measurable, because that
point is rational. -/
theorem measurable_eval_dyadicPoint (n : ℕ) (k : ℤ) :
    Measurable fun ω : CadlagPath S => ω.toFun ((k : ℝ) / 2 ^ n) := by
  have hq : (((k : ℚ) / 2 ^ n : ℚ) : ℝ) = (k : ℝ) / 2 ^ n := by push_cast; ring
  simpa only [hq] using measurable_eval_rat (S := S) ((k : ℚ) / 2 ^ n)

/-- **The dyadic approximants are jointly measurable.**  For fixed `n` the
approximation factors through the countable space `ℤ`. -/
theorem measurable_evalDyadic (n : ℕ) :
    Measurable fun p : CadlagPath S × ℝ => p.1.toFun ((dyadicCeilRat n p.2 : ℚ) : ℝ) := by
  have hF : Measurable fun q : CadlagPath S × ℤ => q.1.toFun ((q.2 : ℝ) / 2 ^ n) :=
    measurable_from_prod_countable_left fun k => measurable_eval_dyadicPoint n k
  have hmap : Measurable fun p : CadlagPath S × ℝ =>
      ((p.1, ⌈p.2 * 2 ^ n⌉) : CadlagPath S × ℤ) :=
    measurable_fst.prodMk (Int.measurable_ceil.comp (measurable_snd.mul measurable_const))
  simpa only [Function.comp_def, dyadicCeilRat_cast] using hF.comp hmap

/-- **Joint measurability of the trajectory coding.**

`(ω, t) ↦ X_t(ω)` is measurable for the rational-time σ-algebra on càdlàg paths.
This is the statement that fails on the raw product space `ℝ → S`, and it is the
exact hypothesis that the conditional path integral of `p:sec:temporalmtp`
needs. -/
theorem measurable_eval_uncurry [TopologicalSpace.PseudoMetrizableSpace S] [BorelSpace S] :
    Measurable fun p : CadlagPath S × ℝ => p.1.toFun p.2 := by
  refine measurable_of_tendsto_metrizable (f := fun n p => p.1.toFun ((dyadicCeilRat n p.2 : ℚ) : ℝ))
    (fun n => measurable_evalDyadic n) ?_
  rw [tendsto_pi_nhds]
  rintro ⟨ω, t⟩
  exact ω.tendsto_eval_of_tendsto_ge (tendsto_dyadicCeilRat t) fun n => self_le_dyadicCeilRat n t

/-- Evaluation at a fixed real time is measurable. -/
theorem measurable_eval [TopologicalSpace.PseudoMetrizableSpace S] [BorelSpace S] (t : ℝ) :
    Measurable fun ω : CadlagPath S => ω.toFun t :=
  measurable_eval_uncurry.comp (measurable_id.prodMk measurable_const)

end CadlagPath

namespace CadlagPath

variable {S : Type*} [TopologicalSpace S]

end CadlagPath

/-! ## Time change and cell reindexing are measurable operations -/

/-- Pre-composition with an increasing affine time change preserves the càdlàg
property.  This is the manuscript's "homeomorphic time change preserves this
fact" for the two changes actually used: the time shift `t ↦ t + r` and the
parabolic time scaling `t ↦ C⁻²t`. -/
theorem isCadlag_comp_affine {S : Type*} [TopologicalSpace S] {f : ℝ → S} (hf : IsCadlag f)
    {a b : ℝ} (ha : 0 < a) : IsCadlag fun t : ℝ => f (a * t + b) := by
  have hcont : Continuous fun t : ℝ => a * t + b := by fun_prop
  constructor
  · intro x
    have hgt : Tendsto (fun t : ℝ => a * t + b) (𝓝[>] x) (𝓝[>] (a * x + b)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((hcont.tendsto x).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : x < y := hy
      have hlt : a * x < a * y := mul_lt_mul_of_pos_left hy' ha
      simp only [Set.mem_Ioi]
      linarith
    exact (hf.isRightContinuous (a * x + b)).tendsto.comp hgt
  · intro x
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (a * x + b)
    refine ⟨l, hl.comp ?_⟩
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hcont.tendsto x).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y < x := hy
    have hlt : a * y < a * x := mul_lt_mul_of_pos_left hy' ha
    simp only [Set.mem_Iio]
    linarith

namespace CadlagPath

variable {S : Type*} [TopologicalSpace S]

/-- **The time flow on the coding**, `θ_r Ω` with `(θ_r Ω)_t = X_{t+r}(Ω)`. -/
def timeShift (r : ℝ) (ω : CadlagPath S) : CadlagPath S where
  toFun t := ω.toFun (t + r)
  isCadlag' := by
    simpa using isCadlag_comp_affine ω.isCadlag' (a := 1) (b := r) one_pos

@[simp] theorem timeShift_apply (r : ℝ) (ω : CadlagPath S) (t : ℝ) :
    (timeShift r ω).toFun t = ω.toFun (t + r) := rfl

@[simp] theorem timeShift_zero (ω : CadlagPath S) : timeShift 0 ω = ω :=
  ext' (funext fun t => by simp)

/-- **The parabolic dilation on the coding.**  With `a = C²`, this is the time
and label part of the manuscript's `S_C Ω = (C𝓗, (C X_{t/C²}))`: the cells are
reindexed by `φ` and the clock is rescaled by `a`. -/
noncomputable def parabolicDilate {S' : Type*} [TopologicalSpace S'] {φ : S → S'}
    (hφ : Continuous φ) {a : ℝ} (ha : 0 < a) (ω : CadlagPath S) : CadlagPath S' where
  toFun t := φ (ω.toFun (a⁻¹ * t))
  isCadlag' := by
    have h := (isCadlag_comp_affine ω.isCadlag' (a := a⁻¹) (b := 0)
      (inv_pos.2 ha)).continuous_comp hφ
    simpa [Function.comp_def] using h

@[simp] theorem parabolicDilate_apply {S' : Type*} [TopologicalSpace S'] {φ : S → S'}
    (hφ : Continuous φ) {a : ℝ} (ha : 0 < a) (ω : CadlagPath S) (t : ℝ) :
    (parabolicDilate hφ ha ω).toFun t = φ (ω.toFun (a⁻¹ * t)) := rfl

variable [MeasurableSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [BorelSpace S]

/-- The time flow is measurable: "scaling time is a measurable operation on this
coding". -/
theorem measurable_timeShift (r : ℝ) : Measurable (timeShift (S := S) r) :=
  measurable_of_ratEval fun q => measurable_eval ((q : ℝ) + r)

/-- **Criterion for time-shift invariance of a law on the coding.**

To know that the real time shift `θ_r` preserves a measure `Q` it suffices to
know that the *rational-time* process `q ↦ X_{q+r}` has the same law under `Q` as
`q ↦ X_q`.  That is exactly the "Markov cylinder distributions" input of
`p:eq:sigmapath`, and it is checked on finite-dimensional distributions only.

No finiteness of `Q` is required, so this applies verbatim to the σ-finite
fixed-environment mixture `Q_H = ∑_v a_v P_H^v`, which is the measure the
manuscript actually shifts.  Nothing here asserts that any particular law
satisfies the hypothesis. -/
theorem measurePreserving_timeShift_of_ratEval_law (Q : Measure (CadlagPath S)) (r : ℝ)
    (h : Q.map (fun ω : CadlagPath S => fun q : ℚ => ω.toFun ((q : ℝ) + r)) = Q.map ratEval) :
    MeasurePreserving (timeShift (S := S) r) Q Q := by
  refine ⟨measurable_timeShift r, eq_of_map_ratEval_eq ?_⟩
  rw [Measure.map_map measurable_ratEval (measurable_timeShift r)]
  exact h

end CadlagPath

/-! ## The parabolic change of variables

The manuscript's scaling bookkeeping for `p:eq:spacefromtime` is

> Under spatial dilation, `a_{H_z}` and `dt` each acquire a factor `C²`, whereas
> `V` acquires a factor `C^{-2}`.

Here is the `dt`-versus-`V` half of it, as one change of variables `t = C² r`. -/

/-- Change of variables `t = a·r` for a lower Lebesgue integral on the time line.
No measurability of `f` is needed, because multiplication by `a ≠ 0` is a
measurable equivalence. -/
theorem lintegral_comp_const_mul (f : ℝ → ℝ≥0∞) {a : ℝ} (ha : a ≠ 0) :
    ∫⁻ t : ℝ, f t = ENNReal.ofReal |a| * ∫⁻ r : ℝ, f (a * r) := by
  have hequiv : ∫⁻ t : ℝ, f t ∂(Measure.map (fun x : ℝ => a * x) volume)
      = ∫⁻ r : ℝ, f (a * r) := by
    simpa using lintegral_map_equiv (μ := (volume : Measure ℝ)) f (MeasurableEquiv.mulLeft₀ a ha)
  calc ∫⁻ t : ℝ, f t
      = ∫⁻ t : ℝ, f t ∂((ENNReal.ofReal |a|) • Measure.map (fun x : ℝ => a * x) volume) := by
        rw [Real.smul_map_volume_mul_left ha]
    _ = ENNReal.ofReal |a| * ∫⁻ t : ℝ, f t ∂(Measure.map (fun x : ℝ => a * x) volume) := by
        rw [lintegral_smul_measure]; rfl
    _ = ENNReal.ofReal |a| * ∫⁻ r : ℝ, f (a * r) := by rw [hequiv]

namespace CadlagPath

variable {S : Type*} [TopologicalSpace S]
variable {S' : Type*} [TopologicalSpace S']

variable [MeasurableSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [BorelSpace S]
variable [MeasurableSpace S'] [TopologicalSpace.PseudoMetrizableSpace S'] [BorelSpace S']

end CadlagPath

end ReflectedGMS.TrajectoryCoding
