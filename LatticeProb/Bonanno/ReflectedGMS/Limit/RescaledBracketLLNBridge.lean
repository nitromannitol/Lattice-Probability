/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RescaledBracketLLNBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ApproximateBracketCLTRescaled
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalizedArrayProducer
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNUniformProbability

/-!
# The reparametrisation: the a.s. bracket law of large numbers feeds `RescaledBracketLLN`

The temporal-homogenization route produces the bracket law of large numbers in the shape

```
∀ᵐ ω ∂P, ∀ r : ℝ, TendstoUniformlyOn
  (fun (e : ℝ) (s : ℝ) => e ^ 2 * A (Real.toNNReal (s / e ^ 2)) ω)
  (fun s : ℝ => s * C) (𝓝[>] (0 : ℝ)) (Set.Icc 0 r)
```

(`Limit/BracketLLNRegenerativeWeld.canonicalBracket_bracket_limit_of_regenerativeInvariance`,
and before it `Limit/ActualArrayBracketLimit.canonicalBracket_bracket_limit`): almost surely,
locally uniformly, and parameterised by a **real** scale `e` through `Real.toNNReal (s / e ^ 2)`.

The CLT's named input is
`Limit/ApproximateBracketCLTRescaled.RescaledBracketLLN P A C`: along every sequence
`ε : ℕ → ℝ≥0` with `ε k → 0⁺`, at every **fixed** time `t : ℝ≥0` and tolerance `δ > 0`,

```
P {ω | δ < |(ε k) ^ 2 * A ((ε k)⁻¹ ^ 2 * t) ω - C * t|} → 0.
```

This module is the reparametrisation between the two.  There are exactly three things to check,
and none of them is a real mismatch:

* **the time argument.**  `Real.toNNReal ((t : ℝ) / (e : ℝ) ^ 2) = e⁻¹ ^ 2 * t` for **every**
  `e t : ℝ≥0`, with no positivity side condition (`toNNReal_div_sq`): at `e = 0` both sides are
  `0`, because `(0 : ℝ)⁻¹ = 0` and division by `0` is `0`.  So the `ε = 0` worry is vacuous and
  the identity never has to be gated by the eventual positivity of `ε`;
* **the index type.**  A sequence `ε : ℕ → ℝ≥0` with `Tendsto ε atTop (𝓝[>] 0)` coerces to a
  real sequence with `Tendsto (fun k => (ε k : ℝ)) atTop (𝓝[>] 0)` (`tendsto_coe_nhdsWithin`),
  so the real-scale filter limit composes into the sequential one.  Nothing is lost: the real
  statement is the stronger one;
* **the order of limits.**  The locally uniform statement is only ever used at the single point
  `s = t` of `Icc 0 t`, through `TendstoUniformlyOn.tendsto_at`.  The uniformity is therefore
  *not* needed here; it is needed by the other consumer (below), which recovers it from
  monotonicity.

## One hypothesis, two consumers

The `hinc` input of the FCLT lane
(`ApproximateBracketCLTRescaled.rescaledIncrementCharFunLimit_of_bracket_data`, field `hLLN`)
and the `ucp` input of the tightness lane
(`Limit/LocalizedArrayProducer.ThresholdArrayInputs`, reduced to its fixed-time `lln` form by
`Limit/BracketLLNThresholdWiring.thresholdArrayInputs_of_pointwise`) are fed by **the same**
bracket hypothesis.  `lln_of_rescaledBracketLLN` and `thresholdArrayInputs_of_rescaledBracketLLN`
say so: at the rescaled array `V k := rescaledBracket A ε k` the `lln` field is literally an
instance of `RescaledBracketLLN P A C` — weaker, in fact, since `lln` only asks for `t ≤ T`
while `RescaledBracketLLN` asks for all `t` and all scale sequences.

**This is an implication.**  Nothing here certifies the bracket law of large numbers in any
form, nor `p:lem:bracketlimit`, `p:thm:areaclt`, `hinc`, `hlimit` or either main theorem.
-/

-- Merged from `ReflectedGMS/Limit/BracketLLNAlmostSureBridge.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_BracketLLNAlmostSureBridge

/-!
# From the almost-sure bracket law of large numbers to the `ucp` field

The temporal-homogenization route produces the bracket law of large numbers **almost surely**
(`Limit/BracketLLNRegenerativeWeld.canonicalBracket_bracket_limit_of_regenerativeInvariance`, and
before it `Limit/ActualArrayBracketLimit.canonicalBracket_bracket_limit`), whereas the `ucp` field
of `Limit/LocalizedArrayProducer.ThresholdArrayInputs` is a statement about measures of *uniform*
bad events.  This module is the bridge, and it is deliberately routed through the **fixed-time**
statement rather than directly.

## Why not go directly from almost-sure uniform convergence

If one already has `∀ᵐ ω, ∀ ε > 0, ∀ᶠ n, ∀ t ∈ [0,T], |V n t ω - v t| ≤ ε`, the `ucp` field still
does not follow, because deducing `P (A n) → 0` from "almost every `ω` is eventually outside
`A n`" needs the sets `A n` to be measurable: an outer measure is not continuous from above, and
`A n = {ω | ∃ t ∈ [0,T], ε < |V n t ω - v t|}` quantifies over an *uncountable* index set, so its
measurability is a genuine side condition (a separability or countable-dense-set reduction of the
path).

Going through the fixed time costs nothing and needs only measurability of `V n t` at each
**deterministic** `t`, which the `adapted_bracket` field of `ThresholdArrayInputs` already gives:

almost sure at fixed `t` → in probability at fixed `t` (`tendstoInMeasure_of_tendsto_ae`,
finite measure) → uniform in probability on `[0,T]`
(`BracketLLNUniform.tendsto_measure_exists_gt_of_tendsto_pointwise`, monotonicity, no
measurability).

## Contents

* `tendsto_measure_gt_of_ae_tendsto` — convergence in probability at a fixed time, in the
  strict-inequality shape the `ucp` field uses.
* `tendsto_measure_exists_gt_of_ae_tendsto` — **the bridge**, in exactly the shape of the `ucp`
  field.

Nothing here is about the reflected walk, and nothing here certifies the bracket law of large
numbers in any form.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.BracketLLNUniform

/-- **Almost-sure convergence to a constant gives convergence in probability**, in the
strict-inequality shape `P {|f n - c| > δ} → 0` used by the `ucp` field.

Only `AEStronglyMeasurable (f n)` is needed, and the measure must be finite. -/
theorem tendsto_measure_gt_of_ae_tendsto
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {f : ℕ → Ω → ℝ} {c : ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 c))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ < |f n ω - c|}) atTop (𝓝 0) := by
  have hmeasure : TendstoInMeasure P f atTop (fun _ => c) :=
    tendstoInMeasure_of_tendsto_ae hmeas hae
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have hlim := hmeasure (ENNReal.ofReal δ) hpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  have hω' : δ < |f n ω - c| := hω
  show ENNReal.ofReal δ ≤ edist (f n ω) c
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hω'.le

end ReflectedGMS.BracketLLNUniform

end Merged_BracketLLNAlmostSureBridge

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.RescaledBracketLLNBridge

open ReflectedGMS.ApproximateBracketCLT ReflectedGMS.BracketLLNUniform
open ReflectedGMS.LocalizedArrayProducer

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## The two reparametrisation lemmas -/

/-- **The time reparametrisation, with no side condition.**  `Real.toNNReal (t / e²) = e⁻¹² · t`
for all `e t : ℝ≥0`.

At `e = 0` both sides are `0`: in `ℝ` division by zero is zero, and in `ℝ≥0` the inverse of `0`
is `0`.  So the real-scale form `Real.toNNReal (t / e ^ 2)` used by the almost-sure bracket
limit and the nonnegative-scale form `e⁻¹ ^ 2 * t` used by `RescaledBracketLLN` agree
everywhere, and the identity never needs the eventual positivity of the scale sequence. -/
theorem toNNReal_div_sq (e t : ℝ≥0) :
    Real.toNNReal ((t : ℝ) / (e : ℝ) ^ 2) = e⁻¹ ^ 2 * t := by
  have h : ((t : ℝ) / (e : ℝ) ^ 2) = ((e⁻¹ ^ 2 * t : ℝ≥0) : ℝ) := by
    push_cast
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  rw [h, Real.toNNReal_coe]

/-- **The index reparametrisation.**  A nonnegative scale sequence tending to `0` from the right
coerces to a real scale sequence tending to `0` from the right. -/
theorem tendsto_coe_nhdsWithin {ε : ℕ → ℝ≥0}
    (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))) :
    Tendsto (fun k => ((ε k : ℝ))) atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h0 : Tendsto ε atTop (𝓝 (0 : ℝ≥0)) := hε.mono_right nhdsWithin_le_nhds
    have h1 : Tendsto (fun k => ((ε k : ℝ))) atTop (𝓝 (((0 : ℝ≥0) : ℝ))) :=
      NNReal.tendsto_coe.mpr h0
    simpa using h1
  · filter_upwards [hε.eventually eventually_mem_nhdsWithin] with k hk
    have hk' : (0 : ℝ≥0) < ε k := hk
    exact Set.mem_Ioi.2 (by exact_mod_cast hk')

/-! ## `RescaledBracketLLN` from the almost-sure form -/

/-- **`RescaledBracketLLN` from the almost-sure real-scale limit at each fixed time.**

`hmeas` is fixed-time measurability of the bracket (an `AEStronglyMeasurable` at each
deterministic time, which the `adapted_bracket` field of the array lane already supplies), and
`hae` is the almost-sure convergence along the **real** scale filter `𝓝[>] 0` at each fixed
time.  Only a finite measure is needed.

The proof is the reparametrisation and nothing else: compose the real-scale limit with the
coerced scale sequence (`tendsto_coe_nhdsWithin`), rewrite the time argument
(`toNNReal_div_sq`), and turn almost-sure convergence into convergence in probability with
`BracketLLNAlmostSureBridge.tendsto_measure_gt_of_ae_tendsto`. -/
theorem rescaledBracketLLN_of_ae_tendsto {P : Measure Ω} [IsFiniteMeasure P]
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hmeas : ∀ u : ℝ≥0, AEStronglyMeasurable (A u) P)
    (hae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun e : ℝ => e ^ 2 * A (Real.toNNReal ((t : ℝ) / e ^ 2)) ω)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (C * (t : ℝ)))) :
    RescaledBracketLLN P A C := by
  intro ε hε t δ hδ
  have hcoe := tendsto_coe_nhdsWithin hε
  refine tendsto_measure_gt_of_ae_tendsto
    (f := fun k ω => (ε k : ℝ) ^ 2 * A ((ε k)⁻¹ ^ 2 * t) ω) (c := C * (t : ℝ))
    (fun k => (hmeas _).const_mul _) ?_ hδ
  filter_upwards [hae] with ω hω
  have h := (hω t).comp hcoe
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, toNNReal_div_sq]

/-! ## The directional combination -/

/-- The directional bracket of a matrix-valued bracket: `η ↦ ∑ᵢⱼ ηᵢ Bᵢⱼ ηⱼ`.

This is the bracket of the scalar projection `⟪η, M⟫` when `B i j` is the predictable covariation
of `M i` and `M j`, i.e. the object the CLT calls `A η`. -/
def dirBracket (B : Fin 2 → Fin 2 → ℝ≥0 → Ω → ℝ) (η : EuclideanSpace ℝ (Fin 2))
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, η i * B i j u ω * η j

/-- **The directional combination of the entrywise bracket limits.**

From the almost-sure fixed-time limit of each of the four matrix entries, with limiting matrix
`Σ`, the directional bracket `∑ᵢⱼ ηᵢ Bᵢⱼ ηⱼ` has the limit `bilinForm Σ η η` — the constant the
CLT asks for.  The combination is a four-term finite sum, so it is done at the pointwise layer
where it costs one `tendsto_finset_sum`; doing it after passing to measures of bad events would
instead cost a union bound. -/
theorem ae_tendsto_dirBracket {P : Measure Ω} {B : Fin 2 → Fin 2 → ℝ≥0 → Ω → ℝ}
    {Sig : Matrix (Fin 2) (Fin 2) ℝ} (η : EuclideanSpace ℝ (Fin 2))
    (hae : ∀ᵐ ω ∂P, ∀ (i j : Fin 2) (t : ℝ≥0),
      Tendsto (fun e : ℝ => e ^ 2 * B i j (Real.toNNReal ((t : ℝ) / e ^ 2)) ω)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Sig i j * (t : ℝ)))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun e : ℝ => e ^ 2 * dirBracket B η (Real.toNNReal ((t : ℝ) / e ^ 2)) ω)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (GaussianLimitIdentification.bilinForm Sig η η * (t : ℝ))) := by
  filter_upwards [hae] with ω hω t
  have hterm : ∀ i j : Fin 2,
      Tendsto (fun e : ℝ => η i * (e ^ 2 * B i j (Real.toNNReal ((t : ℝ) / e ^ 2)) ω) * η j)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (η i * (Sig i j * (t : ℝ)) * η j)) :=
    fun i j => ((hω i j t).const_mul (η i)).mul_const (η j)
  have hsum : Tendsto
      (fun e : ℝ => ∑ i : Fin 2, ∑ j : Fin 2,
        η i * (e ^ 2 * B i j (Real.toNNReal ((t : ℝ) / e ^ 2)) ω) * η j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (∑ i : Fin 2, ∑ j : Fin 2, η i * (Sig i j * (t : ℝ)) * η j)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hterm i j
  have hval : ∀ e : ℝ,
      e ^ 2 * dirBracket B η (Real.toNNReal ((t : ℝ) / e ^ 2)) ω
        = ∑ i : Fin 2, ∑ j : Fin 2,
            η i * (e ^ 2 * B i j (Real.toNNReal ((t : ℝ) / e ^ 2)) ω) * η j := by
    intro e
    simp only [dirBracket, Fin.sum_univ_two]
    ring
  have hlim : GaussianLimitIdentification.bilinForm Sig η η * (t : ℝ)
      = ∑ i : Fin 2, ∑ j : Fin 2, η i * (Sig i j * (t : ℝ)) * η j := by
    simp only [GaussianLimitIdentification.bilinForm, Fin.sum_univ_two]
    ring
  rw [hlim]
  exact hsum.congr fun e => (hval e).symm

/-! ## One hypothesis, two consumers -/

/-- The rescaled bracket array: the `k`-th process of the localized array lane is
`t ↦ εₖ² A(t/εₖ²)`, the very object `RescaledBracketLLN` is about. -/
noncomputable def rescaledBracket (A : ℝ≥0 → Ω → ℝ) (ε : ℕ → ℝ≥0) (k : ℕ) (t : ℝ≥0) (ω : Ω) :
    ℝ :=
  (ε k : ℝ) ^ 2 * A ((ε k)⁻¹ ^ 2 * t) ω

/-- **The array producer's `lln` field is an instance of the CLT's `RescaledBracketLLN`.**

`lln` is the hypothesis of `Limit/BracketLLNThresholdWiring.thresholdArrayInputs_of_pointwise`
that replaces the `ucp` field of `LocalizedArrayProducer.ThresholdArrayInputs`; `RescaledBracketLLN`
is the `hLLN` hypothesis of
`ApproximateBracketCLTRescaled.rescaledIncrementCharFunLimit_of_bracket_data`.  At the rescaled
array they are the same statement, and the proof term is the identity up to discarding `t ≤ T`:
`RescaledBracketLLN` is the (very slightly) stronger one, because it quantifies over all times
and all scale sequences rather than over `t ≤ T` at one sequence. -/
theorem lln_of_rescaledBracketLLN {P : Measure Ω} {A : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hLLN : RescaledBracketLLN P A C) {ε : ℕ → ℝ≥0}
    (hε : Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))) (T : ℝ≥0) :
    ∀ t : ℝ≥0, t ≤ T → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun k => P {ω | δ < |rescaledBracket A ε k t ω - C * (t : ℝ)|}) atTop (𝓝 0) :=
  fun t _ => hLLN ε hε t

end ReflectedGMS.RescaledBracketLLNBridge
