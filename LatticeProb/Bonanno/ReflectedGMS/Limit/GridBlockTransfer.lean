/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.GridBlockTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketTimeAverage
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The grid-probability transfer of `p:prop:timeergodic`, and the block data of `hblk`

`ReflectedGMS/Limit/BracketTimeAverage.lean` reduced the bracket law of large numbers for
`Φ(Y)` to a single named input, its `hblk`:

```
∀ δ > 0, ∀ᶠ T in atTop, ∃ J, MeasurableSet J ∧ Ioc 0 T ⊆ J ∧
  volume J ≤ ENNReal.ofReal ((1 + δ) * T) ∧ IntegrableOn f J volume ∧ setAvg J f ≤ c + δ
```

## A correction: `hblk` is not a reduction

`hblk` is **equivalent** to the conclusion it is used to prove.  Given the Cesàro bound
`∀ᶠ T, (∫₀ᵀ f)/T ≤ c + δ` one takes `J = Ioc 0 T`: it is measurable, contains `Ioc 0 T`,
has `volume J = ENNReal.ofReal T ≤ ENNReal.ofReal ((1+δ)T)`, and `setAvg (Ioc 0 T) f` **is**
the interval average (`BracketTimeAverage.directionalAverage_eq_setAvg`).  So nothing is
gained by producing `hblk` pathwise, and — more importantly — the manuscript never does.

The manuscript's transfer step (tex:1553-1562) is a **contradiction argument over the
independent uniform time grid**: it never exhibits a tight origin block for all large `T`,
only for the `T`'s along one witness sequence and only for a grid drawn from a set of
probability at least the constant `p_δ` of `p:eq:gridprob`.  This module carries out that
argument.  `intervalAverage_le_of_gridChainData` is the manuscript's upper bound and is the
genuine replacement for `hblk`.

## What is proved here

Fix one trajectory, i.e. one nonnegative density `f` on the time axis.  `GridChainData`
bundles the two probabilistic inputs the manuscript uses, both about the **grid law `ν`
alone**:

* `grid` — `p:eq:gridprob`: for every `δ > 0` there is a strictly positive `p_δ` such that
  for every `T > 0` the grid event `gridBlockEvent blk δ T` (some root block contains
  `(0,T]` and has length at most `(1+δ)T`) has probability at least `p_δ`.  The constant
  must depend on `δ` — as `δ ↓ 0` these events decrease to "a root block has length exactly
  `T`", which is null, so a `δ`-uniform positive constant would make the hypothesis
  unsatisfiable — but it must **not** depend on `T`, and does not, by scale invariance of
  the grid law;
* `chain` — the conclusion of `p:lem:timeconverge` read in the manuscript's own
  "all sufficiently long root blocks" form: for `ν`-almost every grid, every root block of
  length at least some `R = R(η)` has block average within `η` of `μ`.

From these:

* `intervalAverage_le_of_gridChainData` — the manuscript's **upper bound**
  `limsup_T T⁻¹∫₀ᵀ f ≤ μ`, for a general nonnegative `f`, with no boundedness assumption.
  This is the whole content of the transfer step; the proof is the manuscript's:
  a witness sequence `T_n → ∞`, the positive grid probability, continuity from above for
  the tail of the witness events, and one grid realisation that is simultaneously good for
  the chain and tight around arbitrarily large witnesses.
* `le_intervalAverage_of_gridChainData` — the manuscript's **lower bound** for a bounded
  nonnegative density, obtained exactly as the manuscript does it, by applying the upper
  bound to `K - f` (`GridChainData.constSub`).
* `HasBlockData` and `tendsto_intervalAverage_of_hasBlockData` — the two bounds plus the
  manuscript's truncation (tex:1561, "apply the bounded result to `F ∧ K` and let
  `K ↑ ∞`") give the Cesàro limit `T⁻¹∫₀ᵀ f → μ` for an unbounded nonnegative density.
  The truncation family and its means enter as data, because each truncated functional is a
  separate instance of the temporal machinery.
* `canonicalBracket_bracket_limit_of_blockData` —
  `MartingaleLimit.canonicalBracket_bracket_limit` for the actual quenched array of `Φ(Y)`
  with `hLLN` **and** `BracketTimeAverage.hblk` both discharged, in favour of the block data
  for the three polarization directions of
  `BracketTimeAverage.tendsto_ordinaryEdgeBracket_div_of_directional`.

## What is *not* proved here

The two inputs themselves.  `p:eq:gridprob` is a computation for the one-dimensional marked
dyadic system of `Temporal/ActualDyadicTemporalBlocks`, and the `chain` field is
`Temporal/ConditionalTemporalAveraging.tendsto_setAverageReal_chain_ae` **together with**
the identification of its tail conditional expectation as the constant `𝔼[Γ]`
(`p:lem:regeninvariant` plus environment ergodicity).  Neither is done here, and nothing in
this file certifies `p:prop:timeergodic`, `p:thm:areaclt` or either main theorem.  No
ergodicity, no triviality of a tail σ-field and no time-shift invariance of any law is
assumed or asserted; the hypotheses below mention only the grid law `ν`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.GridBlockTransfer

open ReflectedGMS.MartingaleIngredients ReflectedGMS.MartingaleLimit
open ReflectedGMS.BracketTimeAverage

variable {G ι : Type*} [MeasurableSpace G]

/-! ### The grid event of `p:eq:gridprob` -/

/-- **The event of `p:eq:gridprob`.**  Some root block of the grid `Dg` contains the
interval `(0,T]` and has length at most `(1+δ)T`.

In the manuscript the blocks are the root dyadic intervals of the independent uniform time
grid, and the probability of this event is the strictly positive constant
`p_δ = (log 2)⁻¹ ∫₁^{1+δ} (r-1)r⁻² dr`. -/
def gridBlockEvent (blk : G → ι → Set ℝ) (δ T : ℝ) : Set G :=
  {Dg : G | ∃ k : ι, Set.Ioc (0 : ℝ) T ⊆ blk Dg k ∧
    volume (blk Dg k) ≤ ENNReal.ofReal ((1 + δ) * T)}

/-- Continuity from above along the tail of a sequence of events: if every `S n` has measure
at least `c`, so does the set of points lying in `S n` for arbitrarily large `n`. -/
theorem le_measure_iInter_iUnion_shift (ν : Measure G) [IsFiniteMeasure ν] (S : ℕ → Set G)
    (hS : ∀ n : ℕ, MeasurableSet (S n)) (c : ℝ≥0∞) (hc : ∀ n : ℕ, c ≤ ν (S n)) :
    c ≤ ν (⋂ N : ℕ, ⋃ n : ℕ, S (N + n)) := by
  have hUmeas : ∀ N : ℕ, NullMeasurableSet (⋃ n : ℕ, S (N + n)) ν := fun N =>
    (MeasurableSet.iUnion fun n => hS (N + n)).nullMeasurableSet
  have hUanti : Antitone fun N : ℕ => ⋃ n : ℕ, S (N + n) := by
    intro a b hab x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨(b - a) + n, ?_⟩
    have hidx : a + ((b - a) + n) = b + n := by omega
    rw [hidx]
    exact hn
  refine ge_of_tendsto
    (tendsto_measure_iInter_atTop hUmeas hUanti ⟨0, measure_ne_top ν _⟩)
    (Eventually.of_forall fun N => ?_)
  refine le_trans (hc N) (measure_mono fun x hx => Set.mem_iUnion.2 ⟨0, ?_⟩)
  simpa using hx

/-! ### Two elementary identities for the constant-shift trick -/

/-- The block average of `K - f` is `K` minus the block average of `f`. -/
theorem setAvg_const_sub {J : Set ℝ} (hJ0 : volume J ≠ 0) (hJtop : volume J ≠ ⊤)
    {f : ℝ → ℝ} (hfJ : IntegrableOn f J volume) (K : ℝ) :
    setAvg J (fun s => K - f s) = K - setAvg J f := by
  have hV : (0 : ℝ) < (volume J).toReal := ENNReal.toReal_pos hJ0 hJtop
  have hconst : IntegrableOn (fun _ : ℝ => K) J volume := integrableOn_const (C := K) hJtop
  have hsplit : (∫ s in J, (K - f s)) = (volume J).toReal * K - ∫ s in J, f s := by
    have h1 : (∫ s in J, (K - f s)) = (∫ _s in J, (K : ℝ)) - ∫ s in J, f s :=
      integral_sub hconst hfJ
    rw [h1, setIntegral_const, measureReal_def, smul_eq_mul]
  rw [setAvg, setAvg, hsplit, mul_sub, ← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]

/-- The interval integral of `K - f` over `[0,T]`. -/
theorem intervalIntegral_const_sub {f : ℝ → ℝ} {T : ℝ}
    (hfint : IntervalIntegrable f volume 0 T) (K : ℝ) :
    (∫ s in (0 : ℝ)..T, (K - f s)) = K * T - ∫ s in (0 : ℝ)..T, f s := by
  have hconst : IntervalIntegrable (fun _ : ℝ => K) volume 0 T := intervalIntegrable_const
  have h1 : (∫ s in (0 : ℝ)..T, (K - f s))
      = (∫ _s in (0 : ℝ)..T, (K : ℝ)) - ∫ s in (0 : ℝ)..T, f s :=
    intervalIntegral.integral_sub hconst hfint
  rw [h1, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm T K]

/-! ### The manuscript's two probabilistic inputs -/

/-- **The block data of the manuscript's transfer step, for one nonnegative time density.**

Both probabilistic fields are statements about the **grid law `ν` alone**; the density `f`
is a fixed function of time (in the application, the directional bracket density along one
fixed trajectory).

* `grid` is `p:eq:gridprob`;
* `chain` is the conclusion of the complete-chain convergence `p:lem:timeconverge` in the
  manuscript's own "all sufficiently long root blocks" form, with its limit already
  identified as the constant `μ`.

Nothing in this structure asserts either of them. -/
structure GridChainData (ν : Measure G) (blk : G → ι → Set ℝ) (f : ℝ → ℝ) (μ : ℝ) :
    Prop where
  /-- The density is nonnegative, as in the transfer step of `p:prop:timeergodic`. -/
  nonneg : ∀ s : ℝ, 0 ≤ f s
  /-- The density is locally integrable along the time axis. -/
  intervalIntegrable : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable f volume 0 T
  /-- The blocks are measurable. -/
  measurableSet_block : ∀ (Dg : G) (k : ι), MeasurableSet (blk Dg k)
  /-- The blocks have positive length. -/
  volume_ne_zero : ∀ (Dg : G) (k : ι), volume (blk Dg k) ≠ 0
  /-- The blocks have finite length. -/
  volume_ne_top : ∀ (Dg : G) (k : ι), volume (blk Dg k) ≠ ⊤
  /-- The density is integrable on every block. -/
  integrableOn : ∀ (Dg : G) (k : ι), IntegrableOn f (blk Dg k) volume
  /-- The grid event is measurable. -/
  measurableSet_grid : ∀ δ T : ℝ, MeasurableSet (gridBlockEvent blk δ T)
  /-- **`p:eq:gridprob`.**  The constant `p_δ` genuinely depends on `δ` — it decreases to `0`
  as `δ ↓ 0`, because the limiting event is that a root block has length exactly `T` — but it
  does not depend on `T`, by scale invariance of the grid law. -/
  grid : ∀ δ : ℝ, 0 < δ → ∃ p : ℝ, 0 < p ∧
    ∀ T : ℝ, 0 < T → ENNReal.ofReal p ≤ ν (gridBlockEvent blk δ T)
  /-- **`p:lem:timeconverge`, with its limit identified as `μ`.** -/
  chain : ∀ᵐ Dg ∂ν, ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ k : ι,
    ENNReal.ofReal R ≤ volume (blk Dg k) → |setAvg (blk Dg k) f - μ| ≤ η

/-- **The manuscript's `K - F` reflection** (tex:1561, "apply this upper bound to `K - F`").
The same grid and the same blocks work for the reflected density. -/
theorem GridChainData.constSub {ν : Measure G} {blk : G → ι → Set ℝ} {f : ℝ → ℝ} {μ : ℝ}
    (h : GridChainData ν blk f μ) {K : ℝ} (hfK : ∀ s : ℝ, f s ≤ K) :
    GridChainData ν blk (fun s => K - f s) (K - μ) :=
  { nonneg := fun s => sub_nonneg.2 (hfK s)
    intervalIntegrable := fun T hT => by
      have hc : IntervalIntegrable (fun _ : ℝ => K) volume 0 T := intervalIntegrable_const
      exact hc.sub (h.intervalIntegrable T hT)
    measurableSet_block := h.measurableSet_block
    volume_ne_zero := h.volume_ne_zero
    volume_ne_top := h.volume_ne_top
    integrableOn := fun Dg k => by
      have hc : IntegrableOn (fun _ : ℝ => K) (blk Dg k) volume :=
        integrableOn_const (C := K) (h.volume_ne_top Dg k)
      exact hc.sub (h.integrableOn Dg k)
    measurableSet_grid := h.measurableSet_grid
    grid := h.grid
    chain := by
      filter_upwards [h.chain] with Dg hDg
      intro η hη
      obtain ⟨R, hR⟩ := hDg η hη
      refine ⟨R, fun k hk => ?_⟩
      rw [setAvg_const_sub (h.volume_ne_zero Dg k) (h.volume_ne_top Dg k)
        (h.integrableOn Dg k) K]
      have hneg : K - setAvg (blk Dg k) f - (K - μ) = -(setAvg (blk Dg k) f - μ) := by ring
      rw [hneg, abs_neg]
      exact hR k hk }

/-! ### The upper bound: the manuscript's transfer argument -/

/-- **The transfer step of `p:prop:timeergodic` (tex:1553-1562): the upper bound.**

For a nonnegative density with the block data above, the Cesàro averages over `[0,T]` are
eventually at most `μ + ε`.  No boundedness of `f` is assumed.

The proof is the manuscript's.  Suppose the bound fails frequently.  Fix `δ > 0` small
enough that `(1+δ)(μ + ε/2) < μ + ε`, and choose a witness `T_n ≥ max(n,1)` with
`T_n⁻¹∫₀^{T_n} f > μ + ε` for every `n`.  Each witness event
`gridBlockEvent blk δ T_n` has `ν`-probability at least `p`, so by continuity from above the
set of grids lying in `gridBlockEvent blk δ T_n` for arbitrarily large `n` also has
probability at least `p > 0`; it therefore meets the full-measure set on which the chain
bound holds.  For such a grid, a block `J` tight around a witness longer than the chain
threshold satisfies simultaneously

```
setAvg J f ≤ μ + ε/2     and     setAvg J f ≥ (μ+ε)T_n / ((1+δ)T_n) > μ + ε/2,
```

the second because `f ≥ 0` makes `∫_J f ≥ ∫₀^{T_n} f > (μ+ε)T_n` while `|J| ≤ (1+δ)T_n`.

CONDITIONAL on `GridChainData`; nothing here certifies `p:eq:gridprob` or
`p:lem:timeconverge`. -/
theorem intervalAverage_le_of_gridChainData {ν : Measure G} [IsFiniteMeasure ν]
    {blk : G → ι → Set ℝ} {f : ℝ → ℝ} {μ : ℝ} (h : GridChainData ν blk f μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (∫ s in (0 : ℝ)..T, f s) / T ≤ μ + ε := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- Step 1: the manuscript's choice of `δ`, so that `(1+δ)(μ + ε/2) < μ + ε`.
  obtain ⟨δ, hδpos, hkey⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 + δ) * (μ + ε / 2) < μ + ε := by
    have habs : (0 : ℝ) ≤ |μ| := abs_nonneg μ
    have hden : (0 : ℝ) < 2 * (1 + |μ| + ε) := by linarith
    have hdpos : (0 : ℝ) < min 1 (ε / (2 * (1 + |μ| + ε))) :=
      lt_min one_pos (div_pos hε hden)
    have hd2 : min 1 (ε / (2 * (1 + |μ| + ε))) ≤ ε / (2 * (1 + |μ| + ε)) := min_le_right _ _
    refine ⟨min 1 (ε / (2 * (1 + |μ| + ε))), hdpos, ?_⟩
    have h1 : min 1 (ε / (2 * (1 + |μ| + ε))) * (2 * (1 + |μ| + ε)) ≤ ε :=
      (le_div_iff₀ hden).1 hd2
    have h2 : μ + ε / 2 ≤ |μ| + ε := by linarith [le_abs_self μ]
    have h4 : min 1 (ε / (2 * (1 + |μ| + ε))) * (μ + ε / 2)
        ≤ min 1 (ε / (2 * (1 + |μ| + ε))) * (|μ| + ε) :=
      mul_le_mul_of_nonneg_left h2 hdpos.le
    linarith
  -- Step 2: the witness sequence.
  have hwit : ∀ n : ℕ, ∃ T : ℝ, max ((n : ℕ) : ℝ) 1 ≤ T ∧
      μ + ε < (∫ s in (0 : ℝ)..T, f s) / T := by
    intro n
    obtain ⟨T, hT1, hT2⟩ :=
      (hcon.and_eventually (eventually_ge_atTop (max ((n : ℕ) : ℝ) 1))).exists
    exact ⟨T, hT2, not_le.1 hT1⟩
  choose Tw hTwge hTwavg using hwit
  have hTwpos : ∀ n : ℕ, 0 < Tw n := fun n =>
    lt_of_lt_of_le one_pos (le_trans (le_max_right ((n : ℕ) : ℝ) 1) (hTwge n))
  -- Step 3: the grid events along the witnesses have a tail of probability at least `p_δ`.
  obtain ⟨p, hppos, hp⟩ := h.grid δ hδpos
  have hE : ENNReal.ofReal p ≤ ν (⋂ N : ℕ, ⋃ n : ℕ, gridBlockEvent blk δ (Tw (N + n))) :=
    le_measure_iInter_iUnion_shift ν (fun n => gridBlockEvent blk δ (Tw n))
      (fun n => h.measurableSet_grid δ (Tw n)) (ENNReal.ofReal p)
      (fun n => hp (Tw n) (hTwpos n))
  -- Step 4: one grid is simultaneously good for the chain and tight at arbitrarily large
  -- witnesses.
  obtain ⟨Dg, hDgE, hDgQ⟩ :
      ∃ Dg ∈ (⋂ N : ℕ, ⋃ n : ℕ, gridBlockEvent blk δ (Tw (N + n))),
        ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ k : ι,
          ENNReal.ofReal R ≤ volume (blk Dg k) → |setAvg (blk Dg k) f - μ| ≤ η := by
    by_contra hno
    have hnull : ν (⋂ N : ℕ, ⋃ n : ℕ, gridBlockEvent blk δ (Tw (N + n))) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 h.chain)
      intro Dg hDg
      simp only [Set.mem_setOf_eq]
      intro hQ
      exact hno ⟨Dg, hDg, hQ⟩
    exact absurd (le_trans hE (le_of_eq hnull))
      (not_le.2 (ENNReal.ofReal_pos.2 hppos))
  obtain ⟨R, hR⟩ := hDgQ (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 hDgE N)
  simp only [gridBlockEvent, Set.mem_setOf_eq] at hn
  obtain ⟨k, hksub, hkvol⟩ := hn
  -- Step 5: the two contradictory estimates for `setAvg (blk Dg k) f`.
  have hTpos : 0 < Tw (N + n) := hTwpos (N + n)
  have hcast : ((N : ℕ) : ℝ) ≤ ((N + n : ℕ) : ℝ) := Nat.cast_le.2 (Nat.le_add_right N n)
  have hRle : R ≤ Tw (N + n) :=
    le_trans hN (le_trans hcast (le_trans (le_max_left _ _) (hTwge (N + n))))
  have hvolge : ENNReal.ofReal R ≤ volume (blk Dg k) := by
    refine le_trans (ENNReal.ofReal_le_ofReal hRle) ?_
    rw [← volume_Ioc_zero (Tw (N + n))]
    exact measure_mono hksub
  have hJm : MeasurableSet (blk Dg k) := h.measurableSet_block Dg k
  have hVpos : (0 : ℝ) < (volume (blk Dg k)).toReal :=
    ENNReal.toReal_pos (h.volume_ne_zero Dg k) (h.volume_ne_top Dg k)
  have hVle : (volume (blk Dg k)).toReal ≤ (1 + δ) * Tw (N + n) := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkvol
    rwa [ENNReal.toReal_ofReal (mul_nonneg (by linarith) hTpos.le)] at hmono
  have hIge : (μ + ε) * Tw (N + n) < ∫ s in blk Dg k, f s := by
    have hstart : (μ + ε) * Tw (N + n) < ∫ s in (0 : ℝ)..Tw (N + n), f s :=
      (lt_div_iff₀ hTpos).1 (hTwavg (N + n))
    exact lt_of_lt_of_le hstart
      (intervalIntegral_le_setIntegral h.nonneg hTpos.le hJm hksub (h.integrableOn Dg k))
  have hInonneg : (0 : ℝ) ≤ ∫ s in blk Dg k, f s :=
    setIntegral_nonneg hJm fun x _ => h.nonneg x
  have hIub : (∫ s in blk Dg k, f s) ≤ (volume (blk Dg k)).toReal * (μ + ε / 2) := by
    have h4 : setAvg (blk Dg k) f ≤ μ + ε / 2 := by
      have hab := (abs_le.1 (hR k hvolge)).2
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hVpos.le
    rwa [setAvg, ← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul] at h5
  rcases le_or_gt 0 (μ + ε / 2) with hsign | hsign
  · have h1 : (volume (blk Dg k)).toReal * (μ + ε / 2) ≤ ((1 + δ) * Tw (N + n)) * (μ + ε / 2) :=
      mul_le_mul_of_nonneg_right hVle hsign
    have h2 : ((1 + δ) * Tw (N + n)) * (μ + ε / 2) < (μ + ε) * Tw (N + n) := by
      have h3 := mul_lt_mul_of_pos_right hkey hTpos
      calc ((1 + δ) * Tw (N + n)) * (μ + ε / 2)
          = ((1 + δ) * (μ + ε / 2)) * Tw (N + n) := by ring
        _ < (μ + ε) * Tw (N + n) := h3
    linarith
  · have hneg : (volume (blk Dg k)).toReal * (μ + ε / 2) < 0 :=
      mul_neg_of_pos_of_neg hVpos hsign
    linarith

/-! ### The lower bound for a bounded density -/

/-- **The transfer step of `p:prop:timeergodic`: the lower bound for a bounded nonnegative
density.**

This is the manuscript's "for bounded `F ≥ 0`, apply this upper bound to `K - F`"; the
reflection is `GridChainData.constSub`.

CONDITIONAL on `GridChainData`. -/
theorem le_intervalAverage_of_gridChainData {ν : Measure G} [IsFiniteMeasure ν]
    {blk : G → ι → Set ℝ} {f : ℝ → ℝ} {μ K : ℝ} (h : GridChainData ν blk f μ)
    (hfK : ∀ s : ℝ, f s ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, μ - ε ≤ (∫ s in (0 : ℝ)..T, f s) / T := by
  have hrefl := intervalAverage_le_of_gridChainData (h.constSub hfK) ε hε
  filter_upwards [hrefl, eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  have hT' : (K * T - ∫ s in (0 : ℝ)..T, f s) / T ≤ K - μ + ε := by
    rw [← intervalIntegral_const_sub (h.intervalIntegrable T hTpos.le) K]
    exact hT
  rw [sub_div, mul_div_assoc, div_self hTpos.ne', mul_one] at hT'
  linarith

/-! ### The Cesàro limit, with the manuscript's truncation -/

/-- **The complete block data for one nonnegative density**: the data for `f` itself,
together with the manuscript's truncation family (tex:1561).  `g K` is `f ∧ K` in the
manuscript, `μK K` is `𝔼[F ∧ K]`, and `μK K → μ` is monotone convergence.

Each `g K` is a separate unmarked scale-invariant functional, so its chain convergence is a
separate instance of the temporal machinery; that is why the family is data and not derived
here.

The truncation clauses are restricted to `0 < K` deliberately: `g K` must be nonnegative
(it is a `GridChainData` density) *and* bounded by `K`, which is impossible for `K < 0`.
With that restriction the family is satisfied by `g K s = min (f s) (max K 0)`. -/
def HasBlockData (ν : Measure G) (blk : G → ι → Set ℝ) (f : ℝ → ℝ) (μ : ℝ) : Prop :=
  GridChainData ν blk f μ ∧
    ∃ g : ℝ → ℝ → ℝ, ∃ μK : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → ∀ s : ℝ, g K s ≤ f s) ∧
      (∀ K : ℝ, 0 < K → ∀ s : ℝ, g K s ≤ K) ∧
      (∀ K : ℝ, 0 < K → GridChainData ν blk (g K) (μK K)) ∧
      Tendsto μK atTop (𝓝 μ)

/-- **`p:eq:timeergodic` for one nonnegative density, from the block data.**

The upper bound needs no boundedness; the lower bound is obtained for the truncations and
transported to `f` by `BracketTimeAverage.eventually_le_intervalAverage_mono`, then the
means of the truncations are let go to `μ`.  The squeeze is
`BracketTimeAverage.tendsto_intervalAverage`.

CONDITIONAL on `HasBlockData`; nothing here certifies `p:eq:gridprob`,
`p:lem:timeconverge`, `p:prop:timeergodic`, `p:thm:areaclt` or either main theorem. -/
theorem tendsto_intervalAverage_of_hasBlockData {ν : Measure G} [IsFiniteMeasure ν]
    {blk : G → ι → Set ℝ} {f : ℝ → ℝ} {μ : ℝ} (h : HasBlockData ν blk f μ) :
    Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, f s) / T) atTop (𝓝 μ) := by
  obtain ⟨hfull, g, μK, hgle, hgbdd, hgdata, hμK⟩ := h
  refine tendsto_intervalAverage
    (fun ε hε => intervalAverage_le_of_gridChainData hfull ε hε) ?_
  intro ε hε
  obtain ⟨K, hK, hKpos⟩ := (((tendsto_order.1 hμK).1 (μ - ε / 2) (by linarith)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hlowK : ∀ ε' : ℝ, 0 < ε' → ∀ᶠ T : ℝ in atTop,
      μK K - ε' ≤ (∫ s in (0 : ℝ)..T, g K s) / T :=
    fun ε' hε' =>
      le_intervalAverage_of_gridChainData (hgdata K hKpos) (hgbdd K hKpos) ε' hε'
  have hmono := eventually_le_intervalAverage_mono (hgle K hKpos) hfull.intervalIntegrable
    (hgdata K hKpos).intervalIntegrable hlowK
  filter_upwards [hmono (ε / 2) (by linarith)] with T hT
  linarith

/-! ### The directional averages of `BracketTimeAverage` -/

/-! ### `hLLN`, and `p:lem:bracketlimit` for the actual quenched array -/

open ReflectedWalk

end ReflectedGMS.GridBlockTransfer
