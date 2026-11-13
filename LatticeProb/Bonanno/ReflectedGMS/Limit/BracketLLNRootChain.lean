/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BracketLLNRootChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.RootBlockGridProbability
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TailAverageIdentification
import LatticeProb.Bonanno.ReflectedGMS.Limit.GridBlockTransfer

/-!
# The bracket law of large numbers along the root dyadic chain

`Limit/RootBlockGridProbability.lean` discharged the `grid` field of
`GridBlockTransfer.GridChainData` for the root dyadic time blocks
`rootTimeBlock D k = [o_k, o_k + σ_k)`, and `Limit/GridChainTailConstant.lean` produced the
`chain` field from the checked temporal block machinery plus the single identification input
`TailAverageIdentification.GridAveragedConstant`.  This module composes the two, and in doing
so records an obstruction in the existing composition.

## 1. An obstruction: the frozen negative-time density makes `hdata` unsatisfiable

The root blocks are **two-sided**: the origin sits at the uniform relative position
`u_k = -o_k/σ_k ∈ [0,1)` of its level-`k` block, so a fraction `u_k` of every root block lies at
negative times.  The canonical densities of
`RootBlockGridProbability.canonicalBracket_bracket_limit_of_rootBlockData` and
`GridBlockTransfer.canonicalBracket_bracket_limit_of_blockData` are read off the **one-sided**
path through `Real.toNNReal`, so at negative times they are frozen at the starting state.

* `eq_of_rootBlockDensity_of_frozen` — if a density is constant `c` on `(-∞,0]`, satisfies
  `RootBlockDensity ν f μ` for a uniform grid law, and has forward Cesàro limit `μ`, then
  `c = μ`.  Proof: with probability at least `(1/4)²` (a lower bound from the level-`k`
  cylinder law alone, uniformly in `k`) the origin sits in the window `u_k ∈ [1/2,3/4]` at
  infinitely many levels; at such a level the block average is `u_k c + (1-u_k)·(forward
  average)`, which stays `u_k|c-μ| ≥ |c-μ|/2` away from `μ`.
* `eq_of_hasRootBlockData_of_frozen` — the same for `HasRootBlockData`, which itself implies
  the forward Cesàro limit.
* `dirForm_bracketDensity_start_eq_of_rootBlockData` — **at the canonical data**: the `hdata`
  hypothesis of `canonicalBracket_bracket_limit_of_rootBlockData` forces
  `ξᵀ Γ(start) ξ = ξᵀ Σ ξ` in the three polarization directions, i.e. the bracket density of
  the *starting cell* already equals the limit.  Since the main theorem runs this over every
  start slot with `Σ = meanCovariance`, that `hdata` can only hold for environments with a
  constant bracket density; for a generic environment it is false.  Do not route through it.

## 2. The repair: extend the forward density by a backward trajectory

The transfer step only reads the density on `[0,T]`.  So the chain data may be supplied for
**any** extension of the forward density to negative times — in the manuscript, the backward
half of the two-sided trajectory (tex:1345, "its forward and time-reversed backward halves are
independent copies").

* `tendsto_intervalAverage_of_hasBlockData_of_eqOn` and the root-block form
  `tendsto_intervalAverage_of_hasRootBlockData_of_eqOn`.
* `canonicalBracket_bracket_limit_of_extendedRootBlockData` — `p:lem:bracketlimit` for the
  actual quenched array of `Φ(Y)` from `hdata` in the form *"almost surely there is an
  extension of the forward directional density with `HasRootBlockData`"*.
* `canonicalBracket_bracket_limit_of_twoSidedRootBlockData` — the same with the extension read
  off an independent backward sample `P ⊗ P'`, which is how the manuscript's two-sided law
  supplies it.

## 3. The chain field of the root blocks from `GridAveragedConstant`

`RootChainSystem` bundles the checked temporal block machinery's hypotheses for a system whose
complete ancestor chain is the actual root dyadic chain, and `UnmarkedRootDensity` the
unmarked functional and its density along the flow.

* `chain_rootTimeBlock_of_nat` — the `ℕ`-indexed conclusion of
  `GridChainTailConstant.ae_ae_chain_of_gridAveragedConstant` is the `ℤ`-indexed `chain` field
  of `RootBlockDensity` (negative levels are shorter than `1` and are excluded by the
  threshold).
* `ae_rootBlockDensity_of_gridAveragedConstant`,
  `ae_hasRootBlockData_of_gridAveragedConstant` (with the manuscript's truncations
  `F ∧ m`, `m : ℕ`, tex:1558) and `ae_tendsto_intervalAverage_of_gridAveragedConstant` —
  `p:prop:timeergodic` (forward half) for the root chain system, from `GridAveragedConstant`
  for `F` and its truncations.
* `ae_forall_dirVec_hasRootBlockData_of_gridAveragedConstant` — the three polarization
  directions at once, in the shape of the `hdata` of §2.

## What is *not* proved here

* `GridAveragedConstant` (`p:lem:regeninvariant` plus environment ergodicity).
* The construction of a `RootChainSystem` for the actual process: the annealed two-sided
  rooted law, the `κ`-selected block family on it, the root-chain selection, and the flow
  invariance `RootChainSystem.flowInvariant`.  That last field is inherited verbatim from the
  checked `ConditionalTemporalAveraging` (`hθP`) and is **stronger than the manuscript**, which
  only uses the degree `-2` temporal mass transport (tex:1360-1397) and therefore controls only
  scale-invariant tests.
* The annealed-to-quenched step of the manuscript (tex:1574, "Fubini gives the quenched
  almost-sure assertion") connecting §3 to the `hdata` of §2 at a fixed environment.

Nothing here certifies `p:lem:timeconverge`, `p:lem:regeninvariant`, `p:prop:timeergodic`,
`p:lem:bracketlimit`, `p:thm:areaclt` or either main theorem.
-/

-- Merged from `ReflectedGMS/Limit/GridChainTailConstant.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_GridChainTailConstant

/-!
# The `chain` field of `GridChainData`, from the tail-constant identification

`ReflectedGMS/Limit/GridBlockTransfer.lean` reduces the bracket law of large numbers for the
actual quenched array of `Φ(Y)` to the two probabilistic fields of
`ReflectedGMS.GridBlockTransfer.GridChainData`.  Its `chain` field reads, verbatim,

```
chain : ∀ᵐ Dg ∂ν, ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ k : ι,
  ENNReal.ofReal R ≤ volume (blk Dg k) → |setAvg (blk Dg k) f - μ| ≤ η
```

— for `ν`-almost every grid, every root block long enough has block average within `η` of the
constant `μ`.  Its author split it into two halves:

* the **convergence** half, which is the already checked
  `ConditionalTemporalAveraging.tendsto_setAverageReal_chain_ae`, read in length-indexed
  rather than chain-indexed form;
* the **identification** half, that the tail conditional expectation which that theorem
  produces as the limit is the constant `𝔼[F]` (in the application `𝔼[Γ]`).

This module carries out the first half and reduces the second to the single named input
`ReflectedGMS.TailAverageIdentification.GridAveragedConstant`, which is verbatim what
`p:lem:regeninvariant` together with environment ergodicity delivers in the manuscript
(tex:1526-1528).  The remaining measure-theoretic content of the identification —
the manuscript's steps `𝔼[Fψ(L)] = 𝔼[F]𝔼[ψ(L)]`, `𝔼[Fψ(L)] = 𝔼[Lψ(L)]` and the sign test —
is proved in `ReflectedGMS/Temporal/TailAverageIdentification.lean`.

## What is proved

* `ae_ae_forall_long_block` — the shape transfer.  A sequential limit along the ancestor
  chain, holding for `(P ⊗ ν)`-almost every (trajectory, grid) pair, becomes: for
  `P`-almost every trajectory, for `ν`-almost every grid, every block longer than a
  threshold has average within `η` of the limit.  This is the `chain` field's own shape,
  with `ι = ℕ`.
* `ae_ae_chain_of_gridAveragedConstant` — the full assembly: the `chain` field of
  `GridChainData`, for the density of one unmarked functional `F₀` along the flow, with
  `μ = 𝔼_P[F₀]`, from
  - the checked temporal block machinery (`TemporalBlockSystem`, its nesting, the flow
    invariance of the law, and the ancestor-chain selection data), and
  - the single named input `GridAveragedConstant`.

The quantifier `∀ᵐ ω ∂P` in front is the manuscript's quenched reading: the density `f` of
`GridChainData` is the bracket density along one fixed trajectory, and the grid is the only
remaining source of randomness.

## What is *not* proved

`GridAveragedConstant`.  In the manuscript it is `p:lem:regeninvariant` plus the
environment-ergodicity hypothesis; `p:lem:regeninvariant`'s own open inputs are reversal
invariance of the complete stopped return-cycle law, the size-biased entrance/age
decomposition of the cycle law, and the `v`-independence step.  None of that is touched
here, and nothing in this file certifies `p:lem:regeninvariant`, `p:prop:timeergodic`,
`p:lem:bracketlimit`, `p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace ReflectedGMS.GridChainTailConstant

open ReflectedGMS.BracketTimeAverage ReflectedGMS.ConditionalTemporalAveraging
open ReflectedGMS.TailAverageIdentification

/-! ### From a chain-indexed limit to the `chain` field's length-indexed form -/

/-- **The shape of the `chain` field, from a sequential limit along the ancestor chain.**

`b d n` is the `n`-th root block of the grid `d`; the lengths increase with `n` and are
finite.  If, for almost every (trajectory, grid) pair, the block averages converge along the
chain to the constant `μ`, then for almost every trajectory and almost every grid *every*
block longer than a threshold is within `η` of `μ`. -/
theorem ae_ae_forall_long_block {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure D} [IsProbabilityMeasure ν]
    {b : D → ℕ → Set ℝ} (hmono : ∀ d : D, Monotone fun n : ℕ => volume (b d n))
    (hfin : ∀ (d : D) (n : ℕ), volume (b d n) ≠ ⊤) {dens : Ω → ℝ → ℝ} {μ : ℝ}
    (hconv : ∀ᵐ p ∂(P.prod ν),
      Tendsto (fun n : ℕ => setAvg (b p.2 n) (dens p.1)) atTop (𝓝 μ)) :
    ∀ᵐ ω ∂P, ∀ᵐ d ∂ν, ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ n : ℕ,
      ENNReal.ofReal R ≤ volume (b d n) → |setAvg (b d n) (dens ω) - μ| ≤ η := by
  filter_upwards [Measure.ae_ae_of_ae_prod hconv] with ω hω
  filter_upwards [hω] with d hd
  intro η hη
  exact exists_threshold_of_tendsto (hmono d) (hfin d) hd hη

/-! ### The full assembly -/

end ReflectedGMS.GridChainTailConstant

end Merged_GridChainTailConstant

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.BracketLLNRootChain

open ReflectedGMS.DyadicApproximation
open ReflectedGMS.MartingaleIngredients ReflectedGMS.MartingaleLimit
open ReflectedGMS.BracketTimeAverage ReflectedGMS.GridBlockTransfer
open ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.ConditionalTemporalAveraging ReflectedGMS.TailAverageIdentification
open ReflectedGMS.GridChainTailConstant

/-! ### 1. The frozen extension to negative times -/

/-- The relative position `-o_k / σ_k ∈ [0,1)` of the time origin inside its level-`k` root
block `[o_k, o_k + σ_k)`. -/
noncomputable def rootPosition (D : Grid) (k : ℤ) : ℝ := -D.origin k 0 / side D k

theorem rootPosition_mul_side (D : Grid) (k : ℤ) :
    rootPosition D k * side D k = -D.origin k 0 :=
  div_mul_cancel₀ _ (side_pos D k).ne'

/-! ### 2. The repair: an arbitrary extension to negative times -/

/-- **The transfer step reads the density only on `[0, T]`.**  Block data for any `g` agreeing
with `f` on `[0, ∞)` gives the forward Cesàro limit of `f`. -/
theorem tendsto_intervalAverage_of_hasBlockData_of_eqOn {G ι : Type*} [MeasurableSpace G]
    {ν : Measure G} [IsFiniteMeasure ν] {blk : G → ι → Set ℝ} {f g : ℝ → ℝ} {μ : ℝ}
    (hfg : ∀ s : ℝ, 0 ≤ s → g s = f s) (h : HasBlockData ν blk g μ) :
    Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, f s) / T) atTop (𝓝 μ) := by
  refine (tendsto_intervalAverage_of_hasBlockData h).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have heq : (∫ s in (0 : ℝ)..T, g s) = ∫ s in (0 : ℝ)..T, f s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT] at hs
    exact hfg s (Set.mem_Icc.1 hs).1
  show (∫ s in (0 : ℝ)..T, g s) / T = (∫ s in (0 : ℝ)..T, f s) / T
  rw [heq]

/-- The root-block form of `tendsto_intervalAverage_of_hasBlockData_of_eqOn`. -/
theorem tendsto_intervalAverage_of_hasRootBlockData_of_eqOn {ν : Measure Grid}
    (hlaw : UniformGridLaw ν) {f g : ℝ → ℝ} {μ : ℝ} (hfg : ∀ s : ℝ, 0 ≤ s → g s = f s)
    (h : HasRootBlockData ν g μ) :
    Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, f s) / T) atTop (𝓝 μ) := by
  have : IsProbabilityMeasure ν := hlaw.1
  exact tendsto_intervalAverage_of_hasBlockData_of_eqOn hfg
    (hasBlockData_of_hasRootBlockData hlaw h)

/-! ### 3. The chain field of the root blocks from `GridAveragedConstant` -/

/-- **The `ℤ`-indexed `chain` field from its `ℕ`-indexed form.**  Blocks at negative levels have
length `2^{φ+k} < 1`, so a threshold at least `1` excludes them. -/
theorem chain_rootTimeBlock_of_nat {f : ℝ → ℝ} {μ : ℝ} {D : Grid}
    (h : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ n : ℕ,
      ENNReal.ofReal R ≤ volume (rootTimeBlock D (n : ℤ)) →
        |setAvg (rootTimeBlock D (n : ℤ)) f - μ| ≤ η) :
    ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ k : ℤ,
      ENNReal.ofReal R ≤ volume (rootTimeBlock D k) → |setAvg (rootTimeBlock D k) f - μ| ≤ η := by
  intro η hη
  obtain ⟨R, hR⟩ := h η hη
  refine ⟨max R 1, fun k hk => ?_⟩
  rcases le_or_gt 0 k with hk0 | hk0
  · -- CONDITIONAL on `0 ≤ k`: a member of the `ℕ`-indexed chain
    lift k to ℕ using hk0 with n
    exact hR n (le_trans (ENNReal.ofReal_le_ofReal (le_max_left R 1)) hk)
  · -- CONDITIONAL on `k < 0`: the block is shorter than the threshold
    exfalso
    have hlt : side D k < 1 := by
      have hside : side D k = (2 : ℝ) ^ (D.phase + (k : ℝ)) := rfl
      have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      have hφ : D.phase < 1 := (Set.mem_Ico.1 D.phase_mem).2
      rw [hside]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    rw [volume_rootTimeBlock] at hk
    have h1 : max R 1 ≤ side D k := (ENNReal.ofReal_le_ofReal_iff (side_pos D k).le).1 hk
    have h2 := le_max_right R 1
    linarith

/-- The root block lengths increase with the level. -/
theorem monotone_volume_rootTimeBlock (D : Grid) :
    Monotone fun n : ℕ => volume (rootTimeBlock D (n : ℤ)) := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [volume_rootTimeBlock]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  rw [ReflectedGMS.DyadicGridTranslation.side_succ]
  linarith [side_pos D (n : ℤ)]

/-- Local integrability on the time axis gives interval integrability. -/
theorem intervalIntegrable_of_locallyIntegrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set
    Set.uIoc_subset_uIcc)

/-- Local integrability on the time axis gives integrability on every root block. -/
theorem integrableOn_rootTimeBlock_of_locallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (D : Grid) (k : ℤ) :
    IntegrableOn f (rootTimeBlock D k) volume := by
  rw [rootTimeBlock_eq]
  exact (hf.integrableOn_isCompact isCompact_Icc).mono_set Set.Ico_subset_Icc_self

/-- **An unmarked nonnegative integrable functional and its density along the flow.**
`unmarked` says that the density does not depend on the grid.  Nothing is asserted. -/
structure UnmarkedRootDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θ : ℝ → Ω × Grid → Ω × Grid) (F : Ω → ℝ) (dens : Ω → ℝ → ℝ) : Prop where
  /-- The functional is measurable. -/
  measurable : Measurable F
  /-- The functional is integrable. -/
  integrable : Integrable F P
  /-- The functional is nonnegative, as in the transfer step. -/
  nonneg : ∀ ω : Ω, 0 ≤ F ω
  /-- Flowing and reading `F` off the trajectory coordinate is the density. -/
  unmarked : ∀ (t : ℝ) (ω : Ω) (d : Grid), F (θ t (ω, d)).1 = dens ω t
  /-- The density is locally integrable on the whole time axis (`p:lem:timeconverge`). -/
  locallyIntegrable : ∀ᵐ ω ∂P, LocallyIntegrable (dens ω) volume

end ReflectedGMS.BracketLLNRootChain
