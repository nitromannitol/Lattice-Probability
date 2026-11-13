/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.MarkovProperty at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.CTRW
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Property (iv) of Theorem 1.6: the Markov property of the constructed process
(Gwynne–Sung, arXiv:2506.18827, Section 3.4, p. 25)

This file discharges the last hypothesis of the existence half of Theorem 1.6: property (iv),
the Markov property (3.15) of the process `X` of (3.26) under the paper's `P_z`.  The paper's
two-line argument is

> each `Xⁿ` is a continuous time random walk, so the Markov property of continuous time random
> walk implies that … on the event `{Xⁿ_t = x}`, the `P_z`-conditional law of `{Xⁿ_{s+t}}_{s≥0}`
> given `{Xⁿ_s}_{s≤t}` is the same as the `P_x`-law of `{Xⁿ_s}_{s≥0}`.  Since `Xⁿ_t → X_t` … we
> can take the limit as `n → ∞`.

and this file is exactly those two steps.

## Step 1: `Xⁿ` is a continuous time random walk (`markovProperty_levelProcess`)

`CTRW.lean` proves the Markov property for the *generic* continuous-time random walk of (3.15)
with skeleton kernel `κ` and rate `w` (`CTRW.markovProperty`), on its own sample space
`(ℕ → V) × (ℕ → ℝ)` carrying `MarkovChain.chainLaw κ z ⊗ unitTimes`.  Two bridges identify
this with `Xⁿ` on the sample space of Section 3.3:

* `Theorem16.markovProperty_map_iff` — **`MarkovProperty` only depends on the law of the
  trajectory.**  All three ingredients of property (iv) (the event `{X_t = x}`, the past
  `{X_s}_{s≤t}` and the future `{X_{s+t}}_{s≥0}`) are functions of the trajectory
  `t ↦ X_t`, so property (iv) for `(P, X)` is property (iv) for the canonical process
  `γ ↦ γ t` under the law `P.map (t ↦ X_t)`.  This is the transfer principle that lets a
  Markov property be moved between sample spaces carrying the same path law.
* `ContinuousTimeChain.map_trajOf_levelProcess` — **the path law of `Xⁿ` is the path law of the
  generic walk** with the level-`(n₀+i)` skeleton kernel `E.stepKernel hG (n₀+i)`.  This is
  `ContinuousTimeChain.map_trajectoryN` (`Xⁿ = jumpPath (Yⁿ, Tⁿ)` together with
  `map_embeddedPair`) combined with `CTRW.trajLaw_eq_map_compProd`, which rewrites the
  `CTRW.lean` walk as the same time change `jumpPath` of the same joint law
  `chainLaw ⊗ₘ holdingKernel w` (`CTRW.ctrw_eq_jumpPath`, `prod_expSeq_map_divPair`).

## Step 2: the limit `n → ∞` (`Theorem16.markovProperty_of_tendsto`)

Mathlib has no convergence theorem for conditional laws, so the limit is taken by hand.  Both
sides of property (iv) are finite measures on
`(Set.Iic t → VG ∪ {∞}) × Trajectory V`, a product of two *cylinder* σ-algebras, so it suffices
to compare them on rectangles `A ×ˢ B` of measurable cylinders
(`ext_of_generate_finite`, `MeasurableSpace.generateFrom_eq_prod`).  On such a rectangle both
sides are measures of events depending on **finitely many times**, so the pointwise clause of
Lemma 3.8 — a.s. `Xⁿ_u = X_u` for all large `n`, for each fixed `u`
(`PathProperties.ae_eventually_processN_eq`) — makes the corresponding indicators agree
eventually, and dominated convergence (`tendsto_measure_of_ae_tendsto_indicator`) gives the
convergence of each side.  The `P_x`-law factor converges for the same reason
(`Existence.tendsto_trajLaw_cylinder`); the level of the comparison walk is `n_z + i`, which
exceeds `n_x` for large `i`, so the walk `Xⁿ` started at `x` is the one carried by
`Existence.sampleLaw E hG x`.

## What is closed

`Existence.markovProperty` is property (iv) for the constructed process, and
`markovProperty_hiv` is the `hiv` hypothesis of `Existence.existence_half` verbatim.
`existence_half` is then unconditional (`existence_half'`), which is what the capstone
`theorem16` consumes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk

open IndexSet

/-! ### 1.  `MarkovProperty` is a property of the law of the trajectory -/

namespace Theorem16

variable {V : Type u}

/-- The canonical process on the path space: `X_t(γ) = γ t`. -/
def evalPath (t : ℝ≥0) (γ : Trajectory V) : Option V := γ t

/-- The trajectory map `ω ↦ {X_t(ω)}_{t ≥ 0}` of a process. -/
def trajOf {Ω : Type*} (X : ℝ≥0 → Ω → Option V) (ω : Ω) : Trajectory V := fun t => X t ω

lemma measurable_evalPath (t : ℝ≥0) : Measurable (evalPath (V := V) t) := measurable_pi_apply t

lemma measurable_trajOf {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V}
    (hX : ∀ t, Measurable (X t)) : Measurable (trajOf X) :=
  measurable_pi_iff.mpr hX

lemma measurable_pastPath {Ω : Type u} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V}
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) : Measurable (pastPath X t) :=
  measurable_pi_iff.mpr fun _ => hX _

lemma measurable_shiftedPath {Ω : Type u} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V}
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) : Measurable (shiftedPath X t) :=
  measurable_pi_iff.mpr fun _ => hX _

/-- Restricting the law of the trajectory to `{γ_t = x}` and pushing forward by a function of
the path is the same as restricting `P` to `{X_t = x}` and pushing forward by the corresponding
function of the outcome. -/
private lemma restrict_map_trajOf {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (x : V)
    {β : Type*} [MeasurableSpace β] {g : Trajectory V → β} (hg : Measurable g) :
    ((P.map (trajOf X)).restrict {γ : Trajectory V | evalPath t γ = some x}).map g =
      (P.restrict {ω | X t ω = some x}).map (fun ω => g (trajOf X ω)) := by
  have htr : Measurable (trajOf X) := measurable_trajOf hX
  have hB : MeasurableSet {γ : Trajectory V | evalPath t γ = some x} :=
    (measurable_evalPath t) (measurableSet_singleton (some x))
  rw [Measure.restrict_map htr hB, Measure.map_map hg htr]
  rfl

/-- **Property (iv) is a property of the law of the trajectory.**  The event `{X_t = x}`, the
past `{X_s}_{s ≤ t}` and the future `{X_{s+t}}_{s ≥ 0}` are all functions of the trajectory
`t ↦ X_t`, so the Markov property for the process `X` under `P` is the Markov property for the
canonical process `γ ↦ γ t` under the law of the trajectory.  This is what lets
`CTRW.markovProperty`, proved on the sample space of `CTRW.lean`, be read on the sample space
of Section 3.3. -/
theorem markovProperty_map_iff {Ω : Type u} [MeasurableSpace Ω] (μ : V → Measure (Trajectory V))
    (P : Measure Ω) {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) :
    MarkovProperty μ (P.map (trajOf X)) evalPath ↔ MarkovProperty μ P X := by
  refine forall_congr' fun t => forall_congr' fun x => ?_
  rw [restrict_map_trajOf P hX t x
      ((measurable_pastPath (fun s => measurable_evalPath (V := V) s) t).prodMk
        (measurable_shiftedPath (fun s => measurable_evalPath (V := V) s) t)),
    restrict_map_trajOf P hX t x
      (measurable_pastPath (fun s => measurable_evalPath (V := V) s) t)]
  exact Iff.rfl

end Theorem16

/-! ### 2.  The generic walk of `CTRW.lean` is the time change of `ContinuousTimeChain.lean`

`CTRW.lean` builds the walk (3.15) from the skeleton `Y` and the **unit** holding times `e`,
with clock `S_k = ∑_{i<k} e_i / w(Y_i)`; `ContinuousTimeChain.lean` builds it from the skeleton
and the **rescaled** holding times `T_j = e_j / w(Y_j)`, with clock `∑_{j<k} T_j`.  The two are
the same function, and rescaling turns the i.i.d. `Exponential(1)` sequence `unitTimes = expSeq`
into `holdingKernel w`; so the path law of the `CTRW.lean` walk is the pushforward of
`chainLaw ⊗ₘ holdingKernel w` under `jumpPath`, which is the law
`ContinuousTimeChain.map_trajectoryN` computes for `Xⁿ`. -/

section Bridge

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- `holdingKernel w y` is the i.i.d. `Exponential(1)` sequence rescaled by `w ∘ y`. -/
lemma holdingKernel_eq_map (w : V → ℝ) (y : ℕ → V) :
    holdingKernel w y = expSeq.map (fun e : ℕ → ℝ => fun j => e j / w (y j)) := by
  rw [holdingKernel, Kernel.map_apply _ (measurable_divSeq w), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_divSeq w) measurable_prodMk_left]
  rfl

/-- **Rescaling the unit holding times.**  The law of `(Y, (e_j/w(Y_j))_j)` for `Y ~ μ`
independent of an i.i.d. `Exponential(1)` sequence `e` is `μ ⊗ₘ holdingKernel w`: the
conditional law of the rescaled holding times given the skeleton. -/
lemma prod_expSeq_map_divPair (w : V → ℝ) (μ : Measure (ℕ → V)) [IsProbabilityMeasure μ] :
    (μ.prod expSeq).map
        (fun p : (ℕ → V) × (ℕ → ℝ) => ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ))) =
      μ ⊗ₘ holdingKernel w := by
  have hm : Measurable
      (fun p : (ℕ → V) × (ℕ → ℝ) => ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ))) :=
    measurable_fst.prodMk (measurable_divSeq w)
  have : IsFiniteMeasure ((μ.prod expSeq).map
      (fun p : (ℕ → V) × (ℕ → ℝ) =>
        ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ)))) :=
    Measure.isFiniteMeasure_map _ _
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply hm (hA.prod hB), Measure.prod_apply (hm (hA.prod hB))]
  have hslice : ∀ y : ℕ → V,
      expSeq (Prod.mk y ⁻¹' ((fun p : (ℕ → V) × (ℕ → ℝ) =>
          ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ))) ⁻¹' (A ×ˢ B))) =
        A.indicator (fun y => holdingKernel w y B) y := by
    intro y
    by_cases hy : y ∈ A
    · have hset : Prod.mk y ⁻¹' ((fun p : (ℕ → V) × (ℕ → ℝ) =>
          ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ))) ⁻¹' (A ×ˢ B)) =
            (fun e : ℕ → ℝ => fun j => e j / w (y j)) ⁻¹' B := by
        ext e
        exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
      rw [Set.indicator_of_mem hy, hset, holdingKernel_eq_map w y,
        Measure.map_apply (Measurable.of_eval fun j => (measurable_pi_apply j).div_const _) hB]
    · have hset : Prod.mk y ⁻¹' ((fun p : (ℕ → V) × (ℕ → ℝ) =>
          ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ))) ⁻¹' (A ×ˢ B)) = ∅ := by
        ext e
        exact ⟨fun h => absurd h.1 hy, fun h => h.elim⟩
      rw [Set.indicator_of_notMem hy, hset, measure_empty]
  simp_rw [hslice]
  rw [lintegral_indicator hA, Measure.compProd_apply_prod hA hB]

end Bridge

namespace CTRW

variable {V : Type u} (w : V → ℝ)

/-- **The walk (3.15) of `CTRW.lean` is the time change `jumpPath`** of
`ContinuousTimeChain.lean`, applied to the rescaled holding times `T_j = e_j / w(Y_j)`: the two
clocks `∑_{i<k} e_i/w(Y_i)` and `∑_{j<k} T_j` are the same. -/
lemma ctrw_eq_jumpPath (Y : ℕ → V) (e : ℕ → ℝ) (t : ℝ≥0) :
    ctrw w Y e t =
      ContinuousTimeChain.jumpPath ((Y, fun j => e j / w (Y j)) : (ℕ → V) × (ℕ → ℝ)) t := by
  have hin : ∀ k, InHold w Y e k t ↔ ContinuousTimeChain.InJump
      ((Y, fun j => e j / w (Y j)) : (ℕ → V) × (ℕ → ℝ)).2 k (t : ℝ≥0∞) := fun _ => Iff.rfl
  by_cases hx : ∃ k, InHold w Y e k t
  · obtain ⟨k, hk⟩ := hx
    rw [ctrw_eq_of_inHold w Y e hk, ContinuousTimeChain.jumpPath_eq_of_inJump ((hin k).mp hk)]
  · rw [(ctrw_eq_none_iff w Y e t).mpr hx,
      (ContinuousTimeChain.jumpPath_eq_none_iff _ t).mpr
        (fun h => hx ⟨h.choose, (hin h.choose).mpr h.choose_spec⟩)]

/-- The trajectory of the `CTRW.lean` walk is the time change of the pair (skeleton, rescaled
holding times). -/
lemma traj_eq_jumpPath (p : (ℕ → V) × (ℕ → ℝ)) :
    traj w p = fun t => ContinuousTimeChain.jumpPath
      ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ)) t :=
  funext fun t => ctrw_eq_jumpPath w p.1 p.2 t

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- **The path law of the generic walk (3.15)** of `CTRW.lean`: the pushforward, under the time
change `jumpPath`, of the joint law `chainLaw κ z ⊗ₘ holdingKernel w` of the skeleton and its
holding times.  This is the law `ContinuousTimeChain.map_trajectoryN` computes for `Xⁿ`. -/
theorem trajLaw_eq_map_compProd (κ : Kernel V V) [IsMarkovKernel κ] (z : V) :
    trajLaw w κ z =
      (MarkovChain.chainLaw κ z ⊗ₘ holdingKernel w).map
        (fun p => (fun t => ContinuousTimeChain.jumpPath p t : Trajectory V)) := by
  have hm : Measurable
      (fun p : (ℕ → V) × (ℕ → ℝ) => ((p.1, fun j => p.2 j / w (p.1 j)) : (ℕ → V) × (ℕ → ℝ))) :=
    measurable_fst.prodMk (measurable_divSeq w)
  have hL : trajLaw w κ z = ((MarkovChain.chainLaw κ z).prod expSeq).map (traj w) := rfl
  rw [hL, ← prod_expSeq_map_divPair w (MarkovChain.chainLaw κ z),
    Measure.map_map ContinuousTimeChain.measurable_jumpTrajectory hm]
  congr 1

end CTRW

/-! ### 3.  Property (iv) for `Xⁿ` -/

namespace ContinuousTimeChain

open Existence PathProperties

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  {G : ConductanceGraph V} (E : G.Exhaustion) (w : V → ℝ)

/-- `Xⁿ` of (3.15) at level offset `i` above the base level `n₀`, as a process on the sample
space of Section 3.3 (`PathProperties.processN` with the two projections). -/
noncomputable def levelProcess (n₀ i : ℕ) (t : ℝ≥0) (ω : Sample V) : Option V :=
  PathProperties.Xn (E.levelSets n₀) ω.1 w ω.2 i t

lemma measurable_levelProcess (n₀ i : ℕ) (t : ℝ≥0) : Measurable (levelProcess E w n₀ i t) :=
  measurable_Xn_sample w (E.levelSets n₀) i t

variable [Nontrivial V] (hG : G.toSimpleGraph.Connected)

/-- **The path law of `Xⁿ`** is the path law of the generic continuous-time random walk (3.15)
of `CTRW.lean` with the level-`(n₀+i)` skeleton kernel: `map_trajectoryN` read through
`CTRW.trajLaw_eq_map_compProd`. -/
theorem map_trajOf_levelProcess (hw : ∀ x, 0 < w x) (n₀ : ℕ) (z : V) (i : ℕ) :
    (E.jointLaw hG n₀ z).map (Theorem16.trajOf (levelProcess E w n₀ i)) =
      CTRW.trajLaw w (E.stepKernel hG (n₀ + i)) z := by
  rw [CTRW.trajLaw_eq_map_compProd]
  exact map_trajectoryN E w hG hw n₀ z i

/-- **Property (iv) for `Xⁿ`** (p. 25, "each `Xⁿ` is a continuous time random walk, so the
Markov property of continuous time random walk implies …"): `CTRW.markovProperty` transferred
to the sample space of Section 3.3 along the identification of the path laws.  The family of
comparison laws is the family of level-`(n₀+i)` walks, one for each starting point. -/
theorem markovProperty_levelProcess (hw : ∀ x, 0 < w x) (n₀ : ℕ) (z : V) (i : ℕ) :
    Theorem16.MarkovProperty (fun x => CTRW.trajLaw w (E.stepKernel hG (n₀ + i)) x)
      (E.jointLaw hG n₀ z) (levelProcess E w n₀ i) := by
  have h1 : Theorem16.MarkovProperty (fun x => CTRW.trajLaw w (E.stepKernel hG (n₀ + i)) x)
      (CTRW.trajLaw w (E.stepKernel hG (n₀ + i)) z) Theorem16.evalPath :=
    (Theorem16.markovProperty_map_iff _ _ (CTRW.measurable_proc w)).mpr
      (CTRW.markovProperty w (E.stepKernel hG (n₀ + i)) hw z)
  rw [← map_trajOf_levelProcess E w hG hw n₀ z i] at h1
  exact (Theorem16.markovProperty_map_iff _ _ (measurable_levelProcess E w n₀ i)).mp h1

end ContinuousTimeChain

/-! ### 4.  Passing property (iv) to the limit -/

namespace Theorem16

variable {V : Type u}

/-- From a.s. eventual agreement at each fixed time to a.s. eventual agreement at finitely many
times simultaneously. -/
lemma ae_eventually_restrict_eq {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {Xn : ℕ → ℝ≥0 → Ω → Option V} {X : ℝ≥0 → Ω → Option V}
    (hconv : ∀ u : ℝ≥0, ∀ᵐ ω ∂P, ∀ᶠ i in atTop, Xn i u ω = X u ω)
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ᶠ i in atTop, ∀ k ∈ s, Xn i (f k) ω = X (f k) ω := by
  have h1 : ∀ᵐ ω ∂P, ∀ k ∈ s, ∀ᶠ i in atTop, Xn i (f k) ω = X (f k) ω :=
    (Filter.eventually_all_finset _).2 fun k _ => hconv (f k)
  filter_upwards [h1] with ω hω
  exact (Filter.eventually_all_finset _).2 hω

/-- The left-hand side of property (iv), evaluated on a rectangle. -/
lemma map_pair_prod_apply {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (x : V)
    {A : Set (Set.Iic t → Option V)} {B : Set (Trajectory V)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ((P.restrict {ω | X t ω = some x}).map
        (fun ω => (pastPath X t ω, shiftedPath X t ω))) (A ×ˢ B) =
      P (pastPath X t ⁻¹' A ∩ shiftedPath X t ⁻¹' B ∩ {ω | X t ω = some x}) := by
  have hpair := (measurable_pastPath hX t).prodMk (measurable_shiftedPath hX t)
  rw [Measure.map_apply hpair (hA.prod hB), Measure.restrict_apply (hpair (hA.prod hB)),
    Set.mk_preimage_prod]

/-- The right-hand side of property (iv), evaluated on a rectangle. -/
lemma map_past_prod_apply {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (x : V)
    (ν : Measure (Trajectory V)) [IsFiniteMeasure ν]
    {A : Set (Set.Iic t → Option V)} {B : Set (Trajectory V)} (hA : MeasurableSet A)
    (_hB : MeasurableSet B) :
    (((P.restrict {ω | X t ω = some x}).map (pastPath X t)).prod ν) (A ×ˢ B) =
      P (pastPath X t ⁻¹' A ∩ {ω | X t ω = some x}) * ν B := by
  have hpast := measurable_pastPath hX t
  have : IsFiniteMeasure ((P.restrict {ω | X t ω = some x}).map (pastPath X t)) :=
    Measure.isFiniteMeasure_map _ _
  rw [Measure.prod_prod, Measure.map_apply hpast hA, Measure.restrict_apply (hpast hA)]

/-- **Property (iv) passes to the limit** (p. 25, "Since `Xⁿ_t → X_t` … we can take the limit as
`n → ∞`").  If each `Xⁿ` has the Markov property with comparison laws `μⁿ`, if for each fixed
time `Xⁿ_u = X_u` almost surely for all large `n`, and if `μⁿ x → μ x` on cylinder sets, then
`X` has the Markov property with comparison laws `μ`.

Both sides of property (iv) are finite measures on a product of two cylinder σ-algebras, so
they agree as soon as they agree on rectangles of measurable cylinders; a rectangle of cylinders
is an event depending on finitely many times, where the hypotheses give convergence by dominated
convergence. -/
theorem markovProperty_of_tendsto {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {μ : V → Measure (Trajectory V)}
    {Xn : ℕ → ℝ≥0 → Ω → Option V} {X : ℝ≥0 → Ω → Option V}
    {μn : ℕ → V → Measure (Trajectory V)}
    (hμfin : ∀ x, IsFiniteMeasure (μ x)) (hμnfin : ∀ i x, IsFiniteMeasure (μn i x))
    (hXn : ∀ i t, Measurable (Xn i t)) (hX : ∀ t, Measurable (X t))
    (hconv : ∀ u : ℝ≥0, ∀ᵐ ω ∂P, ∀ᶠ i in atTop, Xn i u ω = X u ω)
    (hμ : ∀ (x : V) (B : Set (Trajectory V)),
      B ∈ measurableCylinders (fun _ : ℝ≥0 => Option V) →
      Tendsto (fun i => μn i x B) atTop (𝓝 (μ x B)))
    (hmp : ∀ i, MarkovProperty (μn i) P (Xn i)) :
    MarkovProperty μ P X := by
  intro t x
  have := hμfin x
  have hpast := measurable_pastPath hX t
  have hfut := measurable_shiftedPath hX t
  have hpastn : ∀ i, Measurable (pastPath (Xn i) t) := fun i => measurable_pastPath (hXn i) t
  have hfutn : ∀ i, Measurable (shiftedPath (Xn i) t) := fun i => measurable_shiftedPath (hXn i) t
  have hSm : MeasurableSet {ω | X t ω = some x} := (hX t) (measurableSet_singleton _)
  have hSnm : ∀ i, MeasurableSet {ω | Xn i t ω = some x} :=
    fun i => (hXn i t) (measurableSet_singleton _)
  have : IsFiniteMeasure ((P.restrict {ω | X t ω = some x}).map
      (fun ω => (pastPath X t ω, shiftedPath X t ω))) := Measure.isFiniteMeasure_map _ _
  -- the rectangle identity
  have hrect : ∀ A ∈ measurableCylinders (fun _ : Set.Iic t => Option V),
      ∀ B ∈ measurableCylinders (fun _ : ℝ≥0 => Option V),
      ((P.restrict {ω | X t ω = some x}).map
          (fun ω => (pastPath X t ω, shiftedPath X t ω))) (A ×ˢ B) =
        (((P.restrict {ω | X t ω = some x}).map (pastPath X t)).prod (μ x)) (A ×ˢ B) := by
    intro A hA B hB
    have hAm : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
    have hBm : MeasurableSet B := MeasurableSet.of_mem_measurableCylinders hB
    obtain ⟨s₁, S₁, hS₁, rfl⟩ := (mem_measurableCylinders A).mp hA
    obtain ⟨s₂, S₂, hS₂, rfl⟩ := (mem_measurableCylinders B).mp hB
    rw [map_pair_prod_apply P hX t x hAm hBm, map_past_prod_apply P hX t x (μ x) hAm hBm]
    -- the same identity for each `Xⁿ`
    have hi : ∀ i, P (pastPath (Xn i) t ⁻¹' cylinder s₁ S₁ ∩
          shiftedPath (Xn i) t ⁻¹' cylinder s₂ S₂ ∩ {ω | Xn i t ω = some x}) =
        P (pastPath (Xn i) t ⁻¹' cylinder s₁ S₁ ∩ {ω | Xn i t ω = some x}) *
          μn i x (cylinder s₂ S₂) := by
      intro i
      have := hμnfin i x
      rw [← map_pair_prod_apply P (hXn i) t x hAm hBm,
        ← map_past_prod_apply P (hXn i) t x (μn i x) hAm hBm, hmp i t x]
    -- convergence of the joint side
    have hconv1 : Tendsto (fun i => P (pastPath (Xn i) t ⁻¹' cylinder s₁ S₁ ∩
          shiftedPath (Xn i) t ⁻¹' cylinder s₂ S₂ ∩ {ω | Xn i t ω = some x})) atTop
        (𝓝 (P (pastPath X t ⁻¹' cylinder s₁ S₁ ∩ shiftedPath X t ⁻¹' cylinder s₂ S₂ ∩
          {ω | X t ω = some x}))) := by
      refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (((hpast hAm).inter (hfut hBm)).inter hSm)
        (fun i => ((hpastn i hAm).inter (hfutn i hBm)).inter (hSnm i)) ?_
      filter_upwards [ae_eventually_restrict_eq hconv s₁ (fun k : Set.Iic t => (k : ℝ≥0)),
        ae_eventually_restrict_eq hconv s₂ (fun u : ℝ≥0 => u + t), hconv t] with ω g1 g2 g3
      filter_upwards [g1, g2, g3] with i e1 e2 e3
      have p1 : Finset.restrict s₁ (pastPath (Xn i) t ω) = Finset.restrict s₁ (pastPath X t ω) :=
        funext fun k => e1 k.1 k.2
      have p2 : Finset.restrict s₂ (shiftedPath (Xn i) t ω) =
          Finset.restrict s₂ (shiftedPath X t ω) := funext fun k => e2 k.1 k.2
      simp only [Set.mem_inter_iff, Set.mem_preimage, mem_cylinder, Set.mem_ofPred_eq, p1, p2, e3]
    -- convergence of the marginal side
    have hconv2 : Tendsto (fun i => P (pastPath (Xn i) t ⁻¹' cylinder s₁ S₁ ∩
          {ω | Xn i t ω = some x})) atTop
        (𝓝 (P (pastPath X t ⁻¹' cylinder s₁ S₁ ∩ {ω | X t ω = some x}))) := by
      refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        ((hpast hAm).inter hSm) (fun i => (hpastn i hAm).inter (hSnm i)) ?_
      filter_upwards [ae_eventually_restrict_eq hconv s₁ (fun k : Set.Iic t => (k : ℝ≥0)),
        hconv t] with ω g1 g3
      filter_upwards [g1, g3] with i e1 e3
      have p1 : Finset.restrict s₁ (pastPath (Xn i) t ω) = Finset.restrict s₁ (pastPath X t ω) :=
        funext fun k => e1 k.1 k.2
      simp only [Set.mem_inter_iff, Set.mem_preimage, mem_cylinder, Set.mem_ofPred_eq, p1, e3]
    refine tendsto_nhds_unique hconv1 ?_
    simp only [hi]
    exact ENNReal.Tendsto.mul hconv2 (Or.inr (measure_ne_top _ _))
      (hμ x (cylinder s₂ S₂) hB)
      (Or.inr (measure_ne_top _ _))
  refine ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) (measurableCylinders fun _ : Set.Iic t => Option V)
      (measurableCylinders fun _ : ℝ≥0 => Option V))
    (generateFrom_eq_prod generateFrom_measurableCylinders
      generateFrom_measurableCylinders
      ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩
      ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩).symm
    (isPiSystem_measurableCylinders.prod isPiSystem_measurableCylinders) ?_ ?_
  · rintro - ⟨A, hA, B, hB, rfl⟩
    exact hrect A hA B hB
  · have h := hrect Set.univ (univ_mem_measurableCylinders _) Set.univ
      (univ_mem_measurableCylinders _)
    rwa [Set.univ_prod_univ] at h

end Theorem16

/-! ### 5.  Property (iv) for the constructed process -/

namespace Existence

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} (E : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
  (w : V → ℝ)

/-- **Lemma 3.8, pointwise clause, under the paper's `P_z`** (3.28): for each fixed time `u`,
almost surely `Xⁿ_u = X_u` for all large `n`.  This is
`PathProperties.ae_eventually_processN_eq`, with the hypotheses of Lemma 3.7 discharged as in
`Existence.almostEverywhereDefined`. -/
theorem ae_eventually_levelProcess_eq (hw : ∀ x, 0 < w x) (z : V)
    (hsum : ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂sampleLaw E hG z, ∀ᶠ i in atTop,
      ContinuousTimeChain.levelProcess E w (E.nz z) i u ω = process E w u ω := by
  filter_upwards [PathProperties.ae_eventually_processN_eq (sampleLaw E hG z)
      (E.levelSets (E.nz z)) w measurable_fst measurable_snd (E.levelSets_mono _)
      (E.exists_mem_levelSets _) hw (sampleLaw_ae_consistent E hG z) hsum
      (sampleLaw_indepFun_E0_rest E hG z) (sampleLaw_E0_absolutelyContinuous E hG z) u,
    ae_process_eq E hG w z] with ω h1 h2
  filter_upwards [h1] with i hi
  rw [h2 u]
  exact hi

/-- **The law of `Xⁿ` converges to the law of `X` on cylinder sets.**  For a starting point `x`
the level-`m` walk is carried by `Existence.sampleLaw E hG x` as soon as `m ≥ n_x`, and a
cylinder event depends on finitely many times, where `ae_eventually_levelProcess_eq` applies. -/
theorem tendsto_trajLaw_cylinder (hw : ∀ x, 0 < w x)
    (hsum : ∀ z, ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2)
    (x : V) {B : Set (Trajectory V)}
    (hB : B ∈ measurableCylinders fun _ : ℝ≥0 => Option V) :
    Tendsto (fun m : ℕ => CTRW.trajLaw w (E.stepKernel hG m) x B) atTop
      (𝓝 (((sampleLaw E hG x).map (Theorem16.trajOf (process E w))) B)) := by
  have hBm : MeasurableSet B := MeasurableSet.of_mem_measurableCylinders hB
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders B).mp hB
  have hXm : ∀ t, Measurable (process E w t) := measurable_process E w
  have hXnm : ∀ (i : ℕ) (t : ℝ≥0),
      Measurable (ContinuousTimeChain.levelProcess E w (E.nz x) i t) :=
    fun i t => ContinuousTimeChain.measurable_levelProcess E w (E.nz x) i t
  -- convergence of the finite-dimensional events, at the base level `n_x`
  have key : Tendsto (fun j : ℕ => sampleLaw E hG x
      (Theorem16.trajOf (ContinuousTimeChain.levelProcess E w (E.nz x) j) ⁻¹' cylinder s S))
      atTop (𝓝 (sampleLaw E hG x (Theorem16.trajOf (process E w) ⁻¹' cylinder s S))) := by
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (Theorem16.measurable_trajOf hXm hBm)
      (fun j => Theorem16.measurable_trajOf (hXnm j) hBm) ?_
    filter_upwards [Theorem16.ae_eventually_restrict_eq
      (ae_eventually_levelProcess_eq E hG w hw x (hsum x)) s (fun u : ℝ≥0 => u)] with ω hω
    filter_upwards [hω] with j hj
    have p : Finset.restrict s
          (Theorem16.trajOf (ContinuousTimeChain.levelProcess E w (E.nz x) j) ω) =
        Finset.restrict s (Theorem16.trajOf (process E w) ω) := funext fun k => hj k.1 k.2
    simp only [Set.mem_preimage, mem_cylinder, p]
  -- read both sides as trajectory laws
  have e : ∀ j : ℕ, CTRW.trajLaw w (E.stepKernel hG (E.nz x + j)) x (cylinder s S) =
      sampleLaw E hG x
        (Theorem16.trajOf (ContinuousTimeChain.levelProcess E w (E.nz x) j) ⁻¹'
          cylinder s S) := by
    intro j
    rw [← ContinuousTimeChain.map_trajOf_levelProcess E w hG hw (E.nz x) x j,
      Measure.map_apply (Theorem16.measurable_trajOf (hXnm j)) hBm]
  have e' : ((sampleLaw E hG x).map (Theorem16.trajOf (process E w))) (cylinder s S) =
      sampleLaw E hG x (Theorem16.trajOf (process E w) ⁻¹' cylinder s S) :=
    Measure.map_apply (Theorem16.measurable_trajOf hXm) hBm
  rw [e']
  have key2 : Tendsto
      (fun j : ℕ => CTRW.trajLaw w (E.stepKernel hG (E.nz x + j)) x (cylinder s S)) atTop
      (𝓝 (sampleLaw E hG x (Theorem16.trajOf (process E w) ⁻¹' cylinder s S))) := by
    simpa only [e] using key
  -- shift the level index
  have hshift : Tendsto (fun m : ℕ => m - E.nz x) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b + E.nz x, fun a ha => by omega⟩
  refine Filter.Tendsto.congr' ?_ (key2.comp hshift)
  filter_upwards [Filter.eventually_ge_atTop (E.nz x)] with m hm
  show CTRW.trajLaw w (E.stepKernel hG (E.nz x + (m - E.nz x))) x (cylinder s S) = _
  rw [show E.nz x + (m - E.nz x) = m from by omega]

/-- **Theorem 1.6, property (iv) (the Markov property) for the constructed process** (p. 25).

For every rate function `w > 0` for which the summability (3.16) holds `P_z`-almost surely for
every `z` (which Lemma 3.5 provides for `w ≥ w*`), the process (3.26) has the Markov property
under the paper's `P_z`, with comparison laws the laws of the same process started at the other
vertices.  This is the `hiv` hypothesis of `Existence.isReflectedWalk`. -/
theorem markovProperty (hw : ∀ x, 0 < w x)
    (hsum : ∀ z, ∀ᵐ ω ∂sampleLaw E hG z, HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2)
    (z : V) :
    Theorem16.MarkovProperty
      (fun x => (sampleLaw E hG x).map (fun ω t => process E w t ω))
      (sampleLaw E hG z) (process E w) := by
  have hadd : Tendsto (fun i : ℕ => E.nz z + i) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  refine Theorem16.markovProperty_of_tendsto (sampleLaw E hG z)
    (μn := fun i x => CTRW.trajLaw w (E.stepKernel hG (E.nz z + i)) x)
    (Xn := fun i => ContinuousTimeChain.levelProcess E w (E.nz z) i)
    (fun x => Measure.isFiniteMeasure_map _ _) (fun i x => inferInstance)
    (fun i t => ContinuousTimeChain.measurable_levelProcess E w (E.nz z) i t)
    (measurable_process E w)
    (fun u => ae_eventually_levelProcess_eq E hG w hw z (hsum z) u) ?_
    (fun i => ContinuousTimeChain.markovProperty_levelProcess E w hG hw (E.nz z) z i)
  intro x B hB
  exact (tendsto_trajLaw_cylinder E hG w hw hsum x hB).comp hadd

end Existence

/-! ### 6.  The hypothesis `hiv` of the existence half, discharged -/

variable {V : Type u}

/-- **Property (iv) of Theorem 1.6, discharged**: the `hiv` hypothesis of
`Existence.existence_half` (and of `theorem16`) verbatim. -/
theorem markovProperty_hiv (G : ConductanceGraph V) :
    ∀ [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Nontrivial V]
      (E : G.Exhaustion) (hG : G.toSimpleGraph.Connected) (w : V → ℝ), (∀ x, 0 < w x) →
      (∀ z, ∀ᵐ ω ∂Existence.sampleLaw E hG z,
        HoldingTimesSummable (E.levelSets (E.nz z)) ω.1 w ω.2) →
      ∀ z, Theorem16.MarkovProperty
        (fun x => (Existence.sampleLaw E hG x).map (fun ω t => Existence.process E w t ω))
        (Existence.sampleLaw E hG z) (Existence.process E w) := by
  intro mV mS cV nV E hG w hw hsum z
  exact Existence.markovProperty E hG w hw hsum z

set_option linter.unusedVariables false in
/-- **The existence half of Theorem 1.6, unconditionally** (p. 24): `Existence.existence_half`
with its only hypothesis, property (iv), discharged by `markovProperty_hiv`. -/
theorem existence_half' (G : ConductanceGraph V) (hmin : G.EnergyMinimizer) :
    Countable V → Infinite V → G.toSimpleGraph.Connected →
      ∃ wstar : V → ℝ, (∀ x, 0 < wstar x) ∧
        ∀ w : V → ℝ, (∀ x, 0 < w x) → (∀ x, wstar x ≤ w x) →
          ∀ z : V, ∃ 𝓧 : ProcessFamily V, IsReflectedWalk G w hmin 𝓧 :=
  Existence.existence_half G hmin (markovProperty_hiv G)

end ReflectedWalk
