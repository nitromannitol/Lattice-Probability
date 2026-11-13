/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.ActualExcursionErgodicIdentification at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnRecursion

/-! # Actual whole-cycle regeneration at a vertex

The manuscript lemma *Regenerative invariant functionals* (`p:lem:regeninvariant`)
begins:

> Consider the law obtained by concatenating a doubly infinite sequence of
> independent complete return cycles from `v`, with time zero at the entrance to
> the zeroth cycle.  Cycles include their initial holding at `v` and the
> subsequent excursion back to `v`.

Attaching the checked iid-cycle ergodicity of
`ReflectedGMS.Temporal.BernoulliCycleInvariant` to the *actual* reflected process
therefore needs the regeneration property for **complete return cycles**: the
whole path segment from `v` until the first return to `v`, at the actual random
return time, not on a deterministic grid.

`ReflectedGMS.Temporal.RegenerativeErgodicIdentification` proves the manuscript's
excursion-reversal cylinder identity on the constant-step grid `0, δ, …, nδ`.
That does **not** determine a whole cycle: a grid loop may return to the root
between two grid times, so a grid cylinder does not see where the cycle ends.
This file supplies the missing whole-cycle statement.

## What is proved

Write `τ v = targetReturnTime X {v} 1` for the **first complete return time to
`v`**: the first time the path is back at `v` after it has left `v`
(`targetReturnTime X A (n+1) = hitAfter X A (exitAfter X (targetReturnTime X A n))`
with `A = {v}` and `τ⁰ = 0`).  The *cycle* is the path killed at that time,
`killedPathAt X (τ v)`, i.e. `s ↦ X s` for `s < τ v` and `∞` afterwards: exactly
the initial holding at `v` followed by the excursion back to `v`.

* `aemeasurableSetStopped_killedPathAt`: the killed path is measurable for the
  stopped σ-algebra `ℱ_τ` of any a.e. stopping time `τ`.  This is the
  progressive-measurability step that the cylinder machinery of
  `ReflectedGMS.Forms` never needed and that whole-cycle regeneration does.

* `measure_killedPathAt_inter_futureAt` — **whole-cycle regeneration, set form**:
  under the actual fixed-start law `PF.P v`,
  `P_v[cycle ∈ A, post-cycle path ∈ B] = P_v[cycle ∈ A] · P_v[path ∈ B]`,
  for arbitrary measurable sets of trajectories.

* `map_futureAt_firstReturnTime`: the path after the first complete return to `v`
  has again the law `PF.law v`.  (The process genuinely restarts at the end of a
  cycle; this is the "regeneration" half.)

* `map_killedPathAt_prod_futureAt` and `indepFun_killedPathAt_futureAt`: the
  joint-law and `IndepFun` forms — the first complete return cycle at `v` is
  independent of the post-cycle trajectory, and the post-cycle trajectory is a
  fresh copy of the process started at `v`.

## Route and reuse

No new probabilistic input is produced.  The proof reuses

* `ReflectedWalk.Theorem16.strongMarkov_completed`, the strong Markov property of
  `IsReflectedWalk` at an a.e. stopping time, and
* `ReflectedGMS.TargetReturnRecursion.ae_forall_targetReturnTime_finite_mem`,
  `isAEStoppingTime_targetReturnTime`, `aemeasurable_targetReturnTime`, which give
  the actual reflected process's own a.s. finiteness of the return times to a
  finite target.

In particular **no** ordinary embedded-chain recurrence is assumed and no CTRW
killed at an accumulation time is used: the a.s. completion of the cycle is the
already-proved property of the actual reflected walk, specialised to the
singleton target `{v}`.

## What is *not* proved here

This is the one-step regeneration.  Iterating it over the successive return times
`τ v ^[n]` to obtain the full iid cycle sequence, and then length-biasing the
initial holding to pass from the entrance-rooted cycle law to `PP_H^v`, remain
open; see the handoff note for the exact next producer.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.Temporal.ActualExcursionErgodicIdentification

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TargetReturnRecursion

universe u

/-! ### The path killed at a random time -/

section KilledPath

variable {V : Type u} {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The trajectory killed at the random time `τ`: the path up to (but not
including) `τ`, sent to `∞` from `τ` on.  For `τ` the first complete return time
to `v` this is exactly the manuscript's *complete return cycle*: the initial
holding at `v` followed by the excursion back to `v`. -/
noncomputable def killedPathAt (X : ℝ≥0 → Ω → Option V) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Trajectory V :=
  fun s => if (s : WithTop ℝ≥0) < τ ω then X s ω else none

omit mΩ in
lemma killedPathAt_congr {X : ℝ≥0 → Ω → Option V} {τ τ' : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : τ ω = τ' ω) : killedPathAt X τ ω = killedPathAt X τ' ω := by
  funext s
  show (if (s : WithTop ℝ≥0) < τ ω then X s ω else none)
      = (if (s : WithTop ℝ≥0) < τ' ω then X s ω else none)
  rw [h]

omit mΩ in
lemma futureAt_congr {X : ℝ≥0 → Ω → Option V} {τ τ' : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : τ ω = τ' ω) : futureAt X τ ω = futureAt X τ' ω := by
  funext s
  show X (s + (τ ω).untopA) ω = X (s + (τ' ω).untopA) ω
  rw [h]

/-- `Measurable.of_eval` with the domain σ-algebra as a *named* argument.

The mathlib lemma takes the domain σ-algebra as an anonymous instance argument,
so applying it to a goal `Measurable[ℱ t] f` makes instance search return the
*ambient* σ-algebra of `Ω` instead of `ℱ t`.  This restatement can be applied at
any σ-algebra through `(m := …)`. -/
lemma measurable_pi_of_eval_at {α : Type*} {ι : Type*} {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] [m : MeasurableSpace α] {f : α → ∀ i, Y i}
    (hf : ∀ i, Measurable[m] fun c => f c i) : Measurable[m] f :=
  Measurable.of_eval hf

omit mΩ in
/-- `X_u` is measurable for `ℱ_t = σ(X_s : s ≤ t)` when `u ≤ t`. -/
lemma measurable_pastSigma_X (X : ℝ≥0 → Ω → Option V) {u t : ℝ≥0} (hut : u ≤ t) :
    Measurable[pastSigma X t] (X u) := fun S _ =>
  pastSigma_mono X hut _ (measurableSet_pastSigma_eval (X := X) u S)

variable [Countable V]

/-- The killed path is a.e.-measurable as soon as the killing time is. -/
lemma aemeasurable_killedPathAt {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    {P : Measure Ω} {τ : Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ P) :
    AEMeasurable (killedPathAt X τ) P := by
  refine ⟨killedPathAt X (hτm.mk τ), ?_, ?_⟩
  · refine Measurable.of_eval fun s => ?_
    exact Measurable.ite (hτm.measurable_mk measurableSet_Ioi) (hX s) measurable_const
  · filter_upwards [hτm.ae_eq_mk] with ω hω
    exact killedPathAt_congr hω

/-- `aemeasurable_futureAt` for an only a.e.-measurable time. -/
lemma aemeasurable_futureAt' {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    {P : Measure Ω} (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X)
    {τ : Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ P) :
    AEMeasurable (futureAt X τ) P := by
  refine (aemeasurable_futureAt hX hii hR hτm.measurable_mk).congr ?_
  filter_upwards [hτm.ae_eq_mk] with ω hω
  exact futureAt_congr hω.symm

/-- **The path killed at `τ` is `ℱ_τ`-measurable.**  For every measurable set `B`
of trajectories, `{killedPathAt X τ ∈ B}` belongs to the stopped σ-algebra of `τ`
(up to null sets), which is what the strong Markov property of `IsReflectedWalk`
accepts as "the past up to `τ`".

On `{τ ≤ t}` the killed path is the `ℱ_t`-measurable trajectory
`s ↦ 1_{s < τ} X_{min s t}`: the truncation `min s t` is harmless there because
`s < τ ≤ t` on the only times that are not killed. -/
theorem aemeasurableSetStopped_killedPathAt
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) {P : Measure Ω}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ)
    {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    AEMeasurableSetStopped (naturalFiltration X hX) P τ {ω | killedPathAt X τ ω ∈ B} := by
  intro t
  obtain ⟨g, hg, hge⟩ := AEStoppedTime.of_le (σ := τ) hτ (fun _ => le_rfl) t
  obtain ⟨Gt, hGt, hGte⟩ := hτ t
  set Φ : Ω → Trajectory V :=
    fun ω s => if (s : WithTop ℝ≥0) < g ω then X (min s t) ω else none with hΦ
  have hΦm : Measurable[naturalFiltration X hX t] Φ := by
    refine measurable_pi_of_eval_at (m := naturalFiltration X hX t) fun s => ?_
    exact Measurable.ite (hg measurableSet_Ioi)
      (measurable_pastSigma_X X (min_le_right s t)) measurable_const
  have hkey : ∀ ω : Ω, τ ω = g ω → τ ω ≤ (t : WithTop ℝ≥0) →
      killedPathAt X τ ω = Φ ω := by
    intro ω hgω hle
    funext s
    show (if (s : WithTop ℝ≥0) < τ ω then X s ω else none)
        = (if (s : WithTop ℝ≥0) < g ω then X (min s t) ω else none)
    by_cases hs : (s : WithTop ℝ≥0) < τ ω
    · have hs' : (s : WithTop ℝ≥0) < g ω := by rw [← hgω]; exact hs
      have hst : s ≤ t :=
        le_of_lt (WithTop.coe_lt_coe.mp (lt_of_lt_of_le hs hle))
      rw [if_pos hs, if_pos hs', min_eq_left hst]
    · have hs' : ¬ (s : WithTop ℝ≥0) < g ω := by rw [← hgω]; exact hs
      rw [if_neg hs, if_neg hs']
  refine ⟨Φ ⁻¹' B ∩ Gt, MeasurableSet.inter (hΦm hB) hGt, Filter.eventuallyEqSet_iff.2 ?_⟩
  filter_upwards [hge, Filter.eventuallyEqSet_iff.1 hGte] with ω h1 h2
  constructor
  · rintro ⟨hmem, hle⟩
    refine ⟨?_, h2.1 hle⟩
    show Φ ω ∈ B
    rw [← hkey ω (h1 hle) hle]
    exact hmem
  · rintro ⟨hmem, hGω⟩
    have hle : τ ω ≤ (t : WithTop ℝ≥0) := h2.2 hGω
    refine ⟨?_, hle⟩
    show killedPathAt X τ ω ∈ B
    rw [hkey ω (h1 hle) hle]
    exact hmem

end KilledPath

/-! ### Whole-cycle regeneration for the actual reflected process -/

section Regeneration

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- The **first complete return time to `v`**: the first time the path is back at
`v` after it has left `v`.  This is `targetReturnTime` for the singleton target
`{v}` at index `1`, which is exactly the manuscript's cycle length: the initial
holding at `v` plus the excursion back to `v`. -/
noncomputable def firstReturnTime {Ω : Type u} (X : ℝ≥0 → Ω → Option V) (v : V) :
    Ω → WithTop ℝ≥0 :=
  targetReturnTime X ({v} : Finset V) 1

/-- **The cycle is completed almost surely.**  Under the actual fixed-start law
`PF.P v` the first complete return to `v` happens at a finite time and the path
is at `v` then.  This is the reflected walk's own recurrence statement,
specialised to the singleton target; no embedded-chain recurrence is used. -/
theorem ae_mem_stopEvent_firstReturnTime (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (v : V) :
    ∀ᵐ ω ∂PF.P v, ω ∈ stopEvent PF.X (firstReturnTime PF.X v) v := by
  filter_upwards [ae_forall_targetReturnTime_finite_mem h hG
    (Finset.singleton_nonempty v) (Finset.mem_singleton_self v)] with ω hω
  obtain ⟨hfin, hmem⟩ := hω 1
  refine ⟨hfin, ?_⟩
  obtain ⟨x, hx, hxv⟩ := hmem
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
  rw [hx] at hxv
  exact hxv.symm

/-- **Whole-cycle regeneration, set form.**  Under the actual fixed-start law
`PF.P v`, the complete return cycle at `v` — the path killed at the first return
to `v`, i.e. the initial holding at `v` together with the whole excursion back to
`v` — is independent of the trajectory after that return, and the latter has the
law of the process started at `v`:

`P_v[cycle ∈ A and post-cycle path ∈ B] = P_v[cycle ∈ A] · (law of the walk from v)(B)`.

The return time is the actual random return time, so `A` genuinely constrains a
whole cycle; a deterministic grid cylinder cannot express this. -/
theorem measure_killedPathAt_inter_futureAt (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (v : V)
    {A B : Set (Trajectory V)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    PF.P v ({ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ A} ∩
        {ω | futureAt PF.X (firstReturnTime PF.X v) ω ∈ B})
      = PF.P v {ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ A} * PF.law v B := by
  have hR := (h v).2.2.2.1
  have hτm : AEMeasurable (firstReturnTime PF.X v) (PF.P v) :=
    aemeasurable_targetReturnTime h hG (Finset.singleton_nonempty v)
      (Finset.mem_singleton_self v) 1
  have hτ : IsAEStoppingTime PF.naturalFiltration (PF.P v) (firstReturnTime PF.X v) :=
    isAEStoppingTime_targetReturnTime h hG (Finset.singleton_nonempty v)
      (Finset.mem_singleton_self v) 1
  have hF := aemeasurableSetStopped_killedPathAt (X := PF.X) PF.measurable_X hτ hA
  have hSM := strongMarkov_completed h v hR hτm hτ v hF hB
  have hfull := ae_mem_stopEvent_firstReturnTime h hG v
  have e1 : PF.P v ({ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ A} ∩
        stopEvent PF.X (firstReturnTime PF.X v) v ∩
        futureAt PF.X (firstReturnTime PF.X v) ⁻¹' B)
      = PF.P v ({ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ A} ∩
        {ω | futureAt PF.X (firstReturnTime PF.X v) ω ∈ B}) := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hfull] with ω hω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    tauto
  have e2 : PF.P v ({ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ A} ∩
        stopEvent PF.X (firstReturnTime PF.X v) v)
      = PF.P v {ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ A} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hfull] with ω hω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [e1, e2] at hSM
  exact hSM

/-- **The process restarts at the end of a complete cycle.**  The trajectory
after the first complete return to `v` has again the law `PF.law v` of the
reflected walk started at `v`. -/
theorem map_futureAt_firstReturnTime (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (v : V) :
    (PF.P v).map (futureAt PF.X (firstReturnTime PF.X v)) = PF.law v := by
  have hR := (h v).2.2.2.1
  have hii := (h v).2.2.1
  have hτm : AEMeasurable (firstReturnTime PF.X v) (PF.P v) :=
    aemeasurable_targetReturnTime h hG (Finset.singleton_nonempty v)
      (Finset.mem_singleton_self v) 1
  have hfm : AEMeasurable (futureAt PF.X (firstReturnTime PF.X v)) (PF.P v) :=
    aemeasurable_futureAt' PF.measurable_X hii hR hτm
  ext B hB
  rw [Measure.map_apply_of_aemeasurable hfm hB]
  have hkey := measure_killedPathAt_inter_futureAt h hG v MeasurableSet.univ hB
  have huniv : {ω : PF.Ω | killedPathAt PF.X (firstReturnTime PF.X v) ω ∈ (Set.univ :
      Set (Trajectory V))} = Set.univ := by
    ext ω; simp
  rw [huniv, Set.univ_inter, measure_univ, one_mul] at hkey
  exact hkey

/-- **Whole-cycle regeneration, joint-law form.**  Under `PF.P v` the pair
(complete return cycle at `v`, trajectory after the return) has the product law
`(cycle law) ⊗ (PF.law v)`.  This is the exact input needed to make the
successive return cycles an iid sequence, i.e. to attach
`ReflectedGMS.Temporal.ergodic_cycleShift` to the actual reflected process. -/
theorem map_killedPathAt_prod_futureAt (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (v : V) :
    (PF.P v).map (fun ω => (killedPathAt PF.X (firstReturnTime PF.X v) ω,
        futureAt PF.X (firstReturnTime PF.X v) ω))
      = ((PF.P v).map (killedPathAt PF.X (firstReturnTime PF.X v))).prod (PF.law v) := by
  have hR := (h v).2.2.2.1
  have hii := (h v).2.2.1
  have hτm : AEMeasurable (firstReturnTime PF.X v) (PF.P v) :=
    aemeasurable_targetReturnTime h hG (Finset.singleton_nonempty v)
      (Finset.mem_singleton_self v) 1
  have hkm : AEMeasurable (killedPathAt PF.X (firstReturnTime PF.X v)) (PF.P v) :=
    aemeasurable_killedPathAt PF.measurable_X hτm
  have hfm : AEMeasurable (futureAt PF.X (firstReturnTime PF.X v)) (PF.P v) :=
    aemeasurable_futureAt' PF.measurable_X hii hR hτm
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply_of_aemeasurable (hkm.prodMk hfm) (hs.prod ht),
    Measure.map_apply_of_aemeasurable hkm hs]
  exact measure_killedPathAt_inter_futureAt h hG v hs ht

/-- **Whole-cycle regeneration, independence form.**  The complete return cycle
at `v` and the post-cycle trajectory are independent under `PF.P v`. -/
theorem indepFun_killedPathAt_futureAt (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (v : V) :
    IndepFun (killedPathAt PF.X (firstReturnTime PF.X v))
      (futureAt PF.X (firstReturnTime PF.X v)) (PF.P v) := by
  have hR := (h v).2.2.2.1
  have hii := (h v).2.2.1
  have hτm : AEMeasurable (firstReturnTime PF.X v) (PF.P v) :=
    aemeasurable_targetReturnTime h hG (Finset.singleton_nonempty v)
      (Finset.mem_singleton_self v) 1
  have hkm : AEMeasurable (killedPathAt PF.X (firstReturnTime PF.X v)) (PF.P v) :=
    aemeasurable_killedPathAt PF.measurable_X hτm
  have hfm : AEMeasurable (futureAt PF.X (firstReturnTime PF.X v)) (PF.P v) :=
    aemeasurable_futureAt' PF.measurable_X hii hR hτm
  rw [indepFun_iff_map_prod_eq_prod_map_map hkm hfm,
    map_futureAt_firstReturnTime h hG v]
  exact map_killedPathAt_prod_futureAt h hG v

end Regeneration

end ReflectedGMS.Temporal.ActualExcursionErgodicIdentification
