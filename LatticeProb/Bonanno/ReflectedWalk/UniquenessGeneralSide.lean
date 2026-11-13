/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.UniquenessGeneralSide at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessSkeleton
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain
import LatticeProb.Bonanno.ReflectedWalk.TransitionUniqueness
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain

/-!
# The general-process side of the uniqueness argument (Gwynne–Sung, Section 3.4, Step 1)

`UniquenessSkeleton.lean` builds, from an **arbitrary** process `X̃` satisfying the properties
(i)–(vi) of Theorem 1.6, the stopping times `tⁿ_j` of (3.31) and proves the strong Markov
property (Lemma 3.10) at each of them.  This file carries out the rest of Step 1 of the paper's
uniqueness proof (p. 26): it identifies the law of the **embedded chain** `(X̃_{tⁿ_j})_{j ≥ 0}`.

> "By this and Property (iii), on the event `{X̃_{tⁿ_j} = x}`, the random variables `X̃_{tⁿ_{j+1}}`
> and `Tⁿ_j` are conditionally independent given `{X̃_s}_{s ≤ tⁿ_j}`, and the conditional law of
> `Tⁿ_j` is exponential with parameter `w(x)`.  Furthermore, if `x ∈ Gₙ`, then the conditional law
> of `X̃_{tⁿ_{j+1}}` is given by a step of the random walk on `G` started from `x`.  If
> `x ∈ B₁Gₙ \ Gₙ`, then by Property (vi) (applied with `A = VGₙ`), the conditional law of
> `X̃_{tⁿ_{j+1}}` is instead given by harmonic measure on `VGₙ` viewed from `x`."

The conclusion is that `(X̃_{tⁿ_j})_j` is the Markov chain `Yⁿ` with the transition
probabilities (3.2)–(3.3), i.e. that its law is `ApproximatingChain`'s
`ConductanceGraph.Exhaustion.chainLaw` — which is the same object the construction side uses,
so the two halves of the uniqueness proof meet there.

## The route

Lemma 3.10, as proved in `StrongMarkov.lean`, computes
`P_z(F ∩ {X̃_{tⁿ_j} = x} ∩ {X̃_{·+tⁿ_j} ∈ B}) = P_z(F ∩ {X̃_{tⁿ_j} = x}) · P_x(B)` for a
**measurable** set `B` of trajectories.  The event we must feed it — "the next step of (3.31)
lands on `y` after a holding time in `I`" — is a hitting-time event, and hitting times of an
uncountable index set are *not* measurable functionals of the trajectory: they are only
measurable at right-regular trajectories (this is exactly the obstruction the skeleton solves
on the sample space with `denseHitAfter`).  So we build the measurable surrogate on the path
space itself:

* `evalProc`: the coordinate process on `Trajectory V`, making the path space a sample space
  to which the whole skeleton applies.
* `dhit S`: the skeleton's `denseHitAfter` on the path space — a genuinely measurable
  functional which agrees with the hitting time of `S` at every right-regular trajectory.
* `nextEvent Gn I y`: the measurable set of trajectories "the next step of (3.31) takes a time
  in `I` and lands on `y`"; `mem_nextEvent_iff` identifies it at right-regular trajectories.
* `hittingAfter_shift_eq`, `stopEvent_shift_iff`: the hitting time after `t` of the process is
  the hitting time of the *shifted* trajectory, shifted; this is what turns the events of
  (3.31) at `tⁿ_j` into events of `futureAt X̃ tⁿ_j`.

With these, the one-step theorems of Step 1 are:

* `measure_stopEvent_succ_of_mem` — **Property (iii) at `tⁿ_j`** (the paper's "conditionally
  independent … exponential with parameter `w(x)` … a step of the random walk"): for `x ∈ VGₙ`,
  the holding time `Tⁿ_j` and the new position `X̃_{tⁿ_{j+1}}` are conditionally independent
  given the past, with laws `Exponential(w x)` and `c(x,·)/π(x)`.
* `measure_stopEvent_succ_of_notMem` — **Property (vi) at `tⁿ_j`** (the re-entry law): for
  `x ∉ VGₙ`, the conditional law of `X̃_{tⁿ_{j+1}}` is the harmonic measure `hm^x_{VGₙ}`.
* `measure_exitTime_hitting_of_notMem` — **property (vi) *with the holding time***.  For
  `x ∈ B₁Gₙ \ Gₙ` the paper asserts the conditional independence of `Tⁿ_j` and `X̃_{tⁿ_{j+1}}`
  "by Property (iii)", but the step of (3.31) from such an `x` is the *hitting of `VGₙ`*, which
  happens at or after the exit from `x`: property (iii) alone does not see it.  The proof here
  applies Lemma 3.10 **at the exit time** as well, sums over the exit position, and compares
  with `I = [0,∞]` to factor the joint law as `Exponential(w x) ⊗ hm^x_{VGₙ}`.
* `measure_stopEvent_succ_pair` — the two previous items in one statement, for **every**
  `x ∈ B₁Gₙ`: on `{X̃_{tⁿ_j} = x}`, given the past, `(Tⁿ_j, X̃_{tⁿ_{j+1}})` has the law
  `Exponential(w(x)) ⊗ pₙ(x, ·)`.

## The law of the pair, and the meeting point with the construction

* `measure_definedAt_eq_one`, `ae_forall_definedAt`: almost surely `tⁿ_j < ∞` and
  `X̃_{tⁿ_j} ∈ VG` for every `j`, so the embedded chain is a random element of `VG^ℕ`.
* `measure_pairCylEvent`: the finite-dimensional distributions of the pair
  `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)` — the product of the transition probabilities `pₙ` of (3.2)–(3.3)
  with the exponential laws `Exponential(w(X̃_{tⁿ_j}))`.
* `map_embeddedPairOf`, `map_embeddedPairOf_exhaustion` — **the headline**:

    `(𝓧.P z).map (embeddedPairOf 𝓧.X (E.Gsub n) v₀) = E.chainLaw hG n z ⊗ₘ holdingKernel w`,

  i.e. the embedded chain of an arbitrary process satisfying (i)–(vi), **paired with its holding
  times**, has exactly the law that `ContinuousTimeChain.map_embeddedPair` proves for the
  constructed process `Xⁿ` of (3.15).  The measure-theoretic input is the π-system `pairRects`
  of prefix rectangles (`isPiSystem_pairRects`, `generateFrom_pairRects`), the prefix
  probabilities `chainLaw_prefixEvent` of the Ionescu–Tulcea chain law, and
  `Measure.infinitePi_pi` for the conditional law of the holding times.
* `processTildeN` is **(3.32)** — `X̃ⁿ_t = X̃_{tⁿ_k}` for the unique `k` with
  `t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)` — realised as `ContinuousTimeChain.jumpPath` applied to
  that pair (`processTildeN_eq_of_mem_Ico`).  `measure_processTildeN_eq_chainFamily` and
  `exists_measurable_processTildeN` then give the one-time marginals of `X̃ⁿ` as the *same*
  family of laws `q` that `ContinuousTimeChain.chainFamily_transition` computes for `Xⁿ`, which
  is what `UniquenessLimit.ApproximatedBy` demands of both halves of the comparison.

## What Step 2 still needs

`UniquenessLimit.approximatedAtFixedTimes_of_shiftBound` consumes the hypothesis `ShiftBound`,
i.e. the paper's (3.33): "if `X̃_t ∈ VGₙ` then `X̃ⁿ_t = X̃_{t − Rₙ}` with `0 ≤ Rₙ ≤ ∫₀ᵗ 1(X̃ ∉ Gₙ)`".
With `Sₖ := ∑_{j<k} Tⁿ_j` and `Dₖ := tⁿ_k − Sₖ` (the time excised before `tⁿ_k`), (3.32) gives
`X̃ⁿ_t = X̃_{tⁿ_k}` for the `k` with `t ∈ [Sₖ, S_{k+1})`, and `tⁿ_k` may be **larger** than `t`
(by at most `Dₖ`).  In that case `X̃ⁿ_t` is the position of `X̃` at a *later* time and (3.33) as
printed is not available: what is true in the forward direction is `X̃ⁿ_{t − Dⱼ} = X̃_t`.  Step 2
does go through, by the two-sided argument: if `tⁿ_k ≤ t` then `X̃_t = X̃_{tⁿ_k}` outright (the
path is constant on `[tⁿ_k, exitAfter tⁿ_k)`), and if `tⁿ_k > t` then `tⁿ_k − t ≤ Dₖ`, while
`Dₖ ≤ ∫₀^{tⁿ_k} 1(X̃ ∉ Gₙ)` and `tⁿ_k ≤ t + Dₖ` force `Dₖ < ε` as soon as
`∫₀ᵗ 1(X̃ ∉ Gₙ) < ε`, with `ε` the radius from property (i) at `t`; then property (i) gives
`X̃_{tⁿ_k} = X̃_t`.  Formalising that argument (rather than `ShiftBound`) still needs: the a.s.
divergence `∑_j Tⁿ_j = ∞` and `tⁿ_j → ∞` (property (v) plus the law of `Tⁿ_j` above), the
monotonicity `Sₖ ≤ tⁿ_k`, and the measure estimate `Dₖ ≤ ∫₀^{tⁿ_k} 1(X̃ ∉ Gₙ)` for the union of
excised intervals.  None of that is in this file.

## The standing hypothesis

`StrongMarkov.lean` proves Lemma 3.10 under the hypothesis `RightContinuousAtInfty` (a.s., at
every time `t` with `X_t = ∞` and every vertex `y`, `X ≠ y` on some `(t, t+ε)`) — the half of
right continuity that the printed property (ii) does not state.  Every theorem below carries it
as the explicit hypothesis `hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X`, as it did when the
clause was an open input.  Since the approved completion of property (ii) recorded in
`Theorem16Statement.lean` the clause is a conjunct of `IsReflectedWalk` itself (it is not
implied by the printed (i)–(vi): `Lemma311.not_hR`), so for `h : IsReflectedWalk G w hmin 𝓧`
the hypothesis is redundant and is supplied by `fun x => (h x).2.2.2.1`; the signatures are
left unchanged.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk
namespace Theorem16

variable {V : Type u}

/-! ### The path space as a sample space

The path space `Trajectory V` with the coordinate process `evalProc` is itself a sample space
carrying a process, so every pointwise lemma of `UniquenessSkeleton.lean` applies to it.  This
is how the *functionals of the trajectory* that Lemma 3.10 needs are built. -/

/-- The coordinate process `f ↦ f t` on the path space `Trajectory V` (Section 3.4). -/
def evalProc (V : Type u) : ℝ≥0 → Trajectory V → Option V := fun t f => f t

lemma measurable_evalProc (t : ℝ≥0) : Measurable (evalProc V t) := measurable_pi_apply t

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V} {P : Measure Ω}

omit mΩ in
@[simp] lemma evalProc_shiftedPath (a s : ℝ≥0) (ω : Ω) :
    evalProc V s (shiftedPath X a ω) = X (s + a) ω := rfl

omit mΩ in
lemma shiftedPath_zero (ω : Ω) : shiftedPath X 0 ω = fun s => X s ω := by
  funext s; simp [shiftedPath]

omit mΩ in
/-- Right regularity (the pointwise content of (ii)+(R)) passes to the shifted trajectory. -/
lemma rightRegularAt_shiftedPath {ω : Ω} (hω : RightRegularAt X ω) (a : ℝ≥0) :
    RightRegularAt (evalProc V) (shiftedPath X a ω) := by
  refine ⟨fun t ht => ?_, fun t ht y => ?_⟩
  · obtain ⟨ε, hε, hεs⟩ := hω.1 (t + a) ht
    refine ⟨ε, hε, fun s hs => ?_⟩
    show X (s + a) ω = X (t + a) ω
    refine hεs (s + a) ⟨add_le_add hs.1 le_rfl, ?_⟩
    rw [add_right_comm]
    exact add_lt_add_of_lt_of_le hs.2 le_rfl
  · obtain ⟨ε, hε, hεs⟩ := hω.2 (t + a) ht y
    refine ⟨ε, hε, fun s hs => ?_⟩
    show X (s + a) ω ≠ some y
    refine hεs (s + a) ⟨add_lt_add_of_lt_of_le hs.1 le_rfl, ?_⟩
    rw [add_right_comm]
    exact add_lt_add_of_lt_of_le hs.2 le_rfl

/-! ### The hitting time after `t` is the hitting time of the shifted trajectory -/

omit mΩ in
/-- The hitting time of `S` after `a` is infinite exactly when the shifted trajectory never
meets `S`. -/
lemma hittingAfter_shift_eq_top_iff (S : Set (Option V)) (a : ℝ≥0) (ω : Ω) :
    hittingAfter X S a ω = ⊤ ↔ hittingAfter (evalProc V) S 0 (shiftedPath X a ω) = ⊤ := by
  rw [hittingAfter_eq_top_iff, hittingAfter_eq_top_iff]
  constructor
  · intro h j _
    exact h (j + a) le_add_self
  · intro h j hj
    have hjj : X j ω = evalProc V (j - a) (shiftedPath X a ω) := by
      show X j ω = X (j - a + a) ω
      rw [tsub_add_cancel_of_le hj]
    rw [hjj]
    exact h (j - a) (by simp)

omit mΩ in
/-- **The shift identity for hitting times.**  At a right-regular outcome, if the shifted
trajectory hits the admissible target `S` first at time `r`, then the process hits `S` after
`a` first at time `r + a`.  This is what turns the recursion (3.31) at `tⁿ_j` into a
functional of `{X̃_{s + tⁿ_j}}_{s ≥ 0}`. -/
lemma hittingAfter_shift_eq {S : Set (Option V)} (hS : AdmissibleTarget S) {ω : Ω}
    (hω : RightRegularAt X ω) {a r : ℝ≥0}
    (h : hittingAfter (evalProc V) S 0 (shiftedPath X a ω) = (r : WithTop ℝ≥0)) :
    hittingAfter X S a ω = ((r + a : ℝ≥0) : WithTop ℝ≥0) := by
  have hf : RightRegularAt (evalProc V) (shiftedPath X a ω) := rightRegularAt_shiftedPath hω a
  have hmem : X (r + a) ω ∈ S := mem_of_hittingAfter_eq_of_rightRegular hf hS h
  refine le_antisymm (hittingAfter_le_of_mem le_add_self hmem) ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt
  have h1 : evalProc V (j - a) (shiftedPath X a ω) ∈ S := by
    show X (j - a + a) ω ∈ S
    rwa [tsub_add_cancel_of_le hj.1]
  have h2 : hittingAfter (evalProc V) S 0 (shiftedPath X a ω) ≤ ((j - a : ℝ≥0) : WithTop ℝ≥0) :=
    hittingAfter_le_of_mem (by simp) h1
  rw [h, WithTop.coe_le_coe] at h2
  have h3 : r + a ≤ j := by
    calc r + a ≤ (j - a) + a := add_le_add h2 le_rfl
      _ = j := tsub_add_cancel_of_le hj.1
  exact absurd hj.2 (not_lt.2 h3)

omit mΩ in
/-- **The stopped position at a hitting time is a functional of the shifted trajectory.**  At a
right-regular outcome, the event "the hitting time of `S` after `a` is finite and the process is
at `y` there" is the same event for the shifted trajectory at `0`. -/
lemma stopEvent_shift_iff {S : Set (Option V)} (hS : AdmissibleTarget S) {ω : Ω}
    (hω : RightRegularAt X ω) (a : ℝ≥0) (y : V) :
    (hittingAfter X S a ω ≠ ⊤ ∧ stoppedValue X (hittingAfter X S a) ω = some y) ↔
      (hittingAfter (evalProc V) S 0 (shiftedPath X a ω) ≠ ⊤ ∧
        stoppedValue (evalProc V) (hittingAfter (evalProc V) S 0) (shiftedPath X a ω) =
          some y) := by
  cases hr : hittingAfter (evalProc V) S 0 (shiftedPath X a ω) with
  | top =>
    have htop : hittingAfter X S a ω = ⊤ := (hittingAfter_shift_eq_top_iff S a ω).2 hr
    simp [htop]
  | coe r =>
    have hX' : hittingAfter X S a ω = ((r + a : ℝ≥0) : WithTop ℝ≥0) :=
      hittingAfter_shift_eq hS hω hr
    rw [stoppedValue_of_eq hX', stoppedValue_of_eq hr]
    simp only [hX', ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_and]
    exact Iff.rfl

/-! ### The measurable surrogate for the hitting time on the path space -/

/-- A fixed countable dense set of times, used to build the measurable surrogates. -/
noncomputable def denseTimes : Set ℝ≥0 := (TopologicalSpace.exists_countable_dense ℝ≥0).choose

lemma denseTimes_countable : (denseTimes).Countable :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.1

lemma denseTimes_dense : Dense (denseTimes) :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2

/-- The skeleton's measurable candidate `denseHitAfter` for the hitting time of `S`, on the path
space: `⨅ {d ∈ denseTimes : f d ∈ S}`.  It is measurable for the cylinder σ-algebra, and at a
right-regular trajectory it equals the true hitting time (`dhit_eq_hittingAfter`). -/
noncomputable def dhit (S : Set (Option V)) (f : Trajectory V) : WithTop ℝ≥0 :=
  denseHitAfter (evalProc V) S (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) denseTimes f

lemma measurable_dhit (S : Set (Option V)) : Measurable (dhit (V := V) S) :=
  measurable_denseHitAfter measurable_evalProc measurable_const denseTimes_countable

open scoped Classical in
lemma dhit_apply (S : Set (Option V)) (f : Trajectory V) :
    dhit S f = ⨅ d : denseTimes, if f d.1 ∈ S then ((d.1 : ℝ≥0) : WithTop ℝ≥0) else ⊤ := by
  refine iInf_congr fun d => ?_
  have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ ((d.1 : ℝ≥0) : WithTop ℝ≥0) := by
    exact_mod_cast (by simp : (0 : ℝ≥0) ≤ d.1)
  simp only [h0, true_and]
  rfl

lemma dhit_le_of_mem {S : Set (Option V)} {f : Trajectory V} {d : ℝ≥0} (hd : d ∈ denseTimes)
    (hf : f d ∈ S) : dhit S f ≤ ((d : ℝ≥0) : WithTop ℝ≥0) := by
  classical
  rw [dhit_apply]
  refine iInf_le_of_le ⟨d, hd⟩ ?_
  rw [ite_eq_left hf]

lemma le_dhit {S : Set (Option V)} {f : Trajectory V} {c : WithTop ℝ≥0}
    (h : ∀ d ∈ denseTimes, f d ∈ S → c ≤ ((d : ℝ≥0) : WithTop ℝ≥0)) : c ≤ dhit S f := by
  classical
  rw [dhit_apply]
  refine le_iInf fun d => ?_
  by_cases hd : f d.1 ∈ S
  · simpa [hd] using h d.1 d.2 hd
  · simp [hd]

lemma dhit_mono {S S' : Set (Option V)} (hSS' : S' ⊆ S) (f : Trajectory V) :
    dhit S f ≤ dhit S' f :=
  le_dhit fun d hd hfd => dhit_le_of_mem hd (hSS' hfd)

/-- At a right-regular trajectory the measurable surrogate is the hitting time. -/
lemma dhit_eq_hittingAfter {S : Set (Option V)} (hS : AdmissibleTarget S) {f : Trajectory V}
    (hf : RightRegularAt (evalProc V) f) : dhit S f = hittingAfter (evalProc V) S 0 f := by
  have h := hitAfter_eq_denseHitAfter_of_rightRegular (X := evalProc V) (S := S)
    (σ := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) (σ' := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0))
    hf hS rfl (D := denseTimes) denseTimes_dense
  rw [dhit, ← h, hitAfter_const]

/-- **The stopped position, as a measurable condition.**  At a right-regular trajectory, the
hitting time of the admissible target `S` is finite with value `some y` there exactly when the
surrogate for `S ∩ {some y}` agrees with the (finite) surrogate for `S`.  This is the measurable
description of `{X_τ = y}` used to feed Lemma 3.10. -/
lemma dhit_inter_iff {S : Set (Option V)} (hS : AdmissibleTarget S) {f : Trajectory V}
    (hf : RightRegularAt (evalProc V) f) (y : V) :
    (dhit (S ∩ {some y}) f = dhit S f ∧ dhit S f ≠ ⊤) ↔
      (hittingAfter (evalProc V) S 0 f ≠ ⊤ ∧
        stoppedValue (evalProc V) (hittingAfter (evalProc V) S 0) f = some y) := by
  have hd : dhit S f = hittingAfter (evalProc V) S 0 f := dhit_eq_hittingAfter hS hf
  cases hr : hittingAfter (evalProc V) S 0 f with
  | top => simp [hd, hr]
  | coe t =>
    have hft : f t ∈ S := mem_of_hittingAfter_eq_of_rightRegular hf hS hr
    have hval : stoppedValue (evalProc V) (hittingAfter (evalProc V) S 0) f = f t :=
      stoppedValue_of_eq hr
    rw [hval, hd, hr]
    simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, and_true, true_and]
    constructor
    · intro hEq
      by_contra hne
      -- on a right neighbourhood of `t` the trajectory avoids `some y`
      obtain ⟨ε, hε, hεs⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), f s ≠ some y := by
        by_cases hnone : f t = none
        · obtain ⟨ε, hε, hεs⟩ := hf.2 t hnone y
          refine ⟨ε, hε, fun s hs => ?_⟩
          rcases eq_or_lt_of_le hs.1 with rfl | hlt
          · simp [hnone]
          · exact hεs s ⟨hlt, hs.2⟩
        · obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.1 hnone
          obtain ⟨ε, hε, hεs⟩ := hf.1 t ⟨y', hy'⟩
          refine ⟨ε, hε, fun s hs => ?_⟩
          have hst : f s = f t := hεs s hs
          rw [hst]
          exact hne
      have hge : ((t + ε : ℝ≥0) : WithTop ℝ≥0) ≤ dhit (S ∩ {some y}) f := by
        refine le_dhit fun d hd hfd => ?_
        have hdy : f d = some y := hfd.2
        have hdS : f d ∈ S := hfd.1
        have htd : t ≤ d := by
          have := hittingAfter_le_of_mem (u := evalProc V) (s := S) (n := (0 : ℝ≥0))
            (i := d) (ω := f) (by simp) hdS
          rw [hr, WithTop.coe_le_coe] at this
          exact this
        have : ¬ d < t + ε := fun hlt => hεs d ⟨htd, hlt⟩ hdy
        exact_mod_cast not_lt.1 this
      rw [hEq] at hge
      exact absurd (WithTop.coe_le_coe.1 hge) (not_le.2 (lt_add_of_pos_right t hε))
    · intro hfy
      have hmono : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ dhit (S ∩ {some y}) f := by
        rw [← hr, ← hd]
        exact dhit_mono Set.inter_subset_left f
      refine le_antisymm ?_ hmono
      refine Theorem16.WithTop.le_coe_of_forall_lt fun c hc => ?_
      obtain ⟨ε, hε, hεs⟩ := hf.1 t ⟨y, hfy⟩
      have htm : t < min (t + ε) c := lt_min (lt_add_of_pos_right t hε) hc
      obtain ⟨d, hdD, htd, hdm⟩ := denseTimes_dense.exists_between htm
      have hfd : f d = some y := by
        have hdt : f d = f t := hεs d ⟨htd.le, lt_of_lt_of_le hdm (min_le_left _ _)⟩
        rw [hdt]
        exact hfy
      refine le_trans (dhit_le_of_mem hdD ⟨?_, hfd⟩) ?_
      · rw [hfd]; exact hfy ▸ hft
      · exact_mod_cast (lt_of_lt_of_le hdm (min_le_right _ _)).le

/-! ### One step of the recursion (3.31) as a functional of the trajectory -/

open scoped Classical in
/-- The target set of one step of (3.31) from the state `a`: the exit set `{s ≠ a}` if
`a ∈ VGₙ`, and `VGₙ` otherwise. -/
noncomputable def nextTarget (Gn : Finset V) (a : Option V) : Set (Option V) :=
  if a ∈ some '' (Gn : Set V) then {s | s ≠ a} else some '' (Gn : Set V)

lemma admissibleTarget_nextTarget (Gn : Finset V) (a : Option V) :
    AdmissibleTarget (nextTarget Gn a) := by
  by_cases ha : a ∈ some '' (Gn : Set V)
  · rw [nextTarget, ite_eq_left ha]
    obtain ⟨x, -, rfl⟩ := ha
    exact admissibleTarget_ne x
  · rw [nextTarget, ite_eq_right ha]
    exact admissibleTarget_image Gn

omit mΩ in
/-- The recursion (3.31) is the hitting time of `nextTarget` after the current time. -/
lemma nextStep_eq_hitAfter (Gn : Finset V) (σ : Ω → WithTop ℝ≥0) (ω : Ω) :
    nextStep X Gn σ ω = hitAfter X (nextTarget Gn (stoppedValue X σ ω)) σ ω := by
  unfold nextStep nextTarget
  split_ifs <;> rfl

/-- One step of (3.31) read on the path space: the hitting time, from time `0`, of the target
determined by the starting value `f 0`. -/
noncomputable def trajNext (Gn : Finset V) (f : Trajectory V) : WithTop ℝ≥0 :=
  hittingAfter (evalProc V) (nextTarget Gn (f 0)) 0 f

/-- The **measurable** set of trajectories "the step of (3.31) is finite, takes a time in `I`,
and lands on the vertex `y`", built from the surrogate `dhit`.  This is the set `B` fed to
Lemma 3.10; `mem_nextEvent_iff` identifies it with the true event at every right-regular
trajectory. -/
noncomputable def nextEvent (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V) :
    Set (Trajectory V) :=
  ⋃ a : Option V, {f : Trajectory V | f 0 = a} ∩
    ({f | dhit (nextTarget Gn a) f ∈ I} ∩
      ({f | dhit (nextTarget Gn a ∩ {some y}) f = dhit (nextTarget Gn a) f} ∩
        {f | dhit (nextTarget Gn a) f ≠ ⊤}))

lemma measurableSet_nextEvent [Countable V] (Gn : Finset V) {I : Set (WithTop ℝ≥0)}
    (hI : MeasurableSet I) (y : V) : MeasurableSet (nextEvent (V := V) Gn I y) := by
  refine MeasurableSet.iUnion fun a => ?_
  refine MeasurableSet.inter (measurable_evalProc 0 (measurableSet_option {a})) ?_
  refine MeasurableSet.inter (measurable_dhit _ hI) ?_
  exact (measurableSet_eq_fun (measurable_dhit _) (measurable_dhit _)).inter
    (measurable_dhit _ (measurableSet_singleton (⊤ : WithTop ℝ≥0)).compl)

/-- At a right-regular trajectory, the measurable set `nextEvent` is the true event: the step of
(3.31) is finite, takes a time in `I`, and lands on `y`. -/
lemma mem_nextEvent_iff (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V) {f : Trajectory V}
    (hf : RightRegularAt (evalProc V) f) :
    f ∈ nextEvent Gn I y ↔
      (trajNext Gn f ≠ ⊤ ∧ trajNext Gn f ∈ I ∧ f (trajNext Gn f).untopA = some y) := by
  have hmem : f ∈ nextEvent Gn I y ↔
      (dhit (nextTarget Gn (f 0)) f ∈ I ∧
        (dhit (nextTarget Gn (f 0) ∩ {some y}) f = dhit (nextTarget Gn (f 0)) f ∧
          dhit (nextTarget Gn (f 0)) f ≠ ⊤)) := by
    constructor
    · rintro ⟨-, ⟨a, rfl⟩, hfa, h⟩
      have : f 0 = a := hfa
      rw [this]
      exact h
    · intro h
      exact Set.mem_iUnion.2 ⟨f 0, rfl, h⟩
  rw [hmem, dhit_inter_iff (admissibleTarget_nextTarget Gn (f 0)) hf y,
    dhit_eq_hittingAfter (admissibleTarget_nextTarget Gn (f 0)) hf]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

/-! ### Transferring the step of (3.31) to the future trajectory -/

omit mΩ in
/-- **One step of (3.31) at a stopping time is an event of the future trajectory.**  At a
right-regular outcome with `σ = a < ∞`, the step of (3.31) from `σ` is finite, takes a time in
`I` and lands on `y` exactly when the future trajectory `{X_{s+σ}}_{s ≥ 0}` lies in the
measurable set `nextEvent Gn I y`. -/
lemma mem_nextEvent_futureAt_iff {σ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : RightRegularAt X ω)
    (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V) {a : ℝ≥0} (ha : σ ω = a) :
    futureAt X σ ω ∈ nextEvent Gn I y ↔
      (nextStep X Gn σ ω ≠ ⊤ ∧ nextStep X Gn σ ω - σ ω ∈ I ∧
        stoppedValue X (nextStep X Gn σ) ω = some y) := by
  set f := shiftedPath X a ω with hf
  have hfut : futureAt X σ ω = f := futureAt_of_eq ha
  have hf0 : f 0 = stoppedValue X σ ω := by
    show X (0 + a) ω = stoppedValue X σ ω
    rw [zero_add, stoppedValue_of_eq ha]
  set S := nextTarget Gn (stoppedValue X σ ω) with hS
  have hSadm : AdmissibleTarget S := admissibleTarget_nextTarget Gn _
  have hstep : nextStep X Gn σ ω = hittingAfter X S a ω := by
    rw [nextStep_eq_hitAfter, hitAfter_coe ha]
  have htraj : trajNext Gn f = hittingAfter (evalProc V) S 0 f := by
    rw [trajNext, hf0]
  have hfreg : RightRegularAt (evalProc V) f := rightRegularAt_shiftedPath hω a
  rw [hfut, mem_nextEvent_iff Gn I y hfreg, htraj, hstep]
  cases hr : hittingAfter (evalProc V) S 0 f with
  | top =>
    have : hittingAfter X S a ω = ⊤ := (hittingAfter_shift_eq_top_iff S a ω).2 hr
    simp [this]
  | coe r =>
    have hX' : hittingAfter X S a ω = ((r + a : ℝ≥0) : WithTop ℝ≥0) :=
      hittingAfter_shift_eq hSadm hω hr
    have hsub : ((r + a : ℝ≥0) : WithTop ℝ≥0) - (a : WithTop ℝ≥0) = (r : WithTop ℝ≥0) := by
      rw [← WithTop.coe_sub, add_tsub_cancel_right]
    have hval : stoppedValue X (nextStep X Gn σ) ω = f r := by
      rw [stoppedValue_of_eq (hstep.trans hX')]
      rfl
    simp only [hX', ha, hsub, hval, ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_and]
    exact Iff.rfl

/-! ### The law of one step, under `P_x`: properties (iii) and (vi) -/

omit mΩ in
lemma stepTime_one (Gn : Finset V) :
    stepTime X Gn 1 = nextStep X Gn (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) := rfl

omit mΩ in
lemma stepTime_zero_apply (Gn : Finset V) (ω : Ω) :
    stepTime X Gn 0 ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := rfl

lemma measurable_toWithTop : Measurable (toWithTop) :=
  measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal

section OneStep

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}

/-- Every `ConductanceGraph.EnergyMinimizer` is Proposition 1.3's `energyMin` on a non-empty
finite set, by the uniqueness clause of Proposition 1.3. -/
lemma EnergyMinimizer.eq_energyMin (hmin : G.EnergyMinimizer) (hG : G.toSimpleGraph.Connected)
    {A : Finset V} (hA : A.Nonempty) (φ : V → ℝ) : hmin A φ = G.energyMin hG A φ :=
  G.energyMin_unique hG hA φ (hmin.hasFiniteEnergy hA φ) (hmin.eqOn hA φ)
    fun g hg hgA => hmin.le_energy hA φ hg hgA

/-- Harmonic measure on `A` gives no mass outside `A` (Definition 1.5: `h_{1_y} ≡ 0` when
`1_y|_A = 0`). -/
lemma harmonicMeasure_eq_zero_of_notMem (G : ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) {y : V} (hy : y ∉ A)
    (x : V) : G.harmonicMeasure hG A x y = 0 := by
  have heq : Set.EqOn (G.indic y) (Function.const V 0) ↑A := by
    intro v hv
    have hvy : v ≠ y := fun h => hy (h ▸ Finset.mem_coe.1 hv)
    simp [ConductanceGraph.indic, hvy]
  have := congrFun (G.energyMin_congr hG hA heq) x
  rw [ConductanceGraph.harmonicMeasure, this, G.energyMin_const hG hA 0]
  rfl

variable [Countable V]

/-- **Property (vi) as a law** (Section 3.4, "the conditional law of `X̃_{tⁿ_{j+1}}` is given by
harmonic measure on `VGₙ` viewed from `x`"): under `P_x`, the position at the hitting time of a
non-empty finite `A` has the energy-minimising harmonic measure law `hm^x_A` of Definition 1.5.
Property (vi) gives the expectation identity `h_φ(x) = E_x[φ(X_τ)]`; applying it to the
indicators `φ = 1_y` of Definition 1.5 turns it into the law, by Lemma 2.4. -/
theorem measure_stoppedValue_hittingTime (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (x : V) (hR : RightContinuousAtInfty (𝓧.P x) 𝓧.X)
    {A : Finset V} (hA : A.Nonempty) (y : V) :
    𝓧.P x {ω | stoppedValue 𝓧.X (hittingTime 𝓧.X A) ω = some y} =
      ENNReal.ofReal (G.harmonicMeasure hG A x y) := by
  classical
  have hZ : AEMeasurable (stoppedValue 𝓧.X (hittingTime 𝓧.X A)) (𝓧.P x) :=
    aemeasurable_stoppedValue 𝓧.measurable_X (h x).2.2.1 hR
      (aemeasurable_hittingTime 𝓧.measurable_X (h x).2.2.1 hR A)
  obtain ⟨hint, hid⟩ := ((h x).2.2.2.2.2.2.2 A hA).2 (G.indic y)
  set S := (hZ.mk _) ⁻¹' {some y} with hSdef
  have hSm : MeasurableSet S := hZ.measurable_mk (measurableSet_option _)
  have hSeq : {ω | stoppedValue 𝓧.X (hittingTime 𝓧.X A) ω = some y} =ᵐ[𝓧.P x] S := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hZ.ae_eq_mk] with ω hω
    simp only [Set.mem_ofPred_eq, hSdef, Set.mem_preimage, Set.mem_singleton_iff, hω]
  have hintEq : (fun ω => (stoppedValue 𝓧.X (hittingTime 𝓧.X A) ω).elim 0 (G.indic y))
      =ᵐ[𝓧.P x] Set.indicator S (fun _ => (1 : ℝ)) := by
    filter_upwards [hZ.ae_eq_mk] with ω hω
    rw [hω]
    cases hv : hZ.mk _ ω with
    | none => simp [Set.indicator, hSdef, hv]
    | some v =>
      by_cases hvy : v = y <;>
        simp [Set.indicator, hSdef, hv, hvy, ConductanceGraph.indic]
  have hintVal : ∫ ω, (stoppedValue 𝓧.X (hittingTime 𝓧.X A) ω).elim 0 (G.indic y) ∂(𝓧.P x) =
      (𝓧.P x S).toReal := by
    rw [integral_congr_ae hintEq, integral_indicator hSm, setIntegral_const, smul_eq_mul,
      mul_one, measureReal_def]
  rw [congrFun (EnergyMinimizer.eq_energyMin hmin hG hA (G.indic y)) x, hintVal] at hid
  rw [measure_congr hSeq, ConductanceGraph.harmonicMeasure, hid,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

omit [Countable V] in
/-- The exit time of property (iii) is a.s. finite: its law is the image of the exponential
distribution, a measure on `[0,∞)`. -/
lemma measure_exitTime_eq_top (h : IsReflectedWalk G w hmin 𝓧) (x : V) :
    𝓧.P x {ω | exitTime 𝓧.X x ω = ⊤} = 0 := by
  obtain ⟨hmeas, -, -, hlaw, -⟩ := (h x).2.2.2.2.1
  have hset : {ω | exitTime 𝓧.X x ω = ⊤} = exitTime 𝓧.X x ⁻¹' {⊤} := rfl
  rw [hset, ← Measure.map_apply_of_aemeasurable hmeas (measurableSet_singleton ⊤), hlaw,
    Measure.map_apply measurable_toWithTop (measurableSet_singleton ⊤)]
  convert measure_empty (μ := ProbabilityTheory.expMeasure (w x))
  ext r
  simp only [Set.mem_preimage, Set.mem_singleton_iff, toWithTop, Set.mem_empty_iff_false,
    iff_false]
  exact WithTop.coe_ne_top

/-- **Property (iii) as a law at time `0`** (Section 3.4, "the random variables `X̃_{tⁿ_{j+1}}`
and `Tⁿ_j` are conditionally independent … the conditional law of `Tⁿ_j` is exponential with
parameter `w(x)` … the conditional law of `X̃_{tⁿ_{j+1}}` is given by a step of the random walk
on `G` started from `x`"): for `x ∈ VGₙ`, under `P_x` the first step of the recursion (3.31) is
the exit from `x`; its time is exponential with rate `w(x)`, its position is a step of the
random walk, and the two are independent. -/
theorem measure_stepTime_one_of_mem (h : IsReflectedWalk G w hmin 𝓧) {Gn : Finset V} {x : V}
    (hx : x ∈ Gn) {I : Set (WithTop ℝ≥0)} (hI : MeasurableSet I) (y : V) :
    𝓧.P x {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧ stepTime 𝓧.X Gn 1 ω ∈ I ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =
      ((ProbabilityTheory.expMeasure (w x)).map toWithTop) I * ENNReal.ofReal (G.c x y / G.pi x) := by
  obtain ⟨hmeas, -, hindep, hlaw, hval⟩ := (h x).2.2.2.2.1
  have hae : ∀ᵐ ω ∂𝓧.P x, stepTime 𝓧.X Gn 1 ω = exitTime 𝓧.X x ω := by
    filter_upwards [(h x).1] with ω h0
    have h0' : stoppedValue 𝓧.X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω = some x := h0
    rw [stepTime_one, nextStep_eq_of_eq hx h0', exitTime_eq_hitAfter]
  have hfin : ∀ᵐ ω ∂𝓧.P x, exitTime 𝓧.X x ω ≠ ⊤ := by
    have h0 := measure_exitTime_eq_top h x
    rw [ae_iff]
    simpa using h0
  have hset : {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧ stepTime 𝓧.X Gn 1 ω ∈ I ∧
      stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =ᵐ[𝓧.P x]
      (exitTime 𝓧.X x ⁻¹' I) ∩ (stoppedValue 𝓧.X (exitTime 𝓧.X x) ⁻¹' {some y}) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hae, hfin] with ω hω hωfin
    have hsv : stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω =
        stoppedValue 𝓧.X (exitTime 𝓧.X x) ω := by
      simp only [stoppedValue, hω]
    simp only [Set.mem_ofPred_eq, hω, hsv, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, hωfin, ne_eq, not_false_eq_true, true_and]
  rw [measure_congr hset, hindep.measure_inter_preimage_eq_mul _ _ hI
    (measurableSet_option {some y})]
  congr 1
  · rw [← Measure.map_apply_of_aemeasurable hmeas hI, hlaw]
  · exact hval y

/-- **Property (vi) as a law at time `0`** (Section 3.4, the re-entry step of (3.31)): for
`x ∉ VGₙ`, under `P_x` the first step of the recursion (3.31) is the hitting of `VGₙ`, and its
position has the harmonic measure law `hm^x_{VGₙ}`. -/
theorem measure_stepTime_one_of_notMem (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {Gn : Finset V} (hGn : Gn.Nonempty) {x : V} (hx : x ∉ Gn)
    (hR : RightContinuousAtInfty (𝓧.P x) 𝓧.X) (y : V) :
    𝓧.P x {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧ stepTime 𝓧.X Gn 1 ω ∈ (Set.univ : Set (WithTop ℝ≥0)) ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =
      ENNReal.ofReal (G.harmonicMeasure hG Gn x y) := by
  have hae : ∀ᵐ ω ∂𝓧.P x, stepTime 𝓧.X Gn 1 ω = hittingTime 𝓧.X Gn ω := by
    filter_upwards [(h x).1] with ω h0
    have h0' : stoppedValue 𝓧.X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω ∉ some '' (Gn : Set V) := by
      rw [show stoppedValue 𝓧.X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω = some x from h0]
      rintro ⟨v, hv, hvx⟩
      exact hx (Option.some_inj.1 hvx ▸ Finset.mem_coe.1 hv)
    rw [stepTime_one, nextStep_eq_of_notMem h0', hittingTime_eq_hitAfter]
  have hfin : ∀ᵐ ω ∂𝓧.P x, hittingTime 𝓧.X Gn ω ≠ ⊤ :=
    ((h x).2.2.2.2.2.2.2 Gn hGn).1.mono fun _ hω => hω.1
  have hset : {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧
      stepTime 𝓧.X Gn 1 ω ∈ (Set.univ : Set (WithTop ℝ≥0)) ∧
      stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =ᵐ[𝓧.P x]
      {ω | stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω = some y} := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hae, hfin] with ω hω hωfin
    have hsv : stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω =
        stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω := by
      simp only [stoppedValue, hω]
    simp only [Set.mem_ofPred_eq, hω, hsv, Set.mem_univ, hωfin, ne_eq, not_false_eq_true, true_and]
  rw [measure_congr hset, measure_stoppedValue_hittingTime h hG x hR hGn y]

end OneStep

/-! ### The one-step law at the stopping times `tⁿ_j` -/

/-- The holding time `Tⁿ_j` of (3.31): `min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}} − tⁿ_j`. -/
noncomputable def holdingTime (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) :
    ℝ≥0∞ := exitAfter X (stepTime X Gn j) ω - stepTime X Gn j ω

omit mΩ in
/-- If `X̃_{tⁿ_j} = x ∈ VGₙ` then `tⁿ_{j+1}` is the exit time from `x`, so `Tⁿ_j = tⁿ_{j+1} − tⁿ_j`
(the first sentence of p. 26). -/
lemma stepTime_succ_eq_exitAfter {Gn : Finset V} {j : ℕ} {x : V} (hx : x ∈ Gn) {ω : Ω}
    (hω : ω ∈ stopEvent X (stepTime X Gn j) x) :
    stepTime X Gn (j + 1) ω = exitAfter X (stepTime X Gn j) ω := by
  rw [show stepTime X Gn (j + 1) = nextStep X Gn (stepTime X Gn j) from rfl,
    nextStep_eq_of_eq hx hω.2, exitAfter, hω.2]

section OneStepAt

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V]

/-- The `P_x`-law of the first step of (3.31) is the law of the measurable path functional
`nextEvent`.  This is the bridge between Lemma 3.10 (which sees only measurable sets of
trajectories) and properties (iii) and (vi) (which speak of the process under `P_x`). -/
theorem law_nextEvent (h : IsReflectedWalk G w hmin 𝓧) (x : V)
    (hR : RightContinuousAtInfty (𝓧.P x) 𝓧.X) (Gn : Finset V) {I : Set (WithTop ℝ≥0)}
    (hI : MeasurableSet I) (y : V) :
    𝓧.law x (nextEvent Gn I y) =
      𝓧.P x {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧ stepTime 𝓧.X Gn 1 ω ∈ I ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} := by
  rw [ProcessFamily.law, Measure.map_apply 𝓧.measurable_trajectory
    (measurableSet_nextEvent Gn hI y)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_rightRegularAt (h x).2.2.1 hR] with ω hω
  have hfut : futureAt 𝓧.X (stepTime 𝓧.X Gn 0) ω = 𝓧.trajectory ω := by
    rw [futureAt_of_eq (stepTime_zero_apply Gn ω), shiftedPath_zero]
    rfl
  have hiff := mem_nextEvent_futureAt_iff hω Gn I y (stepTime_zero_apply (X := 𝓧.X) Gn ω)
  rw [hfut] at hiff
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hiff, show nextStep 𝓧.X Gn (stepTime 𝓧.X Gn 0) = stepTime 𝓧.X Gn 1 from rfl,
    stepTime_zero_apply]
  simp

/-- **The one-step law at `tⁿ_j`** (Section 3.4, Step 1, second paragraph).  On the event
`{X̃_{tⁿ_j} = x}`, given any event `F` of the past `{X̃_s}_{s ≤ tⁿ_j}`, the pair (time of the next
step of (3.31), position after it) has the `P_x`-law of the first step of (3.31): this is
Lemma 3.10 at `tⁿ_j` combined with the fact that the step of (3.31) is a measurable functional
of the future trajectory. -/
theorem measure_stopEvent_succ (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) (Gn : Finset V) (j : ℕ) (x : V)
    {F : Set 𝓧.Ω}
    (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) (stepTime 𝓧.X Gn j) F)
    {I : Set (WithTop ℝ≥0)} (hI : MeasurableSet I) (y : V) :
    𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
        {ω | stepTime 𝓧.X Gn (j + 1) ω ≠ ⊤ ∧
          stepTime 𝓧.X Gn (j + 1) ω - stepTime 𝓧.X Gn j ω ∈ I ∧
          stoppedValue 𝓧.X (stepTime 𝓧.X Gn (j + 1)) ω = some y}) =
      𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) *
        𝓧.P x {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧ stepTime 𝓧.X Gn 1 ω ∈ I ∧
          stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} := by
  rw [← law_nextEvent h x (hR x) Gn hI y,
    ← stepTime_strongMarkov h z (hR z) Gn j x hF (measurableSet_nextEvent Gn hI y)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_rightRegularAt (h z).2.2.1 (hR z)] with ω hω
  constructor
  · rintro ⟨hFE, hnext⟩
    refine ⟨hFE, ?_⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hFE.2.1
    show futureAt 𝓧.X (stepTime 𝓧.X Gn j) ω ∈ nextEvent Gn I y
    rw [mem_nextEvent_futureAt_iff hω Gn I y ha.symm]
    exact hnext
  · rintro ⟨hFE, hnext⟩
    refine ⟨hFE, ?_⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hFE.2.1
    have hnext' : futureAt 𝓧.X (stepTime 𝓧.X Gn j) ω ∈ nextEvent Gn I y := hnext
    rw [mem_nextEvent_futureAt_iff hω Gn I y ha.symm] at hnext'
    exact hnext'

/-- The exponential law of property (iii) is a probability law on `[0,∞]`. -/
lemma map_toWithTop_expMeasure_univ (h : IsReflectedWalk G w hmin 𝓧) (x : V) :
    ((ProbabilityTheory.expMeasure (w x)).map toWithTop) (Set.univ : Set (WithTop ℝ≥0)) = 1 := by
  obtain ⟨hmeas, -, -, hlaw, -⟩ := (h x).2.2.2.2.1
  rw [← hlaw, Measure.map_apply_of_aemeasurable hmeas MeasurableSet.univ, Set.preimage_univ,
    measure_univ]

/-- **Item 1: the law of `(Tⁿ_j, X̃_{tⁿ_{j+1}})` at `tⁿ_j` for `x ∈ VGₙ`** (Section 3.4, Step 1):
on `{X̃_{tⁿ_j} = x}` with `x ∈ VGₙ`, given the past, the holding time `Tⁿ_j` is exponential with
parameter `w(x)` and the new position `X̃_{tⁿ_{j+1}}` is a step of the random walk on `G` from
`x`, and the two are independent (the law of the pair is the product of the two laws). -/
theorem measure_stopEvent_succ_of_mem (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) {Gn : Finset V} (j : ℕ) {x : V}
    (hx : x ∈ Gn) {F : Set 𝓧.Ω}
    (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) (stepTime 𝓧.X Gn j) F)
    {I : Set (WithTop ℝ≥0)} (hI : MeasurableSet I) (y : V) :
    𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
        ({ω | holdingTime 𝓧.X Gn j ω ∈ I} ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn (j + 1)) y)) =
      𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) *
        (((ProbabilityTheory.expMeasure (w x)).map toWithTop) I * ENNReal.ofReal (G.c x y / G.pi x)) := by
  rw [← measure_stepTime_one_of_mem h hx hI y, ← measure_stopEvent_succ h z hR Gn j x hF hI y]
  refine congrArg _ (Set.ext fun ω => ?_)
  constructor
  · rintro ⟨hFE, hT, hstep⟩
    refine ⟨hFE, hstep.1, ?_, hstep.2⟩
    rwa [stepTime_succ_eq_exitAfter hx hFE.2]
  · rintro ⟨hFE, hne, hT, hval⟩
    refine ⟨hFE, ?_, hne, hval⟩
    show exitAfter 𝓧.X (stepTime 𝓧.X Gn j) ω - stepTime 𝓧.X Gn j ω ∈ I
    rwa [← stepTime_succ_eq_exitAfter hx hFE.2]

/-- **Item 2: the re-entry law at `tⁿ_j` for `x ∉ VGₙ`** (Section 3.4, Step 1: "If
`x ∈ B₁Gₙ \ Gₙ`, then by Property (vi) (applied with `A = VGₙ`), the conditional law of
`X̃_{tⁿ_{j+1}}` is instead given by harmonic measure on `VGₙ` viewed from `x`"). -/
theorem measure_stopEvent_succ_of_notMem (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty) (j : ℕ)
    {x : V} (hx : x ∉ Gn) {F : Set 𝓧.Ω}
    (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) (stepTime 𝓧.X Gn j) F) (y : V) :
    𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
        stopEvent 𝓧.X (stepTime 𝓧.X Gn (j + 1)) y) =
      𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) *
        ENNReal.ofReal (G.harmonicMeasure hG Gn x y) := by
  rw [← measure_stepTime_one_of_notMem h hG hGn hx (hR x) y,
    ← measure_stopEvent_succ h z hR Gn j x hF MeasurableSet.univ y]
  refine congrArg _ (Set.ext fun ω => ?_)
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, true_and]
  exact ⟨fun hh => ⟨hh.1, hh.2.1, hh.2.2⟩, fun hh => ⟨hh.1, hh.2.1, hh.2.2⟩⟩

/-- **The one-step transition of the embedded chain is the kernel (3.2)–(3.3).**  Combining
items 1 and 2: on `{X̃_{tⁿ_j} = x}`, given the past, the new position `X̃_{tⁿ_{j+1}}` has law
`pₙ(x, ·)` — `c(x,·)/π(x)` for `x ∈ VGₙ` and `hm^x_{VGₙ}` otherwise. -/
theorem measure_stopEvent_succ_transProb (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty) (j : ℕ)
    (x : V) {F : Set 𝓧.Ω}
    (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) (stepTime 𝓧.X Gn j) F) (y : V) :
    𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
        stopEvent 𝓧.X (stepTime 𝓧.X Gn (j + 1)) y) =
      𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) *
        ENNReal.ofReal (G.transProb hG Gn x y) := by
  by_cases hx : x ∈ Gn
  · have hmain := measure_stopEvent_succ_of_mem h z hR j hx hF MeasurableSet.univ y
    rw [map_toWithTop_expMeasure_univ h x, one_mul] at hmain
    rw [G.transProb_of_mem hG hx y, ← hmain]
    refine congrArg _ (Set.ext fun ω => ?_)
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    tauto
  · rw [measure_stopEvent_succ_of_notMem h hG z hR hGn j hx hF y]
    by_cases hy : y ∈ Gn
    · rw [G.transProb_of_not_mem_of_mem hG hx hy]
    · rw [G.transProb_of_not_mem_of_not_mem hG hx hy,
        harmonicMeasure_eq_zero_of_notMem G hG hGn hy x]

end OneStepAt

/-! ### The embedded chain and its cylinder probabilities -/

omit mΩ in
lemma stepTime_le_succ (Gn : Finset V) (j : ℕ) (ω : Ω) :
    stepTime X Gn j ω ≤ stepTime X Gn (j + 1) ω := le_nextStep Gn _ ω

omit mΩ in
/-- The times `tⁿ_j` of (3.31) increase in `j`. -/
lemma stepTime_mono (Gn : Finset V) {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    stepTime X Gn j ω ≤ stepTime X Gn k ω := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (stepTime_le_succ Gn _ ω)

/-- `{τ < ∞}` belongs to the stopped σ-algebra of `τ`. -/
lemma aemeasurableSetStopped_ne_top {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsAEStoppingTime ℱ P τ) : AEMeasurableSetStopped ℱ P τ {ω | τ ω ≠ ⊤} := by
  intro t
  obtain ⟨G, hG, hGe⟩ := hτ t
  refine ⟨G, hG, ?_⟩
  have hset : {ω | τ ω ≠ ⊤} ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} = {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_right_iff_imp]
    intro hle htop
    rw [htop] at hle
    exact WithTop.not_top_le_coe t hle
  rw [hset]
  exact hGe

/-- The event `{τ < ∞, X_τ = x}` belongs to the stopped σ-algebra of `τ` (up to null sets). -/
lemma aemeasurableSetStopped_stopEvent [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ) (x : V) :
    AEMeasurableSetStopped (naturalFiltration X hX) P τ (stopEvent X τ x) :=
  AEMeasurableSetStopped.inter (aemeasurableSetStopped_ne_top hτ)
    (aemeasurableSetStopped_stoppedValue_eq hX hii hR hτ x)

/-- The cylinder event of the embedded chain: `X̃_{tⁿ_i} = g i` (and `tⁿ_i < ∞`) for every
`i ≤ j`. -/
def embeddedCyl (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (g : ℕ → V) : ℕ → Set Ω
  | 0 => stopEvent X (stepTime X Gn 0) (g 0)
  | j + 1 => embeddedCyl X Gn g j ∩ stopEvent X (stepTime X Gn (j + 1)) (g (j + 1))

omit mΩ in
lemma embeddedCyl_subset (Gn : Finset V) (g : ℕ → V) (j : ℕ) :
    embeddedCyl X Gn g j ⊆ stopEvent X (stepTime X Gn j) (g j) := by
  cases j with
  | zero => exact subset_rfl
  | succ j => exact Set.inter_subset_right

omit mΩ in
lemma mem_embeddedCyl_iff (Gn : Finset V) (g : ℕ → V) (n : ℕ) (ω : Ω) :
    ω ∈ embeddedCyl X Gn g n ↔ ∀ j ≤ n, ω ∈ stopEvent X (stepTime X Gn j) (g j) := by
  induction n with
  | zero =>
    exact ⟨fun hω j hj => by rw [Nat.le_zero.1 hj]; exact hω, fun hω => hω 0 le_rfl⟩
  | succ n ih =>
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hlt | rfl
      · exact ih.1 h1 j (Nat.lt_succ_iff.1 hlt)
      · exact h2
    · intro hω
      exact ⟨ih.2 fun j hj => hω j (hj.trans (Nat.le_succ n)), hω (n + 1) le_rfl⟩

/-- The cylinder event of the embedded chain up to `j` belongs to the stopped σ-algebra of
`tⁿ_j` — it is an event of the past `{X̃_s}_{s ≤ tⁿ_j}`, as Lemma 3.10 requires. -/
lemma aemeasurableSetStopped_embeddedCyl [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V) (g : ℕ → V)
    (j : ℕ) :
    AEMeasurableSetStopped (naturalFiltration X hX) P (stepTime X Gn j)
      (embeddedCyl X Gn g j) := by
  induction j with
  | zero =>
    exact aemeasurableSetStopped_stopEvent hX hii hR
      (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn 0).1 (g 0)
  | succ j ih =>
    refine AEMeasurableSetStopped.inter
      (ih.mono (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn (j + 1)).1
        fun ω => stepTime_le_succ Gn j ω)
      (aemeasurableSetStopped_stopEvent hX hii hR
        (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn (j + 1)).1 (g (j + 1)))

section ChainLaw

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V]

open scoped Classical in
/-- **The law of the embedded chain, in cylinder form** (Section 3.4, Step 1, conclusion): for a
process satisfying (i)–(vi), the sequence `(X̃_{tⁿ_j})_{j ≥ 0}` of (3.31) has the
finite-dimensional distributions of the Markov chain `Yⁿ` started from `z` with the transition
probabilities `pₙ` of (3.2)–(3.3). -/
theorem measure_embeddedCyl (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty)
    (g : ℕ → V) (n : ℕ) :
    𝓧.P z (embeddedCyl 𝓧.X Gn g n) =
      (if g 0 = z then 1 else 0) *
        ∏ j ∈ Finset.range n, ENNReal.ofReal (G.transProb hG Gn (g j) (g (j + 1))) := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, mul_one]
    by_cases hgz : g 0 = z
    · rw [ite_eq_left hgz]
      have : 𝓧.P z (embeddedCyl 𝓧.X Gn g 0) = 𝓧.P z Set.univ := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [(h z).1] with ω hω
        simp only [Set.mem_univ, iff_true]
        refine ⟨WithTop.coe_ne_top, ?_⟩
        show 𝓧.X 0 ω = some (g 0)
        rw [hω, hgz]
      rw [this, measure_univ]
    · rw [ite_eq_right hgz]
      have hempty : 𝓧.P z (embeddedCyl 𝓧.X Gn g 0) = 𝓧.P z ∅ := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [(h z).1] with ω hω
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hmem
        have hval : 𝓧.X 0 ω = some (g 0) := hmem.2
        rw [hω] at hval
        exact hgz (Option.some_inj.1 hval).symm
      rw [hempty, measure_empty]
  | succ n ih =>
    have hsub : embeddedCyl 𝓧.X Gn g n ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn n) (g n) =
        embeddedCyl 𝓧.X Gn g n := Set.inter_eq_left.2 (embeddedCyl_subset Gn g n)
    have hstep := measure_stopEvent_succ_transProb h hG z hR hGn n (g n)
      (aemeasurableSetStopped_embeddedCyl 𝓧.measurable_X (h z).2.2.1 (hR z) Gn g n)
      (g (n + 1))
    rw [hsub] at hstep
    rw [show embeddedCyl 𝓧.X Gn g (n + 1) =
      embeddedCyl 𝓧.X Gn g n ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn (n + 1)) (g (n + 1)) from rfl,
      hstep, ih, Finset.prod_range_succ, mul_assoc]

end ChainLaw

/-! ### Stopping times are measurable for the stopped σ-algebra

The multi-step form of the recursion (3.31) needs the holding times
`Tⁿ_k = exitAfter tⁿ_k − tⁿ_k` of the *earlier* steps to be events of the past
`{X̃_s}_{s ≤ tⁿ_j}` for `j > k`.  That is the classical fact that a stopping time `τ ≤ σ` is
`𝓕_σ`-measurable, in the `P`-completed form used throughout this development. -/

section StoppedTime

variable {ℱ : Filtration ℝ≥0 mΩ} {σ τ ρ : Ω → WithTop ℝ≥0}

omit mΩ ℱ σ τ ρ in
/-- Truncated subtraction on `[0,∞]` is measurable. -/
lemma measurable_sub_withTop :
    Measurable fun p : WithTop ℝ≥0 × WithTop ℝ≥0 => p.1 - p.2 := by
  exact (measurable_fst.sub measurable_snd : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2)

/-- `τ` is measurable for the stopped σ-algebra `ℱ_σ` up to null sets: for every `t` there is
an `ℱ_t`-measurable `g` with `τ = g` almost surely on `{σ ≤ t}`.  The function-valued
companion of `AEMeasurableSetStopped`. -/
def AEStoppedTime (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (σ τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, ∃ g : Ω → WithTop ℝ≥0, Measurable[ℱ t] g ∧
    ∀ᵐ ω ∂P, σ ω ≤ (t : WithTop ℝ≥0) → τ ω = g ω

/-- A measurable function of two `ℱ_σ`-measurable times is `ℱ_σ`-measurable. -/
lemma AEStoppedTime.comp₂ (hτ : AEStoppedTime ℱ P σ τ) (hρ : AEStoppedTime ℱ P σ ρ)
    {F : WithTop ℝ≥0 → WithTop ℝ≥0 → WithTop ℝ≥0}
    (hF : Measurable fun p : WithTop ℝ≥0 × WithTop ℝ≥0 => F p.1 p.2) :
    AEStoppedTime ℱ P σ (fun ω => F (τ ω) (ρ ω)) := by
  intro t
  obtain ⟨g, hg, hge⟩ := hτ t
  obtain ⟨g', hg', hg'e⟩ := hρ t
  refine ⟨fun ω => F (g ω) (g' ω), hF.comp (hg.prodMk hg'), ?_⟩
  filter_upwards [hge, hg'e] with ω h1 h2 hσ
  show F (τ ω) (ρ ω) = F (g ω) (g' ω)
  rw [h1 hσ, h2 hσ]

/-- The event `{τ ∈ I}` for an `ℱ_σ`-measurable time `τ` lies in the stopped σ-algebra of
`σ` (up to null sets). -/
lemma AEStoppedTime.preimage (hτ : AEStoppedTime ℱ P σ τ) (hσ : IsAEStoppingTime ℱ P σ)
    {I : Set (WithTop ℝ≥0)} (hI : MeasurableSet I) :
    AEMeasurableSetStopped ℱ P σ {ω | τ ω ∈ I} := by
  intro t
  obtain ⟨g, hg, hge⟩ := hτ t
  obtain ⟨G, hG, hGe⟩ := hσ t
  refine ⟨g ⁻¹' I ∩ G, (hg hI).inter hG, Filter.eventuallyEqSet_iff.2 ?_⟩
  filter_upwards [hge, Filter.eventuallyEqSet_iff.1 hGe] with ω h1 h2
  constructor
  · rintro ⟨hmem, hle⟩
    refine ⟨?_, h2.1 hle⟩
    show g ω ∈ I
    rw [← h1 hle]
    exact hmem
  · rintro ⟨hmem, hGω⟩
    have hle : σ ω ≤ (t : WithTop ℝ≥0) := h2.2 hGω
    refine ⟨?_, hle⟩
    show τ ω ∈ I
    rw [h1 hle]
    exact hmem

open scoped Classical in
/-- **A stopping time is measurable for the stopped σ-algebra of any later stopping time.**
The `ℱ_t`-measurable version of `τ` on `{σ ≤ t}` is `min t (⨅ {d ∈ D, d ≤ t : τ ≤ d})`, built
from the countable dense set `denseTimes`. -/
lemma AEStoppedTime.of_le (hτ : IsAEStoppingTime ℱ P τ) (hle : ∀ ω, τ ω ≤ σ ω) :
    AEStoppedTime ℱ P σ τ := by
  classical
  have hc : Countable denseTimes := denseTimes_countable.to_subtype
  choose G hG hGe using hτ
  intro t
  refine ⟨fun ω => min (⨅ d : {d : denseTimes // (d.1 : ℝ≥0) ≤ t},
      if ω ∈ G d.1.1 then ((d.1.1 : ℝ≥0) : WithTop ℝ≥0) else ⊤)
      ((t : ℝ≥0) : WithTop ℝ≥0), ?_, ?_⟩
  · refine Measurable.min (Measurable.iInf fun d => ?_) measurable_const
    exact Measurable.ite (ℱ.mono' d.2 _ (hG d.1.1)) measurable_const measurable_const
  · filter_upwards [ae_all_iff.2 fun d : denseTimes =>
      Filter.eventuallyEqSet_iff.1 (hGe d.1)] with ω hω hσ
    set Q := ⨅ d : {d : denseTimes // (d.1 : ℝ≥0) ≤ t},
      if ω ∈ G d.1.1 then ((d.1.1 : ℝ≥0) : WithTop ℝ≥0) else ⊤ with hQ
    have hτt : τ ω ≤ ((t : ℝ≥0) : WithTop ℝ≥0) := (hle ω).trans hσ
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1
      (fun h => WithTop.not_top_le_coe t (h ▸ hτt))
    have hat : a ≤ t := by rw [← ha] at hτt; exact WithTop.coe_le_coe.1 hτt
    have hleQ : ((a : ℝ≥0) : WithTop ℝ≥0) ≤ Q := by
      refine le_iInf fun d => ?_
      by_cases hd : ω ∈ G d.1.1
      · have hd' : τ ω ≤ ((d.1.1 : ℝ≥0) : WithTop ℝ≥0) := (hω d.1).2 hd
        rw [← ha] at hd'
        simpa [hd] using hd'
      · rw [ite_eq_right hd]
        exact le_top
    refine le_antisymm ?_ ?_
    · rw [← ha]
      exact le_min hleQ (WithTop.coe_le_coe.2 hat)
    · rw [← ha]
      refine Theorem16.WithTop.le_coe_of_forall_lt fun c hc => ?_
      rcases lt_or_ge t c with hct | hct
      · exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 hct.le)
      · obtain ⟨d, hdD, had, hdc⟩ := denseTimes_dense.exists_between hc
        have hdt : d ≤ t := hdc.le.trans hct
        have hdG : ω ∈ G d := (hω ⟨d, hdD⟩).1 (by rw [← ha]; exact WithTop.coe_le_coe.2 had.le)
        have hterm : (if ω ∈ G d then ((d : ℝ≥0) : WithTop ℝ≥0) else ⊤) ≤
            ((c : ℝ≥0) : WithTop ℝ≥0) := by
          rw [ite_eq_left hdG]
          exact WithTop.coe_le_coe.2 hdc.le
        exact (min_le_left _ _).trans
          ((iInf_le _ (⟨⟨d, hdD⟩, hdt⟩ :
            {d : denseTimes // (d.1 : ℝ≥0) ≤ t})).trans hterm)

end StoppedTime

/-! ### The exit time from the current position, and the holding times `Tⁿ_j`

(3.31) defines `Tⁿ_j = min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}} − tⁿ_j`, i.e. `exitAfter tⁿ_j − tⁿ_j`.
It equals `tⁿ_{j+1} − tⁿ_j` when `X̃_{tⁿ_j} ∈ VGₙ` and is smaller otherwise; in both cases
`exitAfter tⁿ_j ≤ tⁿ_{j+1}`, so `Tⁿ_j` is an event of the past at `tⁿ_{j+1}`. -/

section ExitAfter

omit mΩ in
/-- A larger target is hit no later. -/
lemma hittingAfter_mono_target {S S' : Set (Option V)} (hSS' : S' ⊆ S) (t₀ : ℝ≥0) (ω : Ω) :
    hittingAfter X S t₀ ω ≤ hittingAfter X S' t₀ ω := by
  cases hB : hittingAfter X S' t₀ ω with
  | top => exact le_top
  | coe b =>
    refine Theorem16.WithTop.le_coe_of_forall_lt fun c hc => ?_
    have hlt : hittingAfter X S' t₀ ω < ((c : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hB]; exact WithTop.coe_lt_coe.2 hc
    obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt
    exact (hittingAfter_le_of_mem hj.1 (hSS' hjS)).trans (WithTop.coe_le_coe.2 hj.2.le)

omit mΩ in
/-- A larger target is hit no later, for a random start. -/
lemma hitAfter_mono_target {S S' : Set (Option V)} (hSS' : S' ⊆ S) (σ : Ω → WithTop ℝ≥0)
    (ω : Ω) : hitAfter X S σ ω ≤ hitAfter X S' σ ω := by
  cases h : σ ω with
  | top =>
    have h1 : hitAfter X S σ ω = ⊤ := hitAfter_top h
    have h2 : hitAfter X S' σ ω = ⊤ := hitAfter_top h
    exact le_of_eq (h1.trans h2.symm)
  | coe t₀ =>
    have h1 : hitAfter X S σ ω = hittingAfter X S t₀ ω := hitAfter_coe h
    have h2 : hitAfter X S' σ ω = hittingAfter X S' t₀ ω := hitAfter_coe h
    rw [h1, h2]
    exact hittingAfter_mono_target hSS' t₀ ω

omit mΩ in
/-- **The exit from the current position happens no later than the next time of (3.31).**
Equality when `X̃_σ ∈ VGₙ`; when `X̃_σ ∉ VGₙ` the next time of (3.31) is the hitting of `VGₙ`,
whose target is contained in `{s ≠ X̃_σ}`. -/
lemma exitAfter_le_nextStep (Gn : Finset V) (σ : Ω → WithTop ℝ≥0) (ω : Ω) :
    exitAfter X σ ω ≤ nextStep X Gn σ ω := by
  by_cases hmem : stoppedValue X σ ω ∈ some '' (Gn : Set V)
  · obtain ⟨x, hxG, hxω⟩ := hmem
    have hval : stoppedValue X σ ω = some x := hxω.symm
    have h1 : exitAfter X σ ω = nextStep X Gn σ ω := by
      rw [exitAfter, hval, nextStep_eq_of_eq (Finset.mem_coe.1 hxG) hval]
    exact le_of_eq h1
  · have h1 : exitAfter X σ ω = hitAfter X {s : Option V | s ≠ stoppedValue X σ ω} σ ω := rfl
    rw [h1, nextStep_eq_of_notMem hmem]
    refine hitAfter_mono_target (fun s hs => ?_) σ ω
    show s ≠ stoppedValue X σ ω
    intro hcontra
    exact hmem (hcontra ▸ hs)

omit mΩ in
/-- `exitAfter tⁿ_j ≤ tⁿ_{j+1}`, the first half of "`Tⁿ_j = tⁿ_{j+1} − tⁿ_j` if
`X̃_{tⁿ_j} ∈ Gₙ`, and `Tⁿ_j` could be strictly smaller otherwise" (p. 26). -/
lemma exitAfter_le_stepTime_succ (Gn : Finset V) (j : ℕ) (ω : Ω) :
    exitAfter X (stepTime X Gn j) ω ≤ stepTime X Gn (j + 1) ω :=
  exitAfter_le_nextStep Gn (stepTime X Gn j) ω

/-- `Ω` itself is in the stopped σ-algebra of a stopping time. -/
lemma aemeasurableSetStopped_univ {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsAEStoppingTime ℱ P τ) : AEMeasurableSetStopped ℱ P τ Set.univ := by
  intro t
  obtain ⟨G, hG, hGe⟩ := hτ t
  exact ⟨G, hG, by rwa [Set.univ_inter]⟩

/-- `{τ < ∞, X_τ = x}` is null-measurable for an a.e.-measurable `τ`. -/
lemma nullMeasurableSet_stopEvent' [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) {τ : Ω → WithTop ℝ≥0}
    (hτm : AEMeasurable τ P) (x : V) : NullMeasurableSet (stopEvent X τ x) P := by
  refine (nullMeasurableSet_stopEvent hX hii hR hτm.measurable_mk x).congr
    (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hτm.ae_eq_mk] with ω hω
  simp only [stopEvent, Set.mem_ofPred_eq, stoppedValue, hω]

/-- **The exit time from the current position is a stopping time up to null sets.**  As for
`isAEStoppingTime_nextStep`, the proof splits over the (countably many) values of `X̃_σ`; the
hypothesis `hval` says that `X̃_σ` is almost surely a vertex, which is what makes each branch an
admissible target `{s ≠ x}`. -/
theorem isAEStoppingTime_exitAfter [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsAEStoppingTime (naturalFiltration X hX) P σ)
    (hval : ∀ᵐ ω ∂P, ∃ x : V, stoppedValue X σ ω = some x) :
    IsAEStoppingTime (naturalFiltration X hX) P (exitAfter X σ) := by
  classical
  have hx : ∀ x : V, AEMeasurableSetStopped (naturalFiltration X hX) P σ
      {ω | stoppedValue X σ ω = some x} :=
    aemeasurableSetStopped_stoppedValue_eq hX hii hR hσ
  have hexit : ∀ x : V, IsAEStoppingTime (naturalFiltration X hX) P
      (hitAfter X {s : Option V | s ≠ some x} σ) := fun x =>
    isAEStoppingTime_hitAfter hX hii hR (admissibleTarget_ne x) hσ
  intro t
  choose Gx hGx hGxe using fun x : V => (hx x).mono (hexit x) (fun ω => le_hitAfter ω) t
  choose Hx hHx hHxe using fun x : V => hexit x t
  refine ⟨⋃ x : V, Gx x ∩ Hx x, MeasurableSet.iUnion fun x => (hGx x).inter (hHx x), ?_⟩
  have hdecomp : {ω | exitAfter X σ ω ≤ (t : WithTop ℝ≥0)} =ᵐ[P]
      ⋃ x : V, ({ω | stoppedValue X σ ω = some x} ∩
          {ω | hitAfter X {s : Option V | s ≠ some x} σ ω ≤ (t : WithTop ℝ≥0)}) ∩
        {ω | hitAfter X {s : Option V | s ≠ some x} σ ω ≤ (t : WithTop ℝ≥0)} := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hval] with ω hω
    obtain ⟨x, hxω⟩ := hω
    have hE : exitAfter X σ ω = hitAfter X {s : Option V | s ≠ some x} σ ω := by
      rw [exitAfter, hxω]
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, hE]
    constructor
    · intro hle
      exact ⟨x, ⟨hxω, hle⟩, hle⟩
    · rintro ⟨y, ⟨hyω, hy⟩, -⟩
      have hxy : y = x := Option.some_inj.1 (hyω.symm.trans hxω)
      subst hxy
      exact hy
  exact hdecomp.trans
    (EventuallyEqSet.countable_iUnion fun x => ae_eq_set_inter (hGxe x) (hHxe x))

end ExitAfter

/-! ### The embedded chain is everywhere defined

Before the embedded chain `(X̃_{tⁿ_j})_j` can be read as a random element of `VG^ℕ`, the times
`tⁿ_j` must be finite and the positions vertices.  That is a consequence of the one-step law
already proved: the rows of (3.2)–(3.3) are probability vectors. -/

/-- The event "`tⁿ_j < ∞` and `X̃_{tⁿ_j}` is a vertex". -/
def definedAt (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) : Set Ω :=
  ⋃ x : V, stopEvent X (stepTime X Gn j) x

omit mΩ in
lemma mem_definedAt_iff (Gn : Finset V) (j : ℕ) (ω : Ω) :
    ω ∈ definedAt X Gn j ↔ stepTime X Gn j ω ≠ ⊤ ∧
      ∃ x : V, stoppedValue X (stepTime X Gn j) ω = some x := by
  simp only [definedAt, Set.mem_iUnion, stopEvent, Set.mem_ofPred_eq]
  exact ⟨fun ⟨x, h1, h2⟩ => ⟨h1, x, h2⟩, fun ⟨h1, x, h2⟩ => ⟨x, h1, h2⟩⟩

omit mΩ in
/-- Distinct positions give disjoint events. -/
lemma disjoint_stopEvent {τ : Ω → WithTop ℝ≥0} {x y : V} (hxy : x ≠ y) :
    Disjoint (stopEvent X τ x) (stopEvent X τ y) :=
  Set.disjoint_left.2 fun _ hω hω' => hxy (Option.some_inj.1 (hω.2.symm.trans hω'.2))

section Defined

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V]

lemma nullMeasurableSet_stopEvent_stepTime (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : RightContinuousAtInfty (𝓧.P z) 𝓧.X) (Gn : Finset V) (j : ℕ) (x : V) :
    NullMeasurableSet (stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) (𝓧.P z) :=
  nullMeasurableSet_stopEvent' 𝓧.measurable_X (h z).2.2.1 hR
    (stepTime_isAEStoppingTime_aemeasurable 𝓧.measurable_X (h z).2.2.1 hR Gn j).2 x

omit [Countable V] in
/-- The rows of (3.2)–(3.3) are probability vectors, in `[0,∞]`. -/
lemma tsum_ofReal_transProb [Nontrivial V] (hG : G.toSimpleGraph.Connected) {Gn : Finset V}
    (hGn : Gn.Nonempty) (x : V) :
    ∑' y : V, ENNReal.ofReal (G.transProb hG Gn x y) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => G.transProb_nonneg hG hGn x y)
    (G.summable_transProb hG Gn x), G.tsum_transProb hG hGn x, ENNReal.ofReal_one]

variable [Nontrivial V]

/-- **The embedded chain is everywhere defined.**  Almost surely `tⁿ_j < ∞` and
`X̃_{tⁿ_j} ∈ VG`, for every `j`.  Induction on `j` from the one-step law
`measure_stopEvent_succ_transProb` and `∑_y pₙ(x,y) = 1`. -/
theorem measure_definedAt_eq_one (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty)
    (j : ℕ) : 𝓧.P z (definedAt 𝓧.X Gn j) = 1 := by
  have hnull : ∀ (k : ℕ) (x : V),
      NullMeasurableSet (stopEvent 𝓧.X (stepTime 𝓧.X Gn k) x) (𝓧.P z) := fun k x =>
    nullMeasurableSet_stopEvent_stepTime h z (hR z) Gn k x
  induction j with
  | zero =>
    have hset : definedAt 𝓧.X Gn 0 =ᵐ[𝓧.P z] (Set.univ : Set 𝓧.Ω) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [(h z).1] with ω hω
      simp only [Set.mem_univ, iff_true, definedAt, Set.mem_iUnion]
      exact ⟨z, WithTop.coe_ne_top, hω⟩
    rw [measure_congr hset, measure_univ]
  | succ j ih =>
    have hnullj : NullMeasurableSet (definedAt 𝓧.X Gn (j + 1)) (𝓧.P z) :=
      NullMeasurableSet.iUnion fun y => hnull (j + 1) y
    have hfib : ∀ x : V, 𝓧.P z (stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
        definedAt 𝓧.X Gn (j + 1)) = 𝓧.P z (stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) := by
      intro x
      have hstep : ∀ y : V, 𝓧.P z (stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
          stopEvent 𝓧.X (stepTime 𝓧.X Gn (j + 1)) y) =
          𝓧.P z (stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) *
            ENNReal.ofReal (G.transProb hG Gn x y) := by
        intro y
        have hmain := measure_stopEvent_succ_transProb h hG z hR hGn j x
          (F := (Set.univ : Set 𝓧.Ω))
          (aemeasurableSetStopped_univ
            (stepTime_isAEStoppingTime_aemeasurable 𝓧.measurable_X (h z).2.2.1 (hR z) Gn j).1) y
        rwa [Set.univ_inter] at hmain
      rw [definedAt, Set.inter_iUnion,
        measure_iUnion₀
          (fun y y' hyy' => ((disjoint_stopEvent hyy').mono Set.inter_subset_right
            Set.inter_subset_right).aedisjoint)
          fun y => (hnull j x).inter (hnull (j + 1) y)]
      simp_rw [hstep]
      rw [ENNReal.tsum_mul_left, tsum_ofReal_transProb hG hGn x, mul_one]
    have hae : ∀ᵐ ω ∂𝓧.P z, ω ∈ definedAt 𝓧.X Gn j := by
      have hnj : NullMeasurableSet (definedAt 𝓧.X Gn j) (𝓧.P z) :=
        NullMeasurableSet.iUnion fun x => hnull j x
      have h1 : 𝓧.P z (definedAt 𝓧.X Gn j) + 𝓧.P z (definedAt 𝓧.X Gn j)ᶜ = 1 := by
        rw [measure_add_measure_compl₀ hnj, measure_univ]
      rw [ih] at h1
      have hc : 𝓧.P z (definedAt 𝓧.X Gn j)ᶜ = 0 := by
        by_contra hne
        have hlt : (1 : ℝ≥0∞) < 1 + 𝓧.P z (definedAt 𝓧.X Gn j)ᶜ :=
          ENNReal.lt_add_right (by norm_num) hne
        rw [h1] at hlt
        exact absurd hlt (lt_irrefl 1)
      rw [ae_iff]
      exact hc
    have hsplit : definedAt 𝓧.X Gn (j + 1) =ᵐ[𝓧.P z]
        ⋃ x : V, (stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩ definedAt 𝓧.X Gn (j + 1)) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hae] with ω hω
      rw [← Set.iUnion_inter]
      show ω ∈ definedAt 𝓧.X Gn (j + 1) ↔ ω ∈ definedAt 𝓧.X Gn j ∩ definedAt 𝓧.X Gn (j + 1)
      simp only [Set.mem_inter_iff, hω, true_and]
    rw [measure_congr hsplit, measure_iUnion₀
      (fun x x' hxx' => ((disjoint_stopEvent hxx').mono Set.inter_subset_left
        Set.inter_subset_left).aedisjoint)
      fun x => (hnull j x).inter hnullj]
    simp_rw [hfib]
    rw [← measure_iUnion₀ (fun x x' hxx' => (disjoint_stopEvent hxx').aedisjoint)
      fun x => hnull j x]
    exact ih

/-- Almost surely `tⁿ_j < ∞` and `X̃_{tⁿ_j} ∈ VG` for **every** `j` simultaneously. -/
theorem ae_forall_definedAt (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ x, RightContinuousAtInfty (𝓧.P x) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty) :
    ∀ᵐ ω ∂𝓧.P z, ∀ j : ℕ, ω ∈ definedAt 𝓧.X Gn j := by
  refine ae_all_iff.2 fun j => ?_
  have hnj : NullMeasurableSet (definedAt 𝓧.X Gn j) (𝓧.P z) :=
    NullMeasurableSet.iUnion fun x =>
      nullMeasurableSet_stopEvent_stepTime h z (hR z) Gn j x
  have h1 : 𝓧.P z (definedAt 𝓧.X Gn j) + 𝓧.P z (definedAt 𝓧.X Gn j)ᶜ = 1 := by
    rw [measure_add_measure_compl₀ hnj, measure_univ]
  rw [measure_definedAt_eq_one h hG z hR hGn j] at h1
  have hc : 𝓧.P z (definedAt 𝓧.X Gn j)ᶜ = 0 := by
    by_contra hne
    have hlt : (1 : ℝ≥0∞) < 1 + 𝓧.P z (definedAt 𝓧.X Gn j)ᶜ :=
      ENNReal.lt_add_right (by norm_num) hne
    rw [h1] at hlt
    exact absurd hlt (lt_irrefl 1)
  rw [ae_iff]
  exact hc

end Defined

/-! ### The holding time and the next position, as one measurable path event

The paper's sentence "on the event `{X̃_{tⁿ_j} = x}`, the random variables `X̃_{tⁿ_{j+1}}` and
`Tⁿ_j` are conditionally independent given `{X̃_s}_{s ≤ tⁿ_j}`, and the conditional law of `Tⁿ_j`
is exponential with parameter `w(x)`" requires the *pair* `(Tⁿ_j, X̃_{tⁿ_{j+1}})` to be read off
the future trajectory at `tⁿ_j`.  `nextEvent` constrains `tⁿ_{j+1} − tⁿ_j`; `stepPairEvent`
constrains `Tⁿ_j` instead, which is what (3.32) uses and what differs from `tⁿ_{j+1} − tⁿ_j`
when `x ∈ B₁Gₙ \ Gₙ`. -/

omit mΩ in
/-- Hitting times are monotone in the start time. -/
lemma hittingAfter_mono_start {S : Set (Option V)} {a b : ℝ≥0} (hab : a ≤ b) (ω : Ω) :
    hittingAfter X S a ω ≤ hittingAfter X S b ω := by
  cases hB : hittingAfter X S b ω with
  | top => exact le_top
  | coe c₀ =>
    refine Theorem16.WithTop.le_coe_of_forall_lt fun c hc => ?_
    have hlt : hittingAfter X S b ω < ((c : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hB]; exact WithTop.coe_lt_coe.2 hc
    obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt
    exact (hittingAfter_le_of_mem (hab.trans hj.1) hjS).trans (WithTop.coe_le_coe.2 hj.2.le)

omit mΩ in
/-- If the target is avoided before `a`, starting the clock at `a` changes nothing. -/
lemma hittingAfter_eq_zero_of_notMem_lt {S : Set (Option V)} {a : ℝ≥0} {ω : Ω}
    (h : ∀ s : ℝ≥0, s < a → X s ω ∉ S) :
    hittingAfter X S a ω = hittingAfter X S 0 ω := by
  refine le_antisymm ?_ (hittingAfter_mono_start (by simp) ω)
  cases hA : hittingAfter X S 0 ω with
  | top => exact le_top
  | coe c₀ =>
    refine Theorem16.WithTop.le_coe_of_forall_lt fun c hc => ?_
    have hlt : hittingAfter X S 0 ω < ((c : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hA]; exact WithTop.coe_lt_coe.2 hc
    obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.1 hlt
    have haj : a ≤ j := not_lt.1 fun hja => h j hja hjS
    exact (hittingAfter_le_of_mem haj hjS).trans (WithTop.coe_le_coe.2 hj.2.le)

omit mΩ in
/-- Before the exit time the process sits at the vertex it is exiting. -/
lemma eq_of_lt_exitTime {z : V} {ω : Ω} {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < exitTime X z ω) : X s ω = some z := by
  by_contra hne
  exact absurd (hittingAfter_le_of_mem (by simp) hne) (not_le.2 hs)

omit mΩ in
/-- **The holding time read on the future trajectory.**  For an admissible target, the waiting
time `hitAfter S σ − σ` is the hitting time of `S` computed on the shifted trajectory. -/
lemma sub_hitAfter_eq_hittingAfter_shift {S : Set (Option V)} (hS : AdmissibleTarget S) {ω : Ω}
    (hω : RightRegularAt X ω) {σ : Ω → WithTop ℝ≥0} {a : ℝ≥0} (ha : σ ω = a) :
    hitAfter X S σ ω - σ ω = hittingAfter (evalProc V) S 0 (shiftedPath X a ω) := by
  cases hr : hittingAfter (evalProc V) S 0 (shiftedPath X a ω) with
  | top =>
    have h1 : hitAfter X S σ ω = ⊤ := by
      rw [hitAfter_coe ha]
      exact (hittingAfter_shift_eq_top_iff S a ω).2 hr
    rw [h1, ha]
    rfl
  | coe r =>
    have h1 : hitAfter X S σ ω = ((r + a : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hitAfter_coe ha]
      exact hittingAfter_shift_eq hS hω hr
    rw [h1, ha, ← WithTop.coe_sub, add_tsub_cancel_right]

/-- The **measurable** set of trajectories "the holding time at the starting position lies in
`I`, and the step of (3.31) is finite and lands on the vertex `y`", built from the surrogate
`dhit`. -/
noncomputable def stepPairEvent (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V) :
    Set (Trajectory V) :=
  ⋃ a : Option V, {f : Trajectory V | f 0 = a} ∩
    ({f | dhit {s : Option V | s ≠ a} f ∈ I} ∩
      ({f | dhit (nextTarget Gn a ∩ {some y}) f = dhit (nextTarget Gn a) f} ∩
        {f | dhit (nextTarget Gn a) f ≠ ⊤}))

lemma measurableSet_stepPairEvent [Countable V] (Gn : Finset V) {I : Set (WithTop ℝ≥0)}
    (hI : MeasurableSet I) (y : V) : MeasurableSet (stepPairEvent (V := V) Gn I y) := by
  refine MeasurableSet.iUnion fun a => ?_
  refine MeasurableSet.inter (measurable_evalProc 0 (measurableSet_option {a})) ?_
  refine MeasurableSet.inter (measurable_dhit _ hI) ?_
  exact (measurableSet_eq_fun (measurable_dhit _) (measurable_dhit _)).inter
    (measurable_dhit _ (measurableSet_singleton (⊤ : WithTop ℝ≥0)).compl)

lemma mem_stepPairEvent_iff' (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V)
    (f : Trajectory V) :
    f ∈ stepPairEvent Gn I y ↔
      (dhit {s : Option V | s ≠ f 0} f ∈ I ∧
        (dhit (nextTarget Gn (f 0) ∩ {some y}) f = dhit (nextTarget Gn (f 0)) f ∧
          dhit (nextTarget Gn (f 0)) f ≠ ⊤)) := by
  constructor
  · rintro ⟨-, ⟨a, rfl⟩, hfa, hrest⟩
    have hfa' : f 0 = a := hfa
    rw [hfa']
    exact hrest
  · intro hrest
    exact Set.mem_iUnion.2 ⟨f 0, rfl, hrest⟩

/-- At a right-regular trajectory whose starting position has an admissible exit target,
`stepPairEvent` is the true event. -/
lemma mem_stepPairEvent_iff (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V)
    {f : Trajectory V} (hf : RightRegularAt (evalProc V) f)
    (hadm : AdmissibleTarget {s : Option V | s ≠ f 0}) :
    f ∈ stepPairEvent Gn I y ↔
      (hittingAfter (evalProc V) {s : Option V | s ≠ f 0} 0 f ∈ I ∧
        trajNext Gn f ≠ ⊤ ∧ f (trajNext Gn f).untopA = some y) := by
  rw [mem_stepPairEvent_iff' Gn I y f,
    dhit_inter_iff (admissibleTarget_nextTarget Gn (f 0)) hf y,
    dhit_eq_hittingAfter hadm hf]
  exact ⟨fun hh => ⟨hh.1, hh.2.1, hh.2.2⟩, fun hh => ⟨hh.1, hh.2.1, hh.2.2⟩⟩

omit mΩ in
/-- The position after the step of (3.31), read on the future trajectory. -/
lemma trajNext_futureAt_iff {σ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : RightRegularAt X ω)
    (Gn : Finset V) (y : V) {a : ℝ≥0} (ha : σ ω = a) :
    (trajNext Gn (shiftedPath X a ω) ≠ ⊤ ∧
        shiftedPath X a ω (trajNext Gn (shiftedPath X a ω)).untopA = some y) ↔
      (nextStep X Gn σ ω ≠ ⊤ ∧ stoppedValue X (nextStep X Gn σ) ω = some y) := by
  have h2 := mem_nextEvent_futureAt_iff hω Gn (Set.univ : Set (WithTop ℝ≥0)) y ha
  rw [futureAt_of_eq ha,
    mem_nextEvent_iff Gn (Set.univ : Set (WithTop ℝ≥0)) y
      (rightRegularAt_shiftedPath hω a)] at h2
  simpa using h2

omit mΩ in
/-- **One step of (3.31) with its holding time, as an event of the future trajectory.** -/
lemma mem_stepPairEvent_futureAt_iff {σ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : RightRegularAt X ω)
    (Gn : Finset V) (I : Set (WithTop ℝ≥0)) (y : V) {a : ℝ≥0} (ha : σ ω = a)
    (hadm : AdmissibleTarget {s : Option V | s ≠ stoppedValue X σ ω}) :
    futureAt X σ ω ∈ stepPairEvent Gn I y ↔
      (exitAfter X σ ω - σ ω ∈ I ∧ nextStep X Gn σ ω ≠ ⊤ ∧
        stoppedValue X (nextStep X Gn σ) ω = some y) := by
  have hf0 : shiftedPath X a ω 0 = stoppedValue X σ ω := by
    show X (0 + a) ω = stoppedValue X σ ω
    rw [zero_add, stoppedValue_of_eq ha]
  have hfreg : RightRegularAt (evalProc V) (shiftedPath X a ω) :=
    rightRegularAt_shiftedPath hω a
  have hadm' : AdmissibleTarget {s : Option V | s ≠ shiftedPath X a ω 0} := by
    rw [hf0]; exact hadm
  have hexit : exitAfter X σ ω - σ ω =
      hittingAfter (evalProc V) {s : Option V | s ≠ shiftedPath X a ω 0} 0
        (shiftedPath X a ω) := by
    rw [hf0]
    exact sub_hitAfter_eq_hittingAfter_shift hadm hω ha
  rw [futureAt_of_eq ha, mem_stepPairEvent_iff Gn I y hfreg hadm', hexit]
  exact and_congr Iff.rfl (trajNext_futureAt_iff hω Gn y ha)

/-! ### Property (vi) with the holding time: the re-entry step of (3.31)

For `x ∈ B₁Gₙ \ Gₙ` the step of (3.31) is the hitting of `VGₙ`, which happens at or after the
exit from `x`.  The independence of the holding time from the re-entry position is therefore not
property (iii) alone: it needs the strong Markov property at the exit time as well.  Summing the
strong Markov identity over the exit position `v` and comparing with `I = [0,∞]` expresses the
joint law as the product of the exponential law and `P_x(X̃ hits `VGₙ` at `y`)`, and the latter is
harmonic measure by property (vi). -/

/-- The **measurable** set of trajectories "`VGₙ` is hit in finite time, at the vertex `y`". -/
noncomputable def hitEvent (Gn : Finset V) (y : V) : Set (Trajectory V) :=
  {f : Trajectory V |
      dhit (some '' (Gn : Set V) ∩ {some y}) f = dhit (some '' (Gn : Set V)) f} ∩
    {f | dhit (some '' (Gn : Set V)) f ≠ ⊤}

lemma measurableSet_hitEvent [Countable V] (Gn : Finset V) (y : V) :
    MeasurableSet (hitEvent (V := V) Gn y) :=
  (measurableSet_eq_fun (measurable_dhit _) (measurable_dhit _)).inter
    (measurable_dhit _ (measurableSet_singleton (⊤ : WithTop ℝ≥0)).compl)

lemma mem_hitEvent_iff (Gn : Finset V) (y : V) {f : Trajectory V}
    (hf : RightRegularAt (evalProc V) f) :
    f ∈ hitEvent Gn y ↔
      (hittingAfter (evalProc V) (some '' (Gn : Set V)) 0 f ≠ ⊤ ∧
        stoppedValue (evalProc V) (hittingAfter (evalProc V) (some '' (Gn : Set V)) 0) f =
          some y) :=
  dhit_inter_iff (admissibleTarget_image Gn) hf y

omit mΩ in
lemma mem_hitEvent_futureAt_iff {σ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : RightRegularAt X ω)
    (Gn : Finset V) (y : V) {a : ℝ≥0} (ha : σ ω = a) :
    futureAt X σ ω ∈ hitEvent Gn y ↔
      (hittingAfter X (some '' (Gn : Set V)) a ω ≠ ⊤ ∧
        stoppedValue X (hittingAfter X (some '' (Gn : Set V)) a) ω = some y) := by
  rw [futureAt_of_eq ha, mem_hitEvent_iff Gn y (rightRegularAt_shiftedPath hω a)]
  exact (stopEvent_shift_iff (admissibleTarget_image Gn) hω a y).symm

/-- Preimages under an a.e.-measurable map are null-measurable. -/
lemma nullMeasurableSet_preimage_of_aemeasurable {α : Type*} [MeasurableSpace α]
    {f : Ω → α} (hf : AEMeasurable f P) {s : Set α} (hs : MeasurableSet s) :
    NullMeasurableSet (f ⁻¹' s) P := by
  refine ((hf.measurable_mk hs).nullMeasurableSet).congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hf.ae_eq_mk] with ω hω
  simp only [Set.mem_preimage, hω]

/-- A set of full measure contains almost every outcome. -/
lemma ae_mem_of_measure_eq_one [IsProbabilityMeasure P] {s : Set Ω}
    (hs : NullMeasurableSet s P) (h1 : P s = 1) : ∀ᵐ ω ∂P, ω ∈ s := by
  have h2 : P s + P sᶜ = 1 := by rw [measure_add_measure_compl₀ hs, measure_univ]
  rw [h1] at h2
  have hc : P sᶜ = 0 := by
    by_contra hne
    have hlt : (1 : ℝ≥0∞) < 1 + P sᶜ := ENNReal.lt_add_right (by norm_num) hne
    rw [h2] at hlt
    exact absurd hlt (lt_irrefl 1)
  rw [ae_iff]
  exact hc

omit mΩ in
/-- At time `0` the exit from the current position is the exit time of property (iii). -/
lemma exitAfter_stepTime_zero {Gn : Finset V} {ω : Ω} {x : V}
    (hval : stoppedValue X (stepTime X Gn 0) ω = some x) :
    exitAfter X (stepTime X Gn 0) ω = exitTime X x ω := by
  have h1 : exitAfter X (stepTime X Gn 0) ω =
      hitAfter X {s : Option V | s ≠ some x} (stepTime X Gn 0) ω := by
    rw [exitAfter, hval]
  have h2 : hitAfter X {s : Option V | s ≠ some x} (stepTime X Gn 0) ω =
      hittingAfter X {s : Option V | s ≠ some x} 0 ω :=
    hitAfter_coe (stepTime_zero_apply (X := X) Gn ω)
  have h3 : exitTime X x ω = hittingAfter X {s : Option V | s ≠ some x} 0 ω := rfl
  rw [h1, h2, h3]

section Reentry

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V] [Nontrivial V]

omit [Countable V] in
/-- The one-step law of the random walk is a probability vector, in `[0,∞]`. -/
lemma tsum_ofReal_step (hG : G.toSimpleGraph.Connected) (x : V) :
    ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun v => div_nonneg (G.c_nonneg x v) (G.pi_nonneg x)) ((G.summable_c x).div_const _),
    tsum_div_const, show ∑' v, G.c x v = G.pi x from rfl,
    div_self (G.pi_pos_of_connected hG x).ne', ENNReal.ofReal_one]

/-- By property (iii) the exit position is almost surely a vertex. -/
lemma ae_exists_stoppedValue_exitTime (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (x : V) :
    ∀ᵐ ω ∂𝓧.P x, ∃ v : V, stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v := by
  obtain ⟨-, hZ, -, -, hval⟩ := (h x).2.2.2.2.1
  have hnull : ∀ v : V,
      NullMeasurableSet {ω | stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v} (𝓧.P x) := by
    intro v
    refine ((hZ.measurable_mk (measurableSet_option {some v})).nullMeasurableSet).congr
      (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hZ.ae_eq_mk] with ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hω]
  have hdisj : ∀ v v' : V, v ≠ v' →
      Disjoint {ω : 𝓧.Ω | stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v}
        {ω : 𝓧.Ω | stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v'} := by
    intro v v' hvv'
    refine Set.disjoint_left.2 fun ω hω hω' => hvv' ?_
    have h1 : stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v := hω
    have h2 : stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v' := hω'
    exact Option.some_inj.1 (h1.symm.trans h2)
  have hsum : 𝓧.P x (⋃ v : V, {ω | stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v}) = 1 := by
    rw [measure_iUnion₀
      (f := fun v : V => {ω : 𝓧.Ω | stoppedValue 𝓧.X (exitTime 𝓧.X x) ω = some v})
      (fun v v' hvv' => (hdisj v v' hvv').aedisjoint) hnull]
    exact (tsum_congr fun v => hval v).trans (tsum_ofReal_step hG x)
  have hae := ae_mem_of_measure_eq_one (NullMeasurableSet.iUnion hnull) hsum
  filter_upwards [hae] with ω hω
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hω
  exact ⟨v, hv⟩

omit [Nontrivial V] in
/-- The law of `hitEvent` is property (vi)'s harmonic measure. -/
lemma law_hitEvent (h : IsReflectedWalk G w hmin 𝓧) (hG : G.toSimpleGraph.Connected) (v : V)
    (hR : RightContinuousAtInfty (𝓧.P v) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty) (y : V) :
    𝓧.law v (hitEvent Gn y) = ENNReal.ofReal (G.harmonicMeasure hG Gn v y) := by
  rw [ProcessFamily.law,
    Measure.map_apply 𝓧.measurable_trajectory (measurableSet_hitEvent Gn y),
    ← measure_stoppedValue_hittingTime h hG v hR hGn y]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_rightRegularAt (h v).2.2.1 hR, ((h v).2.2.2.2.2.2.2 Gn hGn).1] with ω hω hfin
  have hfut : futureAt 𝓧.X (stepTime 𝓧.X Gn 0) ω = 𝓧.trajectory ω := by
    rw [futureAt_of_eq (stepTime_zero_apply Gn ω), shiftedPath_zero]
    rfl
  have hiff := mem_hitEvent_futureAt_iff hω Gn y (stepTime_zero_apply (X := 𝓧.X) Gn ω)
  rw [hfut] at hiff
  simp only [Set.mem_preimage]
  rw [hiff]
  exact ⟨fun hh => hh.2, fun hh => ⟨hfin.1, hh⟩⟩

/-- **Property (vi) with the holding time** (Section 3.4, Step 1, the re-entry step): for
`x ∈ B₁Gₙ \ Gₙ` the holding time at `x` and the re-entry position are independent under `P_x`,
the holding time being exponential with parameter `w(x)` and the position having the harmonic
measure law `hm^x_{VGₙ}`.

The paper reads this off property (iii), but the step of (3.31) from `x ∉ Gₙ` is the *hitting of
`VGₙ`*, which happens at or after the exit from `x`: the independence therefore needs the strong
Markov property (Lemma 3.10) at the exit time as well.  Summing that identity over the exit
position and comparing with `I = [0,∞]` turns the joint law into the product of the exponential
law and `P_x(X̃` hits `VGₙ` at `y)`, and property (vi) identifies the latter as harmonic
measure. -/
theorem measure_exitTime_hitting_of_notMem (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X)
    {Gn : Finset V} (hGn : Gn.Nonempty) {x : V} (hx : x ∉ Gn)
    {I : Set (WithTop ℝ≥0)} (hI : MeasurableSet I) (y : V) :
    𝓧.P x {ω | exitTime 𝓧.X x ω ∈ I ∧ hittingTime 𝓧.X Gn ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω = some y} =
      ((ProbabilityTheory.expMeasure (w x)).map toWithTop) I *
        ENNReal.ofReal (G.harmonicMeasure hG Gn x y) := by
  classical
  have hii := (h x).2.2.1
  have hτm : AEMeasurable (exitTime 𝓧.X x) (𝓧.P x) :=
    aemeasurable_exitTime 𝓧.measurable_X hii (hR x) x
  have hτs : IsAEStoppingTime 𝓧.naturalFiltration (𝓧.P x) (exitTime 𝓧.X x) :=
    isAEStoppingTime_exitTime 𝓧.measurable_X hii (hR x) x
  have hfinτ : ∀ᵐ ω ∂𝓧.P x, exitTime 𝓧.X x ω ≠ ⊤ := by
    have h0 := measure_exitTime_eq_top h x
    rw [ae_iff]
    simpa using h0
  have hfutm : AEMeasurable (futureAt 𝓧.X (exitTime 𝓧.X x)) (𝓧.P x) := by
    refine (aemeasurable_futureAt 𝓧.measurable_X hii (hR x) hτm.measurable_mk).congr ?_
    filter_upwards [hτm.ae_eq_mk] with ω hω
    funext s
    simp only [futureAt, hω]
  have hhit : ∀ᵐ ω ∂𝓧.P x, hittingTime 𝓧.X Gn ω =
      hittingAfter 𝓧.X (some '' (Gn : Set V)) (exitTime 𝓧.X x ω).untopA ω := by
    filter_upwards [hfinτ] with ω hωfin
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hωfin
    have hua : (exitTime 𝓧.X x ω).untopA = a := by rw [← ha]; exact untopA_coe a
    rw [hua]
    refine (hittingAfter_eq_zero_of_notMem_lt fun s hs => ?_).symm
    have hsx : 𝓧.X s ω = some x := by
      refine eq_of_lt_exitTime ?_
      rw [← ha]
      exact WithTop.coe_lt_coe.2 hs
    rw [hsx]
    rintro ⟨v, hv, hvx⟩
    exact hx (Option.some_inj.1 hvx ▸ Finset.mem_coe.1 hv)
  have key : ∀ J : Set (WithTop ℝ≥0), MeasurableSet J →
      𝓧.P x {ω | exitTime 𝓧.X x ω ∈ J ∧ hittingTime 𝓧.X Gn ω ≠ ⊤ ∧
          stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω = some y} =
        ((ProbabilityTheory.expMeasure (w x)).map toWithTop) J *
          ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) *
            ENNReal.ofReal (G.harmonicMeasure hG Gn v y) := by
    intro J hJ
    have hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P x) (exitTime 𝓧.X x)
        {ω | exitTime 𝓧.X x ω ∈ J} :=
      (AEStoppedTime.of_le hτs (fun _ => le_rfl)).preimage hτs hJ
    have hSM : ∀ v : V, 𝓧.P x ({ω | exitTime 𝓧.X x ω ∈ J} ∩
        stopEvent 𝓧.X (exitTime 𝓧.X x) v ∩
          futureAt 𝓧.X (exitTime 𝓧.X x) ⁻¹' hitEvent Gn y) =
        𝓧.P x ({ω | exitTime 𝓧.X x ω ∈ J} ∩ stopEvent 𝓧.X (exitTime 𝓧.X x) v) *
          ENNReal.ofReal (G.harmonicMeasure hG Gn v y) := by
      intro v
      rw [strongMarkov_completed h x (hR x) hτm hτs v hF (measurableSet_hitEvent Gn y),
        law_hitEvent h hG v (hR v) hGn y]
    have hind : ∀ v : V, 𝓧.P x ({ω | exitTime 𝓧.X x ω ∈ J} ∩
        stopEvent 𝓧.X (exitTime 𝓧.X x) v) =
        ((ProbabilityTheory.expMeasure (w x)).map toWithTop) J * ENNReal.ofReal (G.c x v / G.pi x) := by
      intro v
      obtain ⟨hmeas, -, hindep, hlaw, hval⟩ := (h x).2.2.2.2.1
      have hset : ({ω | exitTime 𝓧.X x ω ∈ J} ∩ stopEvent 𝓧.X (exitTime 𝓧.X x) v)
          =ᵐ[𝓧.P x] (exitTime 𝓧.X x ⁻¹' J) ∩
            (stoppedValue 𝓧.X (exitTime 𝓧.X x) ⁻¹' {some v}) := by
        refine Filter.eventuallyEqSet_iff.2 ?_
        filter_upwards [hfinτ] with ω hωfin
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
          Set.mem_singleton_iff, stopEvent, hωfin, ne_eq, not_false_eq_true, true_and]
      rw [measure_congr hset,
        hindep.measure_inter_preimage_eq_mul _ _ hJ (measurableSet_option {some v})]
      congr 1
      · rw [← Measure.map_apply_of_aemeasurable hmeas hJ, hlaw]
      · exact hval v
    have hdec : {ω | exitTime 𝓧.X x ω ∈ J ∧ hittingTime 𝓧.X Gn ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω = some y} =ᵐ[𝓧.P x]
        ⋃ v : V, ({ω | exitTime 𝓧.X x ω ∈ J} ∩ stopEvent 𝓧.X (exitTime 𝓧.X x) v ∩
          futureAt 𝓧.X (exitTime 𝓧.X x) ⁻¹' hitEvent Gn y) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [ae_rightRegularAt hii (hR x), hfinτ,
        ae_exists_stoppedValue_exitTime h hG x, hhit] with ω hω hωfin hωval hωhit
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hωfin
      have hτa : exitTime 𝓧.X x ω = (a : WithTop ℝ≥0) := ha.symm
      have hua : (exitTime 𝓧.X x ω).untopA = a := by rw [hτa]; exact untopA_coe a
      have hiff := mem_hitEvent_futureAt_iff hω Gn y hτa
      have hne : (hittingTime 𝓧.X Gn ω ≠ ⊤) ↔
          (hittingAfter 𝓧.X (some '' (Gn : Set V)) a ω ≠ ⊤) := by
        rw [hωhit, hua]
      have hsv : stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω =
          stoppedValue 𝓧.X (hittingAfter 𝓧.X (some '' (Gn : Set V)) a) ω := by
        simp only [stoppedValue, hωhit, hua]
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        stopEvent, hiff, hne, hsv]
      constructor
      · rintro ⟨hJω, hne', hsvy⟩
        obtain ⟨v, hv⟩ := hωval
        exact ⟨v, ⟨hJω, hωfin, hv⟩, hne', hsvy⟩
      · rintro ⟨v, ⟨hJω, -, -⟩, hne', hsvy⟩
        exact ⟨hJω, hne', hsvy⟩
    rw [measure_congr hdec,
      measure_iUnion₀ (f := fun v : V => {ω | exitTime 𝓧.X x ω ∈ J} ∩
          stopEvent 𝓧.X (exitTime 𝓧.X x) v ∩
          futureAt 𝓧.X (exitTime 𝓧.X x) ⁻¹' hitEvent Gn y)
        (fun v v' hvv' => ((disjoint_stopEvent hvv').mono
          (Set.inter_subset_left.trans Set.inter_subset_right)
          (Set.inter_subset_left.trans Set.inter_subset_right)).aedisjoint)
        (fun v => ((nullMeasurableSet_preimage_of_aemeasurable hτm hJ).inter
          (nullMeasurableSet_stopEvent' 𝓧.measurable_X hii (hR x) hτm v)).inter
          (nullMeasurableSet_preimage_of_aemeasurable hfutm (measurableSet_hitEvent Gn y)))]
    simp_rw [hSM, hind, mul_assoc]
    rw [ENNReal.tsum_mul_left]
  have h1 := key I hI
  have h2 := key Set.univ MeasurableSet.univ
  rw [map_toWithTop_expMeasure_univ h x, one_mul] at h2
  have h3 : 𝓧.P x {ω | exitTime 𝓧.X x ω ∈ (Set.univ : Set (WithTop ℝ≥0)) ∧
      hittingTime 𝓧.X Gn ω ≠ ⊤ ∧
      stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω = some y} =
      ENNReal.ofReal (G.harmonicMeasure hG Gn x y) := by
    rw [← measure_stoppedValue_hittingTime h hG x (hR x) hGn y]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [((h x).2.2.2.2.2.2.2 Gn hGn).1] with ω hfin
    simp only [Set.mem_univ, true_and]
    exact ⟨fun hh => hh.2, fun hh => ⟨hfin.1, hh⟩⟩
  rw [h1, h2.symm.trans h3]

/-- **The one-step pair law under `P_x`** — properties (iii) and (vi) in one statement.  For
every `x ∈ VG`, under `P_x` the holding time at `x` (the `Tⁿ_0` of (3.31)) and the position
after the step of (3.31) are independent, the holding time being exponential with parameter
`w(x)` and the position having the law `pₙ(x, ·)` of (3.2)–(3.3). -/
theorem measure_stepPair_one (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X)
    {Gn : Finset V} (hGn : Gn.Nonempty) (x : V) {I : Set (WithTop ℝ≥0)}
    (hI : MeasurableSet I) (y : V) :
    𝓧.P x {ω | exitTime 𝓧.X x ω ∈ I ∧ stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =
      ((ProbabilityTheory.expMeasure (w x)).map toWithTop) I * ENNReal.ofReal (G.transProb hG Gn x y) := by
  by_cases hx : x ∈ Gn
  · have hae : ∀ᵐ ω ∂𝓧.P x, stepTime 𝓧.X Gn 1 ω = exitTime 𝓧.X x ω := by
      filter_upwards [(h x).1] with ω h0
      have h0' : stoppedValue 𝓧.X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω = some x := h0
      rw [stepTime_one, nextStep_eq_of_eq hx h0', exitTime_eq_hitAfter]
    have hset : {ω | exitTime 𝓧.X x ω ∈ I ∧ stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =ᵐ[𝓧.P x]
        {ω | stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧ stepTime 𝓧.X Gn 1 ω ∈ I ∧
          stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hae] with ω hω
      simp only [hω]
      tauto
    rw [measure_congr hset, measure_stepTime_one_of_mem h hx hI y,
      G.transProb_of_mem hG hx y]
  · have hae : ∀ᵐ ω ∂𝓧.P x, stepTime 𝓧.X Gn 1 ω = hittingTime 𝓧.X Gn ω := by
      filter_upwards [(h x).1] with ω h0
      have h0' : stoppedValue 𝓧.X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω ∉
          some '' (Gn : Set V) := by
        rw [show stoppedValue 𝓧.X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω = some x from h0]
        rintro ⟨v, hv, hvx⟩
        exact hx (Option.some_inj.1 hvx ▸ Finset.mem_coe.1 hv)
      rw [stepTime_one, nextStep_eq_of_notMem h0', hittingTime_eq_hitAfter]
    have hset : {ω | exitTime 𝓧.X x ω ∈ I ∧ stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} =ᵐ[𝓧.P x]
        {ω | exitTime 𝓧.X x ω ∈ I ∧ hittingTime 𝓧.X Gn ω ≠ ⊤ ∧
          stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω = some y} := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hae] with ω hω
      have hsv : stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω =
          stoppedValue 𝓧.X (hittingTime 𝓧.X Gn) ω := by
        simp only [stoppedValue, hω]
      simp only [hω, hsv]
    rw [measure_congr hset, measure_exitTime_hitting_of_notMem h hG hR hGn hx hI y]
    by_cases hy : y ∈ Gn
    · rw [G.transProb_of_not_mem_of_mem hG hx hy]
    · rw [G.transProb_of_not_mem_of_not_mem hG hx hy,
        harmonicMeasure_eq_zero_of_notMem G hG hGn hy x]

omit [Nontrivial V] in
/-- The `P_x`-law of the first step of (3.31) together with its holding time is the law of the
measurable path functional `stepPairEvent`. -/
theorem law_stepPairEvent (h : IsReflectedWalk G w hmin 𝓧) (x : V)
    (hR : RightContinuousAtInfty (𝓧.P x) 𝓧.X) (Gn : Finset V) {I : Set (WithTop ℝ≥0)}
    (hI : MeasurableSet I) (y : V) :
    𝓧.law x (stepPairEvent Gn I y) =
      𝓧.P x {ω | exitTime 𝓧.X x ω ∈ I ∧ stepTime 𝓧.X Gn 1 ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (stepTime 𝓧.X Gn 1) ω = some y} := by
  rw [ProcessFamily.law, Measure.map_apply 𝓧.measurable_trajectory
    (measurableSet_stepPairEvent Gn hI y)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_rightRegularAt (h x).2.2.1 hR, (h x).1] with ω hω h0
  have hval : stoppedValue 𝓧.X (stepTime 𝓧.X Gn 0) ω = some x := h0
  have hfut : futureAt 𝓧.X (stepTime 𝓧.X Gn 0) ω = 𝓧.trajectory ω := by
    rw [futureAt_of_eq (stepTime_zero_apply Gn ω), shiftedPath_zero]
    rfl
  have hadm : AdmissibleTarget
      {s : Option V | s ≠ stoppedValue 𝓧.X (stepTime 𝓧.X Gn 0) ω} := by
    rw [hval]; exact admissibleTarget_ne x
  have hiff := mem_stepPairEvent_futureAt_iff hω Gn I y
    (stepTime_zero_apply (X := 𝓧.X) Gn ω) hadm
  rw [hfut] at hiff
  simp only [Set.mem_preimage]
  have hstep1 : nextStep 𝓧.X Gn (stepTime 𝓧.X Gn 0) = stepTime 𝓧.X Gn 1 := rfl
  have he : exitAfter 𝓧.X (stepTime 𝓧.X Gn 0) ω - stepTime 𝓧.X Gn 0 ω =
      exitTime 𝓧.X x ω := by
    rw [exitAfter_stepTime_zero hval, stepTime_zero_apply]
    simp
  rw [hiff, hstep1, he]

/-- **The one-step pair law at `tⁿ_j`** (Section 3.4, Step 1, second paragraph): on the event
`{X̃_{tⁿ_j} = x}`, given any event `F` of the past `{X̃_s}_{s ≤ tⁿ_j}`, the holding time `Tⁿ_j`
of (3.31) and the new position `X̃_{tⁿ_{j+1}}` are conditionally independent, with laws
`Exponential(w(x))` and `pₙ(x, ·)`.  This is the exact statement the paper makes, for every
`x ∈ B₁Gₙ`. -/
theorem measure_stopEvent_succ_pair (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty)
    (j : ℕ) (x : V) {F : Set 𝓧.Ω}
    (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) (stepTime 𝓧.X Gn j) F)
    {I : Set (WithTop ℝ≥0)} (hI : MeasurableSet I) (y : V) :
    𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x ∩
        ({ω | holdingTime 𝓧.X Gn j ω ∈ I} ∩
          stopEvent 𝓧.X (stepTime 𝓧.X Gn (j + 1)) y)) =
      𝓧.P z (F ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn j) x) *
        (((ProbabilityTheory.expMeasure (w x)).map toWithTop) I * ENNReal.ofReal (G.transProb hG Gn x y)) := by
  rw [← measure_stepPair_one h hG hR hGn x hI y, ← law_stepPairEvent h x (hR x) Gn hI y,
    ← stepTime_strongMarkov h z (hR z) Gn j x hF (measurableSet_stepPairEvent Gn hI y)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_rightRegularAt (h z).2.2.1 (hR z)] with ω hω
  constructor
  · rintro ⟨hFE, hT, hstep⟩
    refine ⟨hFE, ?_⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hFE.2.1
    have hadm : AdmissibleTarget
        {s : Option V | s ≠ stoppedValue 𝓧.X (stepTime 𝓧.X Gn j) ω} := by
      rw [hFE.2.2]; exact admissibleTarget_ne x
    show futureAt 𝓧.X (stepTime 𝓧.X Gn j) ω ∈ stepPairEvent Gn I y
    rw [mem_stepPairEvent_futureAt_iff hω Gn I y ha.symm hadm]
    exact ⟨hT, hstep.1, hstep.2⟩
  · rintro ⟨hFE, hfut⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hFE.2.1
    have hadm : AdmissibleTarget
        {s : Option V | s ≠ stoppedValue 𝓧.X (stepTime 𝓧.X Gn j) ω} := by
      rw [hFE.2.2]; exact admissibleTarget_ne x
    have hfut' : futureAt 𝓧.X (stepTime 𝓧.X Gn j) ω ∈ stepPairEvent Gn I y := hfut
    rw [mem_stepPairEvent_futureAt_iff hω Gn I y ha.symm hadm] at hfut'
    exact ⟨hFE, hfut'.1, hfut'.2.1, hfut'.2.2⟩

end Reentry

/-! ### The finite-dimensional distributions of the pair `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)`

Iterating `measure_stopEvent_succ_pair` gives the joint cylinder probabilities of the embedded
chain together with its holding times: the product of the transition probabilities `pₙ` of
(3.2)–(3.3) with the exponential laws `Exponential(w(X̃_{tⁿ_j}))`. -/

/-- The cylinder event of the embedded chain **with its holding times**: `X̃_{tⁿ_i} = g i` for
every `i ≤ m`, and `Tⁿ_i ∈ J i` for every `i < m`. -/
def pairCylEvent (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (g : ℕ → V)
    (J : ℕ → Set (WithTop ℝ≥0)) : ℕ → Set Ω
  | 0 => stopEvent X (stepTime X Gn 0) (g 0)
  | m + 1 => pairCylEvent X Gn g J m ∩
      ({ω | holdingTime X Gn m ω ∈ J m} ∩ stopEvent X (stepTime X Gn (m + 1)) (g (m + 1)))

omit mΩ in
lemma pairCylEvent_subset (Gn : Finset V) (g : ℕ → V) (J : ℕ → Set (WithTop ℝ≥0)) (m : ℕ) :
    pairCylEvent X Gn g J m ⊆ stopEvent X (stepTime X Gn m) (g m) := by
  cases m with
  | zero => exact subset_rfl
  | succ m => exact Set.inter_subset_right.trans Set.inter_subset_right

/-- The holding time `Tⁿ_k` is measurable for the stopped σ-algebra at `tⁿ_j`, `k < j`: both
`tⁿ_k` and `exitAfter tⁿ_k` are stopping times bounded by `tⁿ_{k+1} ≤ tⁿ_j`. -/
lemma aeStoppedTime_holdingTime [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V) {k j : ℕ}
    (hkj : k < j)
    (hval : ∀ᵐ ω ∂P, ∃ x : V, stoppedValue X (stepTime X Gn k) ω = some x) :
    AEStoppedTime (naturalFiltration X hX) P (stepTime X Gn j) (holdingTime X Gn k) := by
  have h1 : AEStoppedTime (naturalFiltration X hX) P (stepTime X Gn j)
      (exitAfter X (stepTime X Gn k)) :=
    AEStoppedTime.of_le (isAEStoppingTime_exitAfter hX hii hR
      (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn k).1 hval)
      fun ω => (exitAfter_le_stepTime_succ Gn k ω).trans
        (stepTime_mono Gn (Nat.succ_le_of_lt hkj) ω)
  have h2 : AEStoppedTime (naturalFiltration X hX) P (stepTime X Gn j) (stepTime X Gn k) :=
    AEStoppedTime.of_le (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn k).1
      fun ω => stepTime_mono Gn hkj.le ω
  exact h1.comp₂ h2 measurable_sub_withTop

/-- The joint cylinder event up to `m` is an event of the past `{X̃_s}_{s ≤ tⁿ_m}`, as
Lemma 3.10 requires. -/
lemma aemeasurableSetStopped_pairCylEvent [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V) (g : ℕ → V)
    {J : ℕ → Set (WithTop ℝ≥0)} (hJ : ∀ k, MeasurableSet (J k))
    (hval : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ x : V, stoppedValue X (stepTime X Gn k) ω = some x) (m : ℕ) :
    AEMeasurableSetStopped (naturalFiltration X hX) P (stepTime X Gn m)
      (pairCylEvent X Gn g J m) := by
  induction m with
  | zero =>
    exact aemeasurableSetStopped_stopEvent hX hii hR
      (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn 0).1 (g 0)
  | succ m ih =>
    refine AEMeasurableSetStopped.inter
      (ih.mono (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn (m + 1)).1
        fun ω => stepTime_le_succ Gn m ω)
      (AEMeasurableSetStopped.inter ?_ (aemeasurableSetStopped_stopEvent hX hii hR
        (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn (m + 1)).1 (g (m + 1))))
    exact (aeStoppedTime_holdingTime hX hii hR Gn (Nat.lt_succ_self m) (hval m)).preimage
      (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn (m + 1)).1 (hJ m)

section PairCylinder

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V] [Nontrivial V]

open scoped Classical in
/-- **The finite-dimensional distributions of the pair `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)`** (Section
3.4, Step 1, conclusion).  For a process satisfying (i)–(vi), the embedded chain of (3.31)
together with its holding times has the cylinder probabilities of the Markov chain `Yⁿ` of
(3.2)–(3.3) with conditionally independent `Exponential(w(Yⁿ_j))` holding times — i.e. exactly
the cylinder probabilities of `E.chainLaw hG n z ⊗ₘ holdingKernel w`. -/
theorem measure_pairCylEvent (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (z : V)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty)
    (g : ℕ → V) {J : ℕ → Set (WithTop ℝ≥0)} (hJ : ∀ k, MeasurableSet (J k)) (m : ℕ) :
    𝓧.P z (pairCylEvent 𝓧.X Gn g J m) =
      (if g 0 = z then 1 else 0) *
        ∏ i ∈ Finset.range m, (((ProbabilityTheory.expMeasure (w (g i))).map toWithTop) (J i) *
          ENNReal.ofReal (G.transProb hG Gn (g i) (g (i + 1)))) := by
  have hdef : ∀ k : ℕ, ∀ᵐ ω ∂𝓧.P z, ∃ x : V,
      stoppedValue 𝓧.X (stepTime 𝓧.X Gn k) ω = some x := by
    intro k
    filter_upwards [ae_forall_definedAt h hG z hR hGn] with ω hω
    exact ((mem_definedAt_iff Gn k ω).1 (hω k)).2
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, mul_one]
    by_cases hgz : g 0 = z
    · rw [ite_eq_left hgz]
      have hset : 𝓧.P z (pairCylEvent 𝓧.X Gn g J 0) = 𝓧.P z Set.univ := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [(h z).1] with ω hω
        simp only [Set.mem_univ, iff_true]
        refine ⟨WithTop.coe_ne_top, ?_⟩
        show 𝓧.X 0 ω = some (g 0)
        rw [hω, hgz]
      rw [hset, measure_univ]
    · rw [ite_eq_right hgz]
      have hempty : 𝓧.P z (pairCylEvent 𝓧.X Gn g J 0) = 𝓧.P z ∅ := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [(h z).1] with ω hω
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hmem
        have hval : 𝓧.X 0 ω = some (g 0) := hmem.2
        rw [hω] at hval
        exact hgz (Option.some_inj.1 hval).symm
      rw [hempty, measure_empty]
  | succ m ih =>
    have hsub : pairCylEvent 𝓧.X Gn g J m ∩ stopEvent 𝓧.X (stepTime 𝓧.X Gn m) (g m) =
        pairCylEvent 𝓧.X Gn g J m := Set.inter_eq_left.2 (pairCylEvent_subset Gn g J m)
    have hstep := measure_stopEvent_succ_pair h hG z hR hGn m (g m)
      (aemeasurableSetStopped_pairCylEvent 𝓧.measurable_X (h z).2.2.1 (hR z) Gn g hJ hdef m)
      (hJ m) (g (m + 1))
    rw [hsub] at hstep
    rw [show pairCylEvent 𝓧.X Gn g J (m + 1) = pairCylEvent 𝓧.X Gn g J m ∩
      ({ω | holdingTime 𝓧.X Gn m ω ∈ J m} ∩
        stopEvent 𝓧.X (stepTime 𝓧.X Gn (m + 1)) (g (m + 1))) from rfl,
      hstep, ih, Finset.prod_range_succ, mul_assoc]

end PairCylinder

/-! ### The prefix probabilities of the Ionescu–Tulcea chain law -/

section ChainPrefix

variable {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (κ : Kernel S S)
  [IsMarkovKernel κ]

omit [MeasurableSingletonClass S] κ in
lemma measurableSet_prefixEvent [MeasurableSingletonClass S] (g : ℕ → S) (m : ℕ) :
    MeasurableSet {y : ℕ → S | ∀ j ≤ m, y j = g j} := by
  have he : {y : ℕ → S | ∀ j ≤ m, y j = g j} =
      ⋂ j : ℕ, ⋂ _ : j ≤ m, (fun y : ℕ → S => y j) ⁻¹' {g j} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [he]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (measurable_pi_apply j) (measurableSet_singleton (g j))

open scoped Classical in
/-- **The prefix probabilities of the chain law.**  `P_z(Y_0 = g_0, …, Y_m = g_m)` is the
product of the one-step kernel evaluations, by the first-step decomposition
`MarkovChain.chainLaw_eq_map_consPath`. -/
theorem chainLaw_prefixEvent (m : ℕ) : ∀ (z : S) (g : ℕ → S),
    MarkovChain.chainLaw κ z {y : ℕ → S | ∀ j ≤ m, y j = g j} =
      (if g 0 = z then 1 else 0) * ∏ i ∈ Finset.range m, κ (g i) {g (i + 1)} := by
  induction m with
  | zero =>
    intro z g
    rw [Finset.prod_range_zero, mul_one]
    by_cases hgz : g 0 = z
    · rw [ite_eq_left hgz]
      have hset : MarkovChain.chainLaw κ z {y : ℕ → S | ∀ j ≤ 0, y j = g j} =
          MarkovChain.chainLaw κ z Set.univ := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [MarkovChain.chainLaw_ae_start κ z] with y hy
        simp only [Set.mem_univ, iff_true]
        intro j hj
        rw [Nat.le_zero.1 hj, hy, hgz]
      rw [hset, measure_univ]
    · rw [ite_eq_right hgz]
      have hset : MarkovChain.chainLaw κ z {y : ℕ → S | ∀ j ≤ 0, y j = g j} =
          MarkovChain.chainLaw κ z ∅ := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [MarkovChain.chainLaw_ae_start κ z] with y hy
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hh
        exact hgz ((hy.symm.trans (hh 0 le_rfl)).symm)
      rw [hset, measure_empty]
  | succ m ih =>
    intro z g
    have hpre : (MarkovChain.consPath z) ⁻¹' {y : ℕ → S | ∀ j ≤ m + 1, y j = g j} =
        if g 0 = z then {q : ℕ → S | ∀ j ≤ m, q j = g (j + 1)} else ∅ := by
      by_cases hgz : g 0 = z
      · rw [ite_eq_left hgz]
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · intro hh j hj
          have h1 := hh (j + 1) (Nat.succ_le_succ hj)
          rwa [MarkovChain.consPath_succ] at h1
        · intro hh j hj
          cases j with
          | zero => rw [MarkovChain.consPath_zero, hgz]
          | succ k =>
            rw [MarkovChain.consPath_succ]
            exact hh k (Nat.le_of_succ_le_succ hj)
      · rw [ite_eq_right hgz]
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hh
        have h0 := hh 0 (Nat.zero_le _)
        rw [MarkovChain.consPath_zero] at h0
        exact hgz h0.symm
    rw [MarkovChain.chainLaw_eq_map_consPath κ z,
      Measure.map_apply (MarkovChain.measurable_consPath z)
        (measurableSet_prefixEvent g (m + 1)), hpre]
    by_cases hgz : g 0 = z
    · rw [ite_eq_left hgz, ite_eq_left hgz, one_mul,
        Measure.bind_apply (measurableSet_prefixEvent (fun i => g (i + 1)) m)
          (MarkovChain.pathKernel κ).aemeasurable]
      have hval : ∀ y : S, MarkovChain.pathKernel κ y
          {q : ℕ → S | ∀ j ≤ m, q j = g (j + 1)} =
          (if g 1 = y then (1 : ℝ≥0∞) else 0) *
            ∏ i ∈ Finset.range m, κ (g (i + 1)) {g (i + 1 + 1)} := by
        intro y
        rw [MarkovChain.pathKernel_apply]
        exact ih y (fun i => g (i + 1))
      simp_rw [hval]
      have hind : (fun y : S => if g 1 = y then (1 : ℝ≥0∞) else 0) =
          Set.indicator {g 1} (fun _ => (1 : ℝ≥0∞)) := by
        funext y
        by_cases hy : g 1 = y
        · simp [Set.indicator, hy]
        · have hy' : y ∉ ({g 1} : Set S) := fun hc => hy hc.symm
          simp [Set.indicator, hy, hy']
      rw [lintegral_mul_const _ (by rw [hind]; exact (measurable_one.indicator
        (measurableSet_singleton (g 1))))]
      rw [hind, lintegral_indicator (measurableSet_singleton (g 1)), setLIntegral_const,
        Finset.prod_range_succ' (fun i => κ (g i) {g (i + 1)}) m, hgz, one_mul]
      exact mul_comm _ _
    · rw [ite_eq_right hgz, ite_eq_right hgz, measure_empty, zero_mul]

end ChainPrefix

/-! ### The exponential law on `[0,∞]` versus on `ℝ` -/

section ExpMeasure

open ProbabilityTheory

/-- `Exponential(r)` gives no mass to `(-∞, 0]`. -/
lemma expMeasure_Iic_zero {r : ℝ} (hr : 0 < r) : ProbabilityTheory.expMeasure r (Set.Iic 0) = 0 := by
  have _ : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr]
  simp

/-- Truncating at `0` does not change an `Exponential(r)` probability. -/
lemma expMeasure_preimage_toNNReal {r : ℝ} (hr : 0 < r) (B : Set ℝ) :
    ProbabilityTheory.expMeasure r {t : ℝ | ((t.toNNReal : ℝ)) ∈ B} = ProbabilityTheory.expMeasure r B := by
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  have hae : ∀ᵐ t ∂ProbabilityTheory.expMeasure r, (0 : ℝ) < t := by
    rw [ae_iff]
    have he : {t : ℝ | ¬ (0 : ℝ) < t} = Set.Iic 0 := by ext t; simp
    rw [he]
    exact expMeasure_Iic_zero hr
  filter_upwards [hae] with t ht
  simp only [Real.coe_toNNReal t ht.le]

/-- **The exponential law of property (iii), read on `ℝ`.**  The law of the holding time on
`[0,∞]` of property (iii), pulled back along `ENNReal.toReal`, is the exponential law on `ℝ`
that `holdingKernel` uses. -/
lemma map_toWithTop_expMeasure_toReal_preimage {r : ℝ} (hr : 0 < r) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ((ProbabilityTheory.expMeasure r).map toWithTop) (ENNReal.toReal ⁻¹' B) = ProbabilityTheory.expMeasure r B := by
  have hms : MeasurableSet (ENNReal.toReal ⁻¹' B : Set (WithTop ℝ≥0)) :=
    ENNReal.measurable_toReal hB
  have h1 : ((ProbabilityTheory.expMeasure r).map toWithTop) (ENNReal.toReal ⁻¹' B) =
      ProbabilityTheory.expMeasure r (toWithTop ⁻¹' (ENNReal.toReal ⁻¹' B)) :=
    Measure.map_apply measurable_toWithTop hms
  have hpre : toWithTop ⁻¹' (ENNReal.toReal ⁻¹' B) = {t : ℝ | ((t.toNNReal : ℝ)) ∈ B} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, toWithTop]
    exact Iff.rfl
  rw [h1, hpre]
  exact expMeasure_preimage_toNNReal hr B

end ExpMeasure

/-! ### The embedded chain and its holding times as a random element of `VG^ℕ × ℝ^ℕ` -/

omit mΩ in
lemma mem_pairCylEvent_iff (Gn : Finset V) (g : ℕ → V) (J : ℕ → Set (WithTop ℝ≥0)) (m : ℕ)
    (ω : Ω) :
    ω ∈ pairCylEvent X Gn g J m ↔
      ((∀ i ≤ m, ω ∈ stopEvent X (stepTime X Gn i) (g i)) ∧
        ∀ i < m, holdingTime X Gn i ω ∈ J i) := by
  induction m with
  | zero =>
    constructor
    · intro hω
      refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      rw [Nat.le_zero.1 hi]
      exact hω
    · intro hω
      exact hω.1 0 le_rfl
  | succ m ih =>
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨hp, hq⟩ := ih.1 h1
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rcases eq_or_lt_of_le hi with heq | hlt
        · rw [heq]; exact h3
        · exact hp i (Nat.lt_succ_iff.1 hlt)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
        · exact hq i hlt
        · rw [heq]; exact h2
    · intro hω
      exact ⟨ih.2 ⟨fun i hi => hω.1 i (hi.trans (Nat.le_succ m)),
        fun i hi => hω.2 i (Nat.lt_succ_of_lt hi)⟩, hω.2 m (Nat.lt_succ_self m),
        hω.1 (m + 1) le_rfl⟩

/-- The embedded chain of (3.31) as a `VG`-valued sequence; `v₀` is the (almost surely
irrelevant) value used where the process is undefined. -/
noncomputable def embeddedChainOf (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (v₀ : V) (ω : Ω) :
    ℕ → V := fun j => (stoppedValue X (stepTime X Gn j) ω).getD v₀

/-- The holding times `Tⁿ_j` of (3.31) as a real sequence. -/
noncomputable def holdingSeqOf (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (ω : Ω) : ℕ → ℝ :=
  fun j => (holdingTime X Gn j ω).toReal

/-- **The pair `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)`** of Step 1 of Section 3.4, as a random element of
`VG^ℕ × ℝ^ℕ` — the same object as `ContinuousTimeChain.embeddedPair` for the constructed
process. -/
noncomputable def embeddedPairOf (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (v₀ : V) (ω : Ω) :
    (ℕ → V) × (ℕ → ℝ) := (embeddedChainOf X Gn v₀ ω, holdingSeqOf X Gn ω)

/-- **The exit time from the current position is a random variable**, when the current position
is almost surely a vertex. -/
theorem aemeasurable_exitAfter [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) {σ : Ω → WithTop ℝ≥0}
    (hσ : AEMeasurable σ P)
    (hval : ∀ᵐ ω ∂P, ∃ x : V, stoppedValue X σ ω = some x) :
    AEMeasurable (exitAfter X σ) P := by
  classical
  let Φ : Option V → Ω → WithTop ℝ≥0 := fun a =>
    a.elim (fun _ => (⊤ : WithTop ℝ≥0)) fun x => hitAfter X {s : Option V | s ≠ some x} σ
  have hΦ : ∀ a, AEMeasurable (Φ a) P := by
    intro a
    cases a with
    | none =>
      show AEMeasurable (fun _ : Ω => (⊤ : WithTop ℝ≥0)) P
      exact aemeasurable_const
    | some x =>
      show AEMeasurable (hitAfter X {s : Option V | s ≠ some x} σ) P
      exact aemeasurable_hitAfter hX hii hR (admissibleTarget_ne x) hσ
  have hvalm : AEMeasurable (stoppedValue X σ) P := aemeasurable_stoppedValue hX hii hR hσ
  have hΦm : Measurable fun p : Ω × Option V => (hΦ p.2).mk _ p.1 :=
    measurable_from_prod_countable_left fun a => (hΦ a).measurable_mk
  refine ⟨fun ω => (hΦ (hvalm.mk _ ω)).mk _ ω,
    hΦm.comp (measurable_id.prodMk hvalm.measurable_mk), ?_⟩
  filter_upwards [hvalm.ae_eq_mk, ae_all_iff.2 fun a => (hΦ a).ae_eq_mk, hval]
    with ω hω hΦω hvalω
  obtain ⟨x, hx⟩ := hvalω
  have h1 : exitAfter X σ ω = Φ (stoppedValue X σ ω) ω := by
    rw [hx]
    show exitAfter X σ ω = hitAfter X {s : Option V | s ≠ some x} σ ω
    rw [exitAfter, hx]
  rw [h1, hω, ← hΦω]

/-- The holding times of (3.31) are random variables. -/
lemma aemeasurable_holdingTime [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V) (j : ℕ)
    (hval : ∀ᵐ ω ∂P, ∃ x : V, stoppedValue X (stepTime X Gn j) ω = some x) :
    AEMeasurable (fun ω => holdingTime X Gn j ω) P := by
  have h2 := (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn j).2
  have h1 := aemeasurable_exitAfter hX hii hR h2 hval
  exact measurable_sub_withTop.comp_aemeasurable (h1.prodMk h2)

/-- The pair of the embedded chain and its holding times is a random element of
`VG^ℕ × ℝ^ℕ`. -/
lemma aemeasurable_embeddedPairOf [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (Gn : Finset V) (v₀ : V)
    (hval : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ x : V, stoppedValue X (stepTime X Gn j) ω = some x) :
    AEMeasurable (embeddedPairOf X Gn v₀) P := by
  have hZ : ∀ j : ℕ, AEMeasurable (fun ω => (stoppedValue X (stepTime X Gn j) ω).getD v₀) P := by
    intro j
    exact (measurable_of_countable (fun o : Option V => o.getD v₀)).comp_aemeasurable
      (aemeasurable_stoppedValue hX hii hR
        (stepTime_isAEStoppingTime_aemeasurable hX hii hR Gn j).2)
  have hT : ∀ j : ℕ, AEMeasurable (fun ω => (holdingTime X Gn j ω).toReal) P :=
    fun j => ENNReal.measurable_toReal.comp_aemeasurable
      (aemeasurable_holdingTime hX hii hR Gn j (hval j))
  refine ⟨fun ω => (fun j => (hZ j).mk _ ω, fun j => (hT j).mk _ ω),
    (Measurable.of_eval fun j => (hZ j).measurable_mk).prodMk
      (Measurable.of_eval fun j => (hT j).measurable_mk), ?_⟩
  filter_upwards [ae_all_iff.2 fun j => (hZ j).ae_eq_mk,
    ae_all_iff.2 fun j => (hT j).ae_eq_mk] with ω h1 h2
  show (embeddedChainOf X Gn v₀ ω, holdingSeqOf X Gn ω) =
    (fun j => (hZ j).mk _ ω, fun j => (hT j).mk _ ω)
  rw [Prod.mk.injEq]
  exact ⟨funext fun j => h1 j, funext fun j => h2 j⟩

/-! ### The prefix rectangles of `VG^ℕ × ℝ^ℕ` -/

section PairRect

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- A prefix rectangle: the first `m + 1` positions are prescribed and the first `m` holding
times are constrained. -/
def pairRect (m : ℕ) (g : ℕ → V) (B : ℕ → Set ℝ) : Set ((ℕ → V) × (ℕ → ℝ)) :=
  {y : ℕ → V | ∀ j ≤ m, y j = g j} ×ˢ Set.pi (↑(Finset.range m)) B

/-- The π-system of prefix rectangles; it generates the product σ-algebra
(`generateFrom_pairRects`). -/
def pairRects (V : Type u) : Set (Set ((ℕ → V) × (ℕ → ℝ))) :=
  {C | ∃ (m : ℕ) (g : ℕ → V) (B : ℕ → Set ℝ), (∀ j, MeasurableSet (B j)) ∧ C = pairRect m g B}

omit [Countable V] in
lemma measurableSet_pairRect (m : ℕ) (g : ℕ → V) {B : ℕ → Set ℝ}
    (hB : ∀ j, MeasurableSet (B j)) : MeasurableSet (pairRect m g B) :=
  (measurableSet_prefixEvent (S := V) g m).prod
    (MeasurableSet.pi (Finset.range m).countable_toSet fun j _ => hB j)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- A total extension of a finite history, with the value `v₀` beyond the prefix. -/
def extendPrefix (v₀ : V) (m : ℕ) (h : Finset.Iic m → V) : ℕ → V :=
  fun j => if hj : j ≤ m then h ⟨j, Finset.mem_Iic.2 hj⟩ else v₀

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
lemma extendPrefix_apply_of_le (v₀ : V) {m j : ℕ} (h : Finset.Iic m → V) (hj : j ≤ m) :
    extendPrefix v₀ m h j = h ⟨j, Finset.mem_Iic.2 hj⟩ := dite_eq_left hj

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
lemma pairRect_inter_of_le {m m' : ℕ} (hmm' : m ≤ m') (g g' : ℕ → V) (B B' : ℕ → Set ℝ)
    {p : (ℕ → V) × (ℕ → ℝ)} (hp : p ∈ pairRect m g B ∩ pairRect m' g' B') :
    pairRect m g B ∩ pairRect m' g' B' =
      pairRect m' g' (fun j => (if j < m then B j else Set.univ) ∩ B' j) := by
  obtain ⟨⟨hp1, -⟩, ⟨hp1', -⟩⟩ := hp
  have hgg : ∀ j ≤ m, g j = g' j := fun j hj =>
    (hp1 j hj).symm.trans (hp1' j (hj.trans hmm'))
  ext q
  simp only [pairRect, Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_pi,
    Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h1', h2'⟩⟩
    refine ⟨h1', fun j hj => ⟨?_, h2' j hj⟩⟩
    by_cases hjm : j < m
    · rw [ite_eq_left hjm]; exact h2 j hjm
    · rw [ite_eq_right hjm]; exact Set.mem_univ _
  · rintro ⟨h1', h2'⟩
    refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, h1', fun j hj => (h2' j hj).2⟩
    · rw [h1' j (hj.trans hmm')]
      exact (hgg j hj).symm
    · have hmem := (h2' j (lt_of_lt_of_le hj hmm')).1
      rwa [ite_eq_left hj] at hmem

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
lemma isPiSystem_pairRects : IsPiSystem (pairRects V) := by
  rintro C ⟨m, g, B, hB, rfl⟩ C' ⟨m', g', B', hB', rfl⟩ hne
  obtain ⟨p, hp⟩ := hne
  rcases le_total m m' with hmm' | hmm'
  · refine ⟨m', g', fun j => (if j < m then B j else Set.univ) ∩ B' j, fun j => ?_,
      pairRect_inter_of_le hmm' g g' B B' hp⟩
    exact MeasurableSet.inter (by split_ifs; exacts [hB j, MeasurableSet.univ]) (hB' j)
  · refine ⟨m, g, fun j => (if j < m' then B' j else Set.univ) ∩ B j, fun j => ?_, ?_⟩
    · exact MeasurableSet.inter (by split_ifs; exacts [hB' j, MeasurableSet.univ]) (hB j)
    · rw [Set.inter_comm]
      exact pairRect_inter_of_le hmm' g' g B' B ⟨hp.2, hp.1⟩

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- A countable union of generators is measurable for the generated σ-algebra. -/
lemma measurableSet_generateFrom_iUnion {α : Type*} {C : Set (Set α)} {ι : Sort*} [Countable ι]
    {f : ι → Set α} (hf : ∀ i, f i ∈ C) :
    MeasurableSet[MeasurableSpace.generateFrom C] (⋃ i, f i) := by
  letI : MeasurableSpace α := MeasurableSpace.generateFrom C
  exact MeasurableSet.iUnion fun i => MeasurableSpace.measurableSet_generateFrom (hf i)

omit [MeasurableSingletonClass V] in
/-- A σ-algebra on `(ℕ → V) × (ℕ → ℝ)` measuring every coordinate event contains the whole
product σ-algebra. -/
lemma prod_le_of_coords (m : MeasurableSpace ((ℕ → V) × (ℕ → ℝ)))
    (h1 : ∀ (j : ℕ) (v : V), MeasurableSet[m] {p : (ℕ → V) × (ℕ → ℝ) | p.1 j = v})
    (h2 : ∀ (j : ℕ) (W : Set ℝ), MeasurableSet W →
      MeasurableSet[m] {p : (ℕ → V) × (ℕ → ℝ) | p.2 j ∈ W}) :
    (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → V) × (ℕ → ℝ))) ≤ m := by
  letI : MeasurableSpace ((ℕ → V) × (ℕ → ℝ)) := m
  have hfst : Measurable (Prod.fst : (ℕ → V) × (ℕ → ℝ) → (ℕ → V)) := by
    apply Measurable.of_eval
    intro j
    apply measurable_to_countable'
    intro v
    exact h1 j v
  have hsnd : Measurable (Prod.snd : (ℕ → V) × (ℕ → ℝ) → (ℕ → ℝ)) := by
    apply Measurable.of_eval
    intro j W hW
    exact h2 j W hW
  intro s hs
  exact hfst.prodMk hsnd hs

lemma generateFrom_pairRects (v₀ : V) :
    MeasurableSpace.generateFrom (pairRects V) =
      (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → V) × (ℕ → ℝ))) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro C ⟨m, g, B, hB, rfl⟩
    exact measurableSet_pairRect m g hB
  · refine prod_le_of_coords _ (fun j v => ?_) (fun j W hW => ?_)
    · have he : {p : (ℕ → V) × (ℕ → ℝ) | p.1 j = v} =
          ⋃ hh : {hh : Finset.Iic j → V // hh ⟨j, Finset.mem_Iic.2 le_rfl⟩ = v},
            pairRect j (extendPrefix v₀ j hh.1) (fun _ => Set.univ) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, pairRect, Set.mem_prod, Set.mem_pi]
        constructor
        · intro hpj
          refine ⟨⟨fun i => p.1 i.1, hpj⟩, fun k hk => ?_, fun k _ => Set.mem_univ _⟩
          rw [extendPrefix_apply_of_le v₀ _ hk]
        · rintro ⟨⟨hh, hhv⟩, h1, -⟩
          have h1j := h1 j le_rfl
          rw [extendPrefix_apply_of_le v₀ _ (le_refl j)] at h1j
          rw [h1j]
          exact hhv
      rw [he]
      exact measurableSet_generateFrom_iUnion fun hh =>
        ⟨j, extendPrefix v₀ j hh.1, fun _ => Set.univ, fun _ => MeasurableSet.univ, rfl⟩
    · have he : {p : (ℕ → V) × (ℕ → ℝ) | p.2 j ∈ W} =
          ⋃ hh : Finset.Iic (j + 1) → V,
            pairRect (j + 1) (extendPrefix v₀ (j + 1) hh)
              (fun k => if k = j then W else Set.univ) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, pairRect, Set.mem_prod, Set.mem_pi,
          Finset.coe_range, Set.mem_Iio]
        constructor
        · intro hpj
          refine ⟨fun i => p.1 i.1, fun k hk => ?_, fun k _ => ?_⟩
          · rw [extendPrefix_apply_of_le v₀ _ hk]
          · by_cases hkj : k = j
            · rw [ite_eq_left hkj, hkj]; exact hpj
            · rw [ite_eq_right hkj]; exact Set.mem_univ _
        · rintro ⟨hh, -, h2⟩
          have h2j := h2 j (Nat.lt_succ_self j)
          rwa [ite_eq_left rfl] at h2j
      rw [he]
      refine measurableSet_generateFrom_iUnion fun hh =>
        ⟨j + 1, extendPrefix v₀ (j + 1) hh, fun k => if k = j then W else Set.univ,
          fun k => ?_, rfl⟩
      show MeasurableSet (if k = j then W else Set.univ)
      split_ifs
      exacts [hW, MeasurableSet.univ]

end PairRect

/-! ### The law of the pair: the meeting point of the two halves of the uniqueness proof -/

section PairLaw

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {𝓧 : ProcessFamily V}

/-- **The law of the pair `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)`** (Gwynne–Sung, Section 3.4, Step 1,
conclusion).  For an **arbitrary** process satisfying the properties (i)–(vi) of Theorem 1.6, the
embedded chain of (3.31) paired with its holding times has the law

  `MarkovChain.chainLaw (G.stepKernel hG hGn) z ⊗ₘ holdingKernel w`,

i.e. the embedded chain is the Markov chain `Yⁿ` of (3.2)–(3.3) started at `z`, and conditionally
on it the holding times are independent `Exponential(w(Yⁿ_j))`.  This is precisely the law that
`ContinuousTimeChain.map_embeddedPair` establishes for the process `Xⁿ` of (3.15); since `Xⁿ` is
the fixed measurable time change `jumpPath` of that pair
(`ContinuousTimeChain.Xn_eq_jumpPath`, `ContinuousTimeChain.map_trajectoryN`), the two processes
have the same law — the last sentence of Step 1 (p. 26). -/
theorem map_embeddedPairOf (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty)
    (z v₀ : V) :
    (𝓧.P z).map (embeddedPairOf 𝓧.X Gn v₀) =
      MarkovChain.chainLaw (G.stepKernel hG hGn) z ⊗ₘ holdingKernel w := by
  classical
  have hdef : ∀ k : ℕ, ∀ᵐ ω ∂𝓧.P z, ∃ x : V,
      stoppedValue 𝓧.X (stepTime 𝓧.X Gn k) ω = some x := by
    intro k
    filter_upwards [ae_forall_definedAt h hG z hR hGn] with ω hω
    exact ((mem_definedAt_iff Gn k ω).1 (hω k)).2
  have hpairm : AEMeasurable (embeddedPairOf 𝓧.X Gn v₀) (𝓧.P z) :=
    aemeasurable_embeddedPairOf 𝓧.measurable_X (h z).2.2.1 (hR z) Gn v₀ hdef
  haveI hfin : IsFiniteMeasure ((𝓧.P z).map (embeddedPairOf 𝓧.X Gn v₀)) := by
    constructor
    rw [Measure.map_apply_of_aemeasurable hpairm MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top _ _
  refine MeasureTheory.ext_of_generate_finite (pairRects V)
    (generateFrom_pairRects v₀).symm isPiSystem_pairRects ?_ ?_
  · rintro C ⟨m, g, B, hB, rfl⟩
    -- the left-hand side, by the cylinder law of Step 1
    have hJm : ∀ i : ℕ, MeasurableSet ((ENNReal.toReal ⁻¹' B i : Set (WithTop ℝ≥0))) :=
      fun i => ENNReal.measurable_toReal (hB i)
    have hsetL : (embeddedPairOf 𝓧.X Gn v₀) ⁻¹' pairRect m g B =ᵐ[𝓧.P z]
        pairCylEvent 𝓧.X Gn g (fun i => ENNReal.toReal ⁻¹' B i) m := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [ae_forall_definedAt h hG z hR hGn] with ω hω
      rw [mem_pairCylEvent_iff]
      simp only [Set.mem_preimage, pairRect, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_pi,
        Finset.coe_range, Set.mem_Iio, embeddedPairOf, embeddedChainOf, holdingSeqOf]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, fun i hi => h2 i hi⟩
        obtain ⟨hfin, x, hx⟩ := (mem_definedAt_iff Gn i ω).1 (hω i)
        have hgi : x = g i := by
          have h1i := h1 i hi
          rw [hx] at h1i
          exact h1i
        exact ⟨hfin, by rw [hx, hgi]⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, fun i hi => h2 i hi⟩
        rw [(h1 i hi).2]
        rfl
    have hLHS : ((𝓧.P z).map (embeddedPairOf 𝓧.X Gn v₀)) (pairRect m g B) =
        (if g 0 = z then 1 else 0) *
          ∏ i ∈ Finset.range m, (ProbabilityTheory.expMeasure (w (g i)) (B i) *
            ENNReal.ofReal (G.transProb hG Gn (g i) (g (i + 1)))) := by
      rw [Measure.map_apply_of_aemeasurable hpairm (measurableSet_pairRect m g hB),
        measure_congr hsetL, measure_pairCylEvent h hG z hR hGn g hJm m]
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      rw [map_toWithTop_expMeasure_toReal_preimage (hw (g i)) (hB i)]
    -- the right-hand side, by the prefix law of the chain and the product form of the kernel
    have hA : MeasurableSet {y : ℕ → V | ∀ j ≤ m, y j = g j} :=
      measurableSet_prefixEvent (S := V) g m
    have hD : MeasurableSet (Set.pi (↑(Finset.range m)) B) :=
      MeasurableSet.pi (Finset.range m).countable_toSet fun j _ => hB j
    have hker : ∀ y ∈ {y : ℕ → V | ∀ j ≤ m, y j = g j},
        holdingKernel w y (Set.pi (↑(Finset.range m)) B) =
          ∏ i ∈ Finset.range m, ProbabilityTheory.expMeasure (w (g i)) (B i) := by
      intro y hy
      haveI : ∀ i : ℕ, IsProbabilityMeasure (ProbabilityTheory.expMeasure (w (y i))) :=
        fun i => ProbabilityTheory.isProbabilityMeasure_expMeasure (hw (y i))
      rw [holdingKernel_apply hw y, Measure.infinitePi_pi _ fun j _ => hB j]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [hy i (le_of_lt (Finset.mem_range.1 hi))]
    have hRHS : (MarkovChain.chainLaw (G.stepKernel hG hGn) z ⊗ₘ holdingKernel w)
        (pairRect m g B) =
        (∏ i ∈ Finset.range m, ProbabilityTheory.expMeasure (w (g i)) (B i)) *
          ((if g 0 = z then 1 else 0) *
            ∏ i ∈ Finset.range m, ENNReal.ofReal (G.transProb hG Gn (g i) (g (i + 1)))) := by
      rw [pairRect, Measure.compProd_apply_prod hA hD]
      rw [lintegral_congr_ae ((ae_restrict_iff' hA).2 (ae_of_all _ hker)), setLIntegral_const,
        chainLaw_prefixEvent (G.stepKernel hG hGn) m z g]
      refine congrArg _ (congrArg _ (Finset.prod_congr rfl fun i _ => ?_))
      exact G.stepKernel_singleton hG hGn (g i) (g (i + 1))
    rw [hLHS, hRHS, Finset.prod_mul_distrib]
    ring
  · rw [Measure.map_apply_of_aemeasurable hpairm MeasurableSet.univ, Set.preimage_univ,
      measure_univ, measure_univ]

/-- **The law of the pair, along an exhaustion** (the form in which the constructed side states
it, `ContinuousTimeChain.map_embeddedPair`): for an arbitrary process satisfying (i)–(vi), the
embedded chain of (3.31) at level `n` with its holding times has the law
`E.chainLaw hG n z ⊗ₘ holdingKernel w`. -/
theorem map_embeddedPairOf_exhaustion (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) (E : G.Exhaustion) (n : ℕ) (z v₀ : V) :
    (𝓧.P z).map (embeddedPairOf 𝓧.X (E.Gsub n) v₀) =
      E.chainLaw hG n z ⊗ₘ holdingKernel w :=
  map_embeddedPairOf h hG hw hR (E.nonempty n) z v₀

end PairLaw

/-! ### (3.32): the process `X̃ⁿ`, and its one-time marginals

> "Hence we can define `X̃ⁿ : [0,∞) → B₁Gₙ` by `X̃ⁿ_t := X̃_{tⁿ_k}` for all
> `t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)`, for all `k ≥ 1`." (3.32)

This is exactly the time change `ContinuousTimeChain.jumpPath` applied to the pair
`((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)`, so `map_embeddedPairOf` identifies the one-time marginals of `X̃ⁿ`
with those of the constructed process `Xⁿ` of (3.15) — the *same* family of laws `q` that
`ContinuousTimeChain.chainFamily_transition` computes, which is what
`UniquenessLimit.ApproximatedBy` requires of both sides. -/

section ProcessTildeN

/-- **(3.32)**: the process `X̃ⁿ` read off the embedded chain of (3.31) and its holding times,
`X̃ⁿ_t = X̃_{tⁿ_k}` for the unique `k` with `t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)`. -/
noncomputable def processTildeN (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (v₀ : V) (t : ℝ≥0)
    (ω : Ω) : Option V :=
  ContinuousTimeChain.jumpPath (embeddedPairOf X Gn v₀ ω) t

omit mΩ in
/-- The holding time `Tⁿ_j` is finite as soon as `tⁿ_{j+1}` is. -/
lemma holdingTime_ne_top {Gn : Finset V} {j : ℕ} {ω : Ω}
    (hfin : stepTime X Gn (j + 1) ω ≠ ⊤) : holdingTime X Gn j ω ≠ ⊤ := by
  have hex : exitAfter X (stepTime X Gn j) ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (exitAfter_le_stepTime_succ Gn j ω)
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hex
  cases hb : stepTime X Gn j ω with
  | top =>
    have htop : exitAfter X (stepTime X Gn j) ω = ⊤ := hitAfter_top hb
    exact absurd htop hex
  | coe b =>
    rw [holdingTime, ← ha, hb, ← WithTop.coe_sub]
    exact WithTop.coe_ne_top

omit mΩ in
/-- The clock of (3.32) is the partial sum of the holding times of (3.31). -/
lemma jumpClock_holdingSeqOf (Gn : Finset V) {ω : Ω}
    (hfin : ∀ j, holdingTime X Gn j ω ≠ ⊤) (k : ℕ) :
    ContinuousTimeChain.jumpClock (holdingSeqOf X Gn ω) k =
      ∑ j ∈ Finset.range k, holdingTime X Gn j ω :=
  Finset.sum_congr rfl fun j _ => ENNReal.ofReal_toReal (hfin j)

omit mΩ in
/-- **(3.32), explicitly.**  `X̃ⁿ_t = X̃_{tⁿ_k}` whenever
`t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)`. -/
theorem processTildeN_eq_of_mem_Ico (Gn : Finset V) (v₀ : V) {ω : Ω}
    (hfin : ∀ j, holdingTime X Gn j ω ≠ ⊤) {k : ℕ} {t : ℝ≥0}
    (h1 : ∑ j ∈ Finset.range k, holdingTime X Gn j ω ≤ (t : ℝ≥0∞))
    (h2 : (t : ℝ≥0∞) < ∑ j ∈ Finset.range (k + 1), holdingTime X Gn j ω) :
    processTildeN X Gn v₀ t ω =
      some ((stoppedValue X (stepTime X Gn k) ω).getD v₀) := by
  refine ContinuousTimeChain.jumpPath_eq_of_inJump ?_
  exact ⟨by rw [show ((embeddedPairOf X Gn v₀ ω).2) = holdingSeqOf X Gn ω from rfl,
      jumpClock_holdingSeqOf Gn hfin]; exact h1,
    by rw [show ((embeddedPairOf X Gn v₀ ω).2) = holdingSeqOf X Gn ω from rfl,
      jumpClock_holdingSeqOf Gn hfin]; exact h2⟩

section Marginals

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {𝓧 : ProcessFamily V}

/-- **The one-time marginals of `X̃ⁿ`.**  They are computed from the law of the pair, hence are
the one-time marginals of the constructed process `Xⁿ` of (3.15). -/
theorem measure_processTildeN (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) {Gn : Finset V} (hGn : Gn.Nonempty)
    (z v₀ : V) (t : ℝ≥0) (y : V) :
    𝓧.P z {ω | processTildeN 𝓧.X Gn v₀ t ω = some y} =
      (MarkovChain.chainLaw (G.stepKernel hG hGn) z ⊗ₘ holdingKernel w)
        {p : (ℕ → V) × (ℕ → ℝ) | ContinuousTimeChain.jumpPath p t = some y} := by
  have hdef : ∀ k : ℕ, ∀ᵐ ω ∂𝓧.P z, ∃ x : V,
      stoppedValue 𝓧.X (stepTime 𝓧.X Gn k) ω = some x := by
    intro k
    filter_upwards [ae_forall_definedAt h hG z hR hGn] with ω hω
    exact ((mem_definedAt_iff Gn k ω).1 (hω k)).2
  have hpairm : AEMeasurable (embeddedPairOf 𝓧.X Gn v₀) (𝓧.P z) :=
    aemeasurable_embeddedPairOf 𝓧.measurable_X (h z).2.2.1 (hR z) Gn v₀ hdef
  have hsy : MeasurableSet
      {p : (ℕ → V) × (ℕ → ℝ) | ContinuousTimeChain.jumpPath p t = some y} :=
    ContinuousTimeChain.measurable_jumpPath t (measurableSet_singleton (some y))
  rw [← map_embeddedPairOf h hG hw hR hGn z v₀,
    Measure.map_apply_of_aemeasurable hpairm hsy]
  rfl

/-- **The two halves of the uniqueness comparison meet.**  The one-time marginals of the process
`X̃ⁿ` of (3.32), built from an **arbitrary** process satisfying (i)–(vi), agree with those of the
constructed process `Xⁿ` of (3.15) (`ContinuousTimeChain.chainFamily`).  This is the common
family of laws `q` that `UniquenessLimit.ApproximatedBy` requires of both sides:
`q x n t y = (E.chainLaw hG (E.nz x + n) x ⊗ₘ holdingKernel w) {p | jumpPath p t = some y}`. -/
theorem measure_processTildeN_eq_chainFamily (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) (E : G.Exhaustion) (i : ℕ) (z v₀ : V)
    (t : ℝ≥0) (y : V) :
    𝓧.P z {ω | processTildeN 𝓧.X (E.Gsub (E.nz z + i)) v₀ t ω = some y} =
      (ContinuousTimeChain.chainFamily E w hG i).P z
        {ω | (ContinuousTimeChain.chainFamily E w hG i).X t ω = some y} := by
  rw [ContinuousTimeChain.chainFamily_transition E w hG hw i z t y,
    measure_processTildeN h hG hw hR (E.nonempty (E.nz z + i)) z v₀ t y]
  rfl

/-- A genuinely measurable version of (3.32) with the same one-time marginals: the form in which
`UniquenessLimit.ApproximatedBy` consumes `X̃ⁿ` (which asks for measurable time sections, while
`stoppedValue` at the stopping times of (3.31) is only measurable up to null sets). -/
theorem exists_measurable_processTildeN (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ x, 0 < w x)
    (hR : ∀ v, RightContinuousAtInfty (𝓧.P v) 𝓧.X) (E : G.Exhaustion) (z v₀ : V) :
    ∃ Xn : ℕ → ℝ≥0 → 𝓧.Ω → Option V, (∀ i s, Measurable (Xn i s)) ∧
      (∀ i : ℕ, ∀ᵐ ω ∂𝓧.P z, ∀ t : ℝ≥0,
        Xn i t ω = processTildeN 𝓧.X (E.Gsub (E.nz z + i)) v₀ t ω) ∧
      ∀ (i : ℕ) (t : ℝ≥0) (y : V), 𝓧.P z {ω | Xn i t ω = some y} =
        (E.chainLaw hG (E.nz z + i) z ⊗ₘ holdingKernel w)
          {p : (ℕ → V) × (ℕ → ℝ) | ContinuousTimeChain.jumpPath p t = some y} := by
  have hdef : ∀ (i k : ℕ), ∀ᵐ ω ∂𝓧.P z, ∃ x : V,
      stoppedValue 𝓧.X (stepTime 𝓧.X (E.Gsub (E.nz z + i)) k) ω = some x := by
    intro i k
    filter_upwards [ae_forall_definedAt h hG z hR (E.nonempty (E.nz z + i))] with ω hω
    exact ((mem_definedAt_iff (E.Gsub (E.nz z + i)) k ω).1 (hω k)).2
  have hpairm : ∀ i : ℕ,
      AEMeasurable (embeddedPairOf 𝓧.X (E.Gsub (E.nz z + i)) v₀) (𝓧.P z) := fun i =>
    aemeasurable_embeddedPairOf 𝓧.measurable_X (h z).2.2.1 (hR z) (E.Gsub (E.nz z + i)) v₀
      (hdef i)
  refine ⟨fun i t ω => ContinuousTimeChain.jumpPath ((hpairm i).mk _ ω) t,
    fun i s => (ContinuousTimeChain.measurable_jumpPath s).comp (hpairm i).measurable_mk,
    fun i => ?_, fun i t y => ?_⟩
  · filter_upwards [(hpairm i).ae_eq_mk] with ω hω t
    show ContinuousTimeChain.jumpPath ((hpairm i).mk _ ω) t =
      ContinuousTimeChain.jumpPath (embeddedPairOf 𝓧.X (E.Gsub (E.nz z + i)) v₀ ω) t
    rw [hω]
  · have hset : {ω | ContinuousTimeChain.jumpPath ((hpairm i).mk _ ω) t = some y} =ᵐ[𝓧.P z]
        {ω | processTildeN 𝓧.X (E.Gsub (E.nz z + i)) v₀ t ω = some y} := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [(hpairm i).ae_eq_mk] with ω hω
      simp only [processTildeN, hω]
    rw [measure_congr hset,
      measure_processTildeN h hG hw hR (E.nonempty (E.nz z + i)) z v₀ t y]
    rfl

end Marginals

end ProcessTildeN

end Theorem16
end ReflectedWalk

