/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Theorem16Statement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Harmonic
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.HittingTime

/-!
# Theorem 1.6 of Gwynne–Sung, stated (arXiv:2506.18827, Section 1.3, p. 5)

This file states — and does not prove — Theorem 1.6: existence and uniqueness in law of
the *continuous-time random walk on `G` reflected off of infinity*.  It follows the
repository precedent `BouRabeeGwynne.TheoremBStatement`: `Theorem16Statement` is a
`def … : Prop` carrying no proof.  There is no `sorry`, no `axiom`, no placeholder.

The English text this file is answerable to is the Theorem 1.6 section of
`THEOREM_STATEMENTS_ENGLISH.md`, including its binding reading notes.

## The object: a process with a family of starting laws

The paper writes "for each starting point `z ∈ VG` … there is a unique (in law) process
`X` with `X₀ = z`", but property (iv) refers to "the law of `{X_s}` started from `x`" for
*every* vertex `x`, and Lemma 3.10 (p. 25) makes the convention explicit: "for `z ∈ VG`,
write `P_z` for the law of `X` started at `z`".  The uniqueness proof (pp. 25–26) likewise
takes "another process `X̃` … [and] the probability measure `P_z` where `X̃` starts at
`z`".  So the mathematical object is a *Markov family*

  `(Ω, 𝓕, (X_t)_{t ≥ 0}, (P_z)_{z ∈ VG})`

— one measurable space, one process, one probability measure per starting point — and
property (iv) for the process under `P_z` refers to the `P_x`-law of the same process.
`ProcessFamily` is exactly this object.  Existence means a family with properties
(i)–(vi) under every `P_z` exists; **uniqueness in law** means any two such families
have identically distributed trajectories under `P_z`, for every `z`
(`ProbabilityTheory.IdentDistrib`).  Nothing is claimed about uniqueness of the process as
a function, in accordance with the reading note.

## State space and path space

* `VG ∪ {∞}` is `Option V`: `some x` is the vertex `x`, `none` is the single adjoined
  point `∞` of Remark 1.7.  Its σ-algebra is the full power set (`⊤`), the only sensible
  σ-algebra on a countable discrete set.  `∞` is *not* refined into ends (Proposition 5.3
  is out of scope).
* The time index `[0,∞)` is `ℝ≥0`.
* A trajectory is a function `ℝ≥0 → Option V`, and the path space `Trajectory V` carries
  the product (cylinder) σ-algebra `MeasurableSpace.pi`.

## The reading of "unique (in law)" — recorded for `STATEMENT_SPEC.md`

The conclusion of `Theorem16Statement` is `ProbabilityTheory.IdentDistrib`: the two
processes have the same law on the path space `Trajectory V` with its cylinder
σ-algebra.  By mathlib's `ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq`
(and its `IdentDistrib` form `identDistrib_iff_forall_finset_identDistrib`, both in
`Mathlib/Probability/Process/FiniteDimensionalLaws.lean`) this holds if and only if all
finite-dimensional distributions `(X_{t₁}, …, X_{tₙ})` agree.  Equality of
finite-dimensional distributions is the standard meaning of "two stochastic processes
have the same law", and it is the paper's: the uniqueness proof (pp. 25–26) concludes
"`X̃ =ᵈ X`", and Section 3.4 introduces the metric space `L¹_loc([0,∞), VG ∪ {∞})` of
Definition 3.9 (p. 24) only as a proof device ("for technical reasons it is convenient to
work with a topology"), to pass to the limit `X̃ⁿ → X̃` in law.  Under property (i) the
`L¹_loc`-law and the finite-dimensional distributions determine each other (each `X_t` is
a.s. the a.e.-constant value of the trajectory near `t`; conversely the `L¹_loc`-class is
a.s. a function of the values at rational times), so the paper's argument delivers
exactly the clause formalised here.  No other notion of uniqueness is used or added.
Mathlib has no Skorokhod or `L¹_loc` path space, and this file does not depend on the
`L1loc` package.

## Why the a.s. properties live on `Ω`, not on path space

Properties (ii) and (v) quantify over *all* times `t`, and the corresponding sets of
trajectories are not measurable for the cylinder σ-algebra; worse, the set of
trajectories violating (ii) has outer measure `1` under the law of the paper's own
process (any cylinder set containing a trajectory with a one-point modification contains
the unmodified trajectory).  So "almost surely" in (ii) and (v) must be read on the
underlying probability space, as `∀ᵐ ω ∂P`, exactly as the paper does.  This is why the
statement is about processes on probability spaces and not merely about laws.

## The `∞`-side of property (ii) — the one approved modification of the printed statement

The printed property (ii) constrains the path only at times `t` with `X_t ∈ VG`.  The state
space is `VG ∪ {∞}`, and right continuity of a path into `VG ∪ {∞}` — the one-point
compactification of the discrete set `VG`, the only topology under which "right continuity"
of a `VG ∪ {∞}`-valued path has a meaning — has a second half that the printed text omits:
at a time `t` with `X_t = ∞`, every vertex `y` must be avoided on some `(t, t + ε)`.  That
half is `Theorem16.RightContinuousAtInfty`, and `IsReflectedWalk` carries it as a conjunct
immediately after `RightContinuous`, so that (ii) is present in its complete form.

**This clause is not in the printed (ii).**  It is the only place where the formal statement
departs from the printed one; the departure is deliberate, user-approved, and recorded in
`STATEMENT_SPEC.md`.  The reasons:

* **Without it the class (i)–(vi) contains single-time kills.**  `Lemma311.not_hR` proves
  that for every countably infinite connected `G` and every energy minimiser there is a
  process satisfying the printed (i)–(vi) verbatim which is *not* right continuous at `∞`:
  the constructed walk with `X_m := ∞` at the (atomless) start `m` of the first return
  sojourn to the starting vertex.  Property (i) survives because `m` is atomless, (ii)
  because it is vacuous at `∞`-times, (iii) because it sees only the first exit (before
  `m`), (vi) because it sees only *first hits* of finite sets and `m` is a *return*, and
  (v) trivially.  So under the printed clauses alone the class is strictly larger than the
  paper's, and the paper's proof does not apply to its pathological members.
* **The paper's own proof uses the clause.**  The proof of Lemma 3.11 (p. 27) takes
  `τ_k(x)` to be the *smallest* `s` with `X_s = x` and applies Lemma 3.10 on
  `{X_{τ_k} = x}`; that the infimum is attained is exactly the left-closedness of the visit
  set that Assertion 1 asserts, which is this clause.  Step 1 of the uniqueness proof
  (p. 25) applies Lemma 3.10 at the hitting times (3.31), which are stopping times of the
  natural filtration only for paths right continuous into `VG ∪ {∞}` (`StrongMarkov.lean`).
* **It does not alter the conclusion.**  The clause is pathwise: a single-time kill leaves
  every finite-dimensional distribution unchanged, so uniqueness *in law* is untouched.  The
  clause only fixes which processes the theorem quantifies over, in accordance with what
  "right continuity" means for a `VG ∪ {∞}`-valued path.  The constructed process has it
  (`Existence.rightContinuousAtInfty`, from `RightContinuityAtInfty.lean`), so the
  existence half is unaffected.

## Hitting times

`τ := min{t > 0 : X_t ≠ z}` in (iii) and `τ := min{t ≥ 0 : X_t ∈ A}` in (vi) are
rendered with mathlib's `MeasureTheory.hittingAfter`, which returns the infimum of the
hitting set and `⊤` when the set is empty, so the empty case is explicit.  The paper's
`min` (rather than `inf`) presupposes that the hitting time is finite and attained; where
this presupposition is not already forced by the other clauses it is stated explicitly
(see `HarmonicHitting`).  Junk values of `stoppedValue` at `τ = ⊤` only ever occur on
events these clauses make null.

## Property (iv)

Mathlib's regular conditional distribution `ProbabilityTheory.condDistrib` requires a
standard Borel target; the path space with the cylinder σ-algebra is not standard Borel,
so the conditional law of the whole future cannot be phrased through it.  We use the
equivalent joint-law form, which is the convention of
`BouRabeeGwynne.WalkStrongMarkov`: on the event `{X_t = x}`, the joint law of
`({X_s}_{s ≤ t}, {X_{s+t}}_{s ≥ 0})` is the product of the law of the past and the
`P_x`-law of the process.  Restricting to the event and factorising is precisely the
statement that the conditional law of the future given the past is `P_x` on `{X_t = x}`,
and it is equivalent to the `condDistrib` statement on every finite-dimensional marginal.

## Property (vi) and Proposition 1.3

Property (vi) refers to the energy-minimising function `h_ϕ` of Proposition 1.3.  That
function is delivered by Contract A (`energyMin`) concurrently, so this file does not
import it. Instead `ConductanceGraph.EnergyMinimizer` bundles a function
`Finset V → (V → ℝ) → V → ℝ` with the three properties that characterise `h_ϕ` (agrees
with `ϕ` on `A`, finite energy, minimal energy among finite-energy competitors — the
shape of Contract A's `energyMin_eqOn`, `energyMin_hasFiniteEnergy`,
`energyMin_le_energy`).  Contract A's `energyMin_unique` shows any such bundle *is*
`energyMin` on non-empty `A`, so the statement is the same for every bundle.  Once
Contract A lands, the instantiation is the one-liner

  `Theorem16Statement G ⟨G.energyMin hG, G.energyMin_eqOn hG,
      G.energyMin_hasFiniteEnergy hG, G.energyMin_le_energy hG⟩`.

## Hypothesis on `w`

The printed theorem requires `w(x) ≥ w*(x)` for **all** `x ∈ VG`; the paper's proof
(Lemma 3.5, p. 22) only uses it for all but finitely many `x`.  We formalise the printed,
stronger hypothesis (`∀ x, wstar x ≤ w x`), as the reading notes require.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

namespace ReflectedWalk

variable {V : Type u}

/-- The state space `VG ∪ {∞}` of Theorem 1.6 is the countable discrete set `Option V`
(`some x` a vertex, `none` the single point `∞` of Remark 1.7).  Its σ-algebra is the full
power set. -/
scoped instance instMeasurableSpaceOption (V : Type u) : MeasurableSpace (Option V) := ⊤

/-- A trajectory `[0,∞) → VG ∪ {∞}`.  As a type this is the path space of Theorem 1.6,
carrying the product (cylinder) σ-algebra `MeasurableSpace.pi`. -/
abbrev Trajectory (V : Type u) : Type u := ℝ≥0 → Option V

/-- A continuous-time stochastic process `X : [0,∞) → VG ∪ {∞}` together with a family of
probability measures `P z`, one for each starting point `z ∈ VG`: the Markov-family setup
of Lemma 3.10 ("write `P_z` for the law of `X` started at `z`").  Each `X t` is a random
variable, i.e. measurable, which is what "stochastic process" means. -/
structure ProcessFamily (V : Type u) : Type (u + 1) where
  /-- The sample space. -/
  Ω : Type u
  [mΩ : MeasurableSpace Ω]
  /-- The process: `X t ω` is the position at time `t` in outcome `ω`. -/
  X : ℝ≥0 → Ω → Option V
  measurable_X : ∀ t, Measurable (X t)
  /-- `P z` is the probability measure under which the process starts at `z`. -/
  P : V → Measure Ω
  [isProbabilityMeasure : ∀ z, IsProbabilityMeasure (P z)]

attribute [instance] ProcessFamily.mΩ ProcessFamily.isProbabilityMeasure

namespace ProcessFamily

variable (𝓧 : ProcessFamily V)

/-- The trajectory `{X_t}_{t ≥ 0}` of the outcome `ω`. -/
def trajectory (ω : 𝓧.Ω) : Trajectory V := fun t => 𝓧.X t ω

/-- The law of `{X_t}_{t ≥ 0}` started from `z`: the pushforward of `P z` to path space.
This is the "`P_x`-law of `{X_s}_{s ≥ 0}`" that property (iv) refers to. -/
noncomputable def law (z : V) : Measure (Trajectory V) := (𝓧.P z).map 𝓧.trajectory

end ProcessFamily

namespace Theorem16

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Property (i) (Almost everywhere defined).**  For each `t ≥ 0`, a.s. `X_t ∈ VG` and
there is `ε > 0` with `X_s = X_t` for every `s ∈ (t − ε, t + ε)`.  The interval is
`Metric.ball t ε` in `ℝ≥0`, i.e. `(t − ε, t + ε) ∩ [0,∞)`, which is what the paper's
`s ∈ (t−ε, t+ε)` means for a process defined on `[0,∞)`.  The quantifier order is the
paper's: the null set may depend on `t`. -/
def AlmostEverywhereDefined (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
    (∃ x : V, X t ω = some x) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, X s ω = X t ω

/-- **Property (ii) (Right continuity).**  Almost surely, for every `t ≥ 0` with
`X_t ∈ VG` there is `ε > 0` with `X_s = X_t` for every `s ∈ [t, t + ε)`.  The paper
prints the closed interval `[t, t + ε]`; the two forms are equivalent (halve `ε`).  A
single null set serves all `t`, as in the paper ("almost surely, for every `t`"). -/
def RightContinuous (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∃ x : V, X t ω = some x) →
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω

/-- **The `∞`-side of property (ii) (Right continuity at `∞`).**  Almost surely, for every
`t ≥ 0` with `X_t = ∞` and every vertex `y`, there is `ε > 0` with `X_s ≠ y` for all
`s ∈ (t, t + ε)`.  A single null set serves all `t` and all `y`, as in (ii).

**This clause is not in the printed property (ii).**  The printed (ii) constrains the path
only at times where `X_t ∈ VG`; this clause is the other half of right continuity of the
path into the one-point compactification `VG ∪ {∞}` (`VG` discrete): together the two say
that `X_{t_k} → X_t` for every `t_k ↓ t`, i.e. for every vertex `y`, `X_{t_k} = y`
eventually iff `X_t = y`.  It is a conjunct of `IsReflectedWalk`, immediately after
`RightContinuous`, by an approved modification of the theorem statement recorded in the
module docstring and in `STATEMENT_SPEC.md`: without it the class (i)–(vi) contains
single-time kills (`Lemma311.not_hR` exhibits one for every countably infinite connected
`G`), and the paper's own Lemma 3.11 (attainment of `τ_k(x) = min{s : X_s = x}`) and Step 1
of its uniqueness proof (Lemma 3.10 at the hitting times (3.31)) both use it.  See
`StrongMarkov.lean` for how Lemma 3.10 consumes it. -/
def RightContinuousAtInfty (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = none →
    ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y

/-- The first exit time `τ := min{t > 0 : X_t ≠ z}` of property (iii), as
`MeasureTheory.hittingAfter`: the infimum of `{t ≥ 0 : X_t ≠ z}`, or `⊤` if that set is
empty.  The infimum runs over `t ≥ 0` rather than `t > 0`; on the event `{X_0 = z}`,
which has full measure for the process started at `z`, the two sets coincide. -/
noncomputable def exitTime (X : ℝ≥0 → Ω → Option V) (z : V) : Ω → WithTop ℝ≥0 :=
  hittingAfter X {s | s ≠ some z} 0

/-- The inclusion `[0,∞) → [0,∞]` along which the exponential law is pushed forward in
`ExponentialFirstStep`. -/
noncomputable def toWithTop (r : ℝ) : WithTop ℝ≥0 := (r.toNNReal : WithTop ℝ≥0)

/-- **Property (iii) (Continuous-time random walk).**  With `τ := min{t > 0 : X_t ≠ z}`
(`exitTime X z`) and `X_τ := stoppedValue X τ`:
* `τ` and `X_τ` are random variables (a.e.-measurable) — presupposed by the paper in
  speaking of their laws and independence — and they are independent
  (`ProbabilityTheory.IndepFun`);
* `τ` has the exponential distribution with rate `w z`: its law on `[0,∞]` is the image
  of `expMeasure (w z)` (density `w z · exp(−w z · t)` on `t ≥ 0`) under
  `[0,∞) ↪ [0,∞]`.  In particular `τ < ∞` almost surely;
* `X_τ` has the law of one step of the random walk on `G` from `z`:
  `P[X_τ = x] = c(z,x)/π(z)` for every vertex `x`.  For `x ≁ z` this reads
  `P[X_τ = x] = 0`, and since the probabilities sum to `1` it forces `P[X_τ = ∞] = 0`;
  this is what "the law of a step of the random walk" means. -/
def ExponentialFirstStep (G : ConductanceGraph V) (w : V → ℝ) (z : V)
    (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  AEMeasurable (exitTime X z) P ∧
  AEMeasurable (stoppedValue X (exitTime X z)) P ∧
  IndepFun (exitTime X z) (stoppedValue X (exitTime X z)) P ∧
  P.map (exitTime X z) = (expMeasure (w z)).map toWithTop ∧
  ∀ x : V, P {ω | stoppedValue X (exitTime X z) ω = some x} = ENNReal.ofReal (G.c z x / G.pi z)

/-- The past `{X_s}_{s ≤ t}` of the outcome `ω`, as a random element of the product space
`Set.Iic t → Option V`.  Its σ-algebra pulled back to `Ω` is the natural filtration
`σ(X_s : s ≤ t)`. -/
def pastPath (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) (ω : Ω) : Set.Iic t → Option V :=
  fun s => X s ω

/-- The future `{X_{s+t}}_{s ≥ 0}` of the outcome `ω`, as a trajectory. -/
def shiftedPath (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) (ω : Ω) : Trajectory V :=
  fun s => X (s + t) ω

/-- **Property (iv) (Markov property).**  For every `t ≥ 0` and `x ∈ VG`, on the event
`{X_t = x}` the conditional law of `{X_{s+t}}_{s ≥ 0}` given `{X_s}_{s ≤ t}` is `μ x`,
the law of the process started from `x` (`ProcessFamily.law x` when instantiated).

Stated in joint-law form: under `P` restricted to `{X_t = x}`, the pair
`(past, future) = ({X_s}_{s ≤ t}, {X_{s+t}}_{s ≥ 0})` has the product law
`(law of the past) ⊗ μ x`.  Evaluated on a rectangle `S ×ˢ B` this is
`P(F ∩ {X_t = x} ∩ {X_{·+t} ∈ B}) = P(F ∩ {X_t = x}) · μ x (B)` for every `F` in
`σ(X_s : s ≤ t)` and every cylinder-measurable `B`, which is the textbook definition of
the Markov property at time `t`; rectangles generate the product σ-algebra, so the two
readings are equivalent.  See the module docstring for why `condDistrib` is not used. -/
def MarkovProperty (μ : V → Measure (Trajectory V)) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ (t : ℝ≥0) (x : V),
    (P.restrict {ω | X t ω = some x}).map (fun ω => (pastPath X t ω, shiftedPath X t ω)) =
      ((P.restrict {ω | X t ω = some x}).map (pastPath X t)).prod (μ x)

/-- **Property (v) (Recurrence).**  Almost surely there are arbitrarily large `t ≥ 0`
with `X_t = z`. -/
def Recurrent (z : V) (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ t : ℝ≥0, T ≤ t ∧ X t ω = some z

/-- The hitting time `τ := min{t ≥ 0 : X_t ∈ A}` of property (vi), as
`MeasureTheory.hittingAfter`: the infimum of `{t ≥ 0 : X_t ∈ A}`, or `⊤` if `A` is never
hit. -/
noncomputable def hittingTime (X : ℝ≥0 → Ω → Option V) (A : Finset V) : Ω → WithTop ℝ≥0 :=
  hittingAfter X (some '' (A : Set V)) 0

end Theorem16

/-- The energy-minimising extension of Proposition 1.3, abstracted: a function
`A ↦ ϕ ↦ h_ϕ` together with the three properties that characterise `h_ϕ` for non-empty
finite `A` — `h_ϕ|_A = ϕ`, `Energy(h_ϕ) < ∞`, and `Energy(h_ϕ) ≤ Energy(f)` for every
finite-energy `f` with `f|_A = ϕ`.  Minimality is stated against finite-energy competitors
only, for the reason recorded in `INTERFACES.md` (`Energy` of a non-summable family is
junk-valued `0`).  The fields have exactly the types of Contract A's `energyMin_eqOn`,
`energyMin_hasFiniteEnergy` and `energyMin_le_energy`, so
`⟨G.energyMin hG, G.energyMin_eqOn hG, G.energyMin_hasFiniteEnergy hG,
  G.energyMin_le_energy hG⟩` is an `EnergyMinimizer` once Contract A lands; by
`energyMin_unique` every `EnergyMinimizer` agrees with `energyMin` on non-empty `A`. -/
structure ConductanceGraph.EnergyMinimizer (G : ConductanceGraph V) : Type u where
  /-- `(A, ϕ) ↦ h_ϕ`; the paper's `ϕ : A → ℝ` is carried as a total function of which
  only the restriction to `A` matters. -/
  toFun : Finset V → (V → ℝ) → V → ℝ
  /-- `h_ϕ|_A = ϕ`. -/
  eqOn : ∀ {A : Finset V}, A.Nonempty → ∀ φ : V → ℝ, Set.EqOn (toFun A φ) φ ↑A
  /-- `h_ϕ` has finite Dirichlet energy. -/
  hasFiniteEnergy : ∀ {A : Finset V}, A.Nonempty → ∀ φ : V → ℝ, G.HasFiniteEnergy (toFun A φ)
  /-- `Energy(h_ϕ)` is minimal among finite-energy `f` with `f|_A = ϕ`. -/
  le_energy : ∀ {A : Finset V}, A.Nonempty → ∀ φ : V → ℝ, ∀ {f : V → ℝ},
    G.HasFiniteEnergy f → Set.EqOn f φ ↑A → G.Energy (toFun A φ) ≤ G.Energy f

instance {G : ConductanceGraph V} :
    CoeFun G.EnergyMinimizer (fun _ => Finset V → (V → ℝ) → V → ℝ) :=
  ⟨ConductanceGraph.EnergyMinimizer.toFun⟩

namespace Theorem16

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Property (vi) (Relation to harmonic functions).**  For every non-empty finite
`A ⊆ VG` and `ϕ : A → ℝ` (carried as a total `φ : V → ℝ`, only `φ|_A` matters), with
`h_ϕ` the energy-minimising function of Proposition 1.3 and `τ := min{t ≥ 0 : X_t ∈ A}`
(`hittingTime X A`):

  `h_ϕ(z) = E_z[ϕ(X_τ)]`.

Writing `min` and `E_z[ϕ(X_τ)]` presupposes that `τ` is a.s. finite and attained with
`X_τ ∈ A`; both are stated explicitly (they do not depend on `ϕ`), following the
convention of `BouRabeeGwynne.IsStoppedTilingWalkLaw`.  The integrand `(X_τ).elim 0 φ`
evaluates `φ` at the vertex `X_τ`; by the attainment clause `X_τ ∈ A` a.s., so only
`φ|_A` enters and the value `0` at `∞` is never used on a non-null set.  The
`z`-dependence ("for each choice of starting point `z`") is supplied by the measure `P`,
which is `P_z` when instantiated.

The `Integrable` conjunct makes the expectation `E_z[φ(X_τ)]` meaningful rather than
leaving it to a junk value: mathlib's Bochner integral of a non-integrable function is
`0`, so without it the identity could be discharged by the junk value rather than by the
mathematics.  It is not a strengthening of the paper: by the attainment clause `X_τ ∈ A`
almost surely and `A` is finite, so the integrand is a.s. bounded and integrability is
equivalent to measurability, which the paper's `E_z[·]` presupposes. -/
def HarmonicHitting (G : ConductanceGraph V) (hmin : G.EnergyMinimizer) (z : V)
    (P : Measure Ω) (X : ℝ≥0 → Ω → Option V) : Prop :=
  ∀ (A : Finset V), A.Nonempty →
    (∀ᵐ ω ∂P, hittingTime X A ω ≠ ⊤ ∧
      stoppedValue X (hittingTime X A) ω ∈ some '' (A : Set V)) ∧
    ∀ φ : V → ℝ,
      Integrable (fun ω => (stoppedValue X (hittingTime X A) ω).elim 0 φ) P ∧
        hmin A φ z = ∫ ω, (stoppedValue X (hittingTime X A) ω).elim 0 φ ∂P

end Theorem16

/-- `𝓧` is a continuous-time random walk on `G` reflected off of infinity with rate
function `w`: for every starting point `z`, under `P z` the process starts at `z` and
satisfies properties (i)–(vi) of Theorem 1.6 — property (ii) in its complete form, i.e.
`RightContinuous` together with its `∞`-side `Theorem16.RightContinuousAtInfty` (**not in
the printed (ii)**; an approved modification of the statement, see the module docstring and
the docstring of `RightContinuousAtInfty`) — property (iv) referring to the family's own
laws `𝓧.law x`.

Conjunct order: `X_0 = z`, (i), (ii), (ii at `∞`), (iii), (iv), (v), (vi). -/
def IsReflectedWalk (G : ConductanceGraph V) (w : V → ℝ) (hmin : G.EnergyMinimizer)
    (𝓧 : ProcessFamily V) : Prop :=
  ∀ z : V,
    (∀ᵐ ω ∂𝓧.P z, 𝓧.X 0 ω = some z) ∧
    Theorem16.AlmostEverywhereDefined (𝓧.P z) 𝓧.X ∧
    Theorem16.RightContinuous (𝓧.P z) 𝓧.X ∧
    Theorem16.RightContinuousAtInfty (𝓧.P z) 𝓧.X ∧
    Theorem16.ExponentialFirstStep G w z (𝓧.P z) 𝓧.X ∧
    Theorem16.MarkovProperty 𝓧.law (𝓧.P z) 𝓧.X ∧
    Theorem16.Recurrent z (𝓧.P z) 𝓧.X ∧
    Theorem16.HarmonicHitting G hmin z (𝓧.P z) 𝓧.X

/-- **Theorem 1.6** (Gwynne–Sung, p. 5), as an unproved target.

For a countably infinite connected conductance graph `G` (with `π(x) < ∞`, which is part
of `ConductanceGraph`): there exists a rate function `w* : VG → (0,∞)` such that for every
`w : VG → (0,∞)` with `w(x) ≥ w*(x)` for **all** `x ∈ VG` and every starting point
`z ∈ VG`, there is a process `X : [0,∞) → VG ∪ {∞}` with `X₀ = z` satisfying (i)–(vi),
and it is **unique in law** among processes satisfying (i)–(vi).  Here (i)–(vi) are read
with property (ii) in its complete form, i.e. together with its `∞`-side
`Theorem16.RightContinuousAtInfty`; this is the only departure from the printed statement,
it is approved, and it is recorded in the module docstring and in `STATEMENT_SPEC.md`.

The quantifiers follow the printed sentence.  "A process satisfying (i)–(vi)" is a
`ProcessFamily` with `IsReflectedWalk`: the process under `𝓧.P z` starts at `z` and has
(i)–(vi), and — because property (iv) refers to the law started from every other vertex
`x` — it comes with its starting laws `𝓧.P x`, exactly as in the paper's Lemma 3.10.
"Unique in law" is `IdentDistrib` of the trajectories, i.e. equality of the laws on path
space, equivalently of all finite-dimensional distributions (module docstring); it is not
uniqueness as a function.

`hmin` abstracts the Proposition 1.3 minimiser used in property (vi); see
`ConductanceGraph.EnergyMinimizer` for the instantiation with Contract A's `energyMin`.
The sample spaces of the process families range over `Type u`, the universe of `V`. -/
def Theorem16Statement (G : ConductanceGraph V) (hmin : G.EnergyMinimizer) : Prop :=
  Countable V → Infinite V → G.toSimpleGraph.Connected →
    ∃ wstar : V → ℝ, (∀ x, 0 < wstar x) ∧
      ∀ w : V → ℝ, (∀ x, 0 < w x) → (∀ x, wstar x ≤ w x) →
        ∀ z : V, ∃ 𝓧 : ProcessFamily V, IsReflectedWalk G w hmin 𝓧 ∧
          ∀ 𝓧' : ProcessFamily V, IsReflectedWalk G w hmin 𝓧' →
            IdentDistrib 𝓧'.trajectory 𝓧.trajectory (𝓧'.P z) (𝓧.P z)

end ReflectedWalk
