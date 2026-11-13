/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.StrongMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Theorem16Statement
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Algebra.Order.Nonneg.Floor
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Filter.CountableInter

/-!
# Lemma 3.10 of Gwynne–Sung (arXiv:2506.18827, p. 25): the strong Markov property

> **Lemma 3.10.** Let `X : [0,∞) → VG ∪ {∞}` be a process satisfying the properties in
> Theorem 1.6 and for `z ∈ VG` write `P_z` for the law of `X` started at `z`.  Let `τ` be a
> stopping time for `{X_t}_{t ≥ 0}` and let `x ∈ VG`.  On the event `{τ < ∞, X_τ = x}`, the
> `P_z`-conditional law of `{X_{s+τ}}_{s ≥ 0}` given `{X_s}_{s ≤ τ}` is the same as the
> `P_x`-law of `{X_s}_{s ≥ 0}`.

The paper emphasises that this holds for **any** process satisfying the properties of
Theorem 1.6, not just the one constructed in (3.26).  Accordingly everything here is stated
for a `ProcessFamily` and consumes only the property predicates of `Theorem16Statement.lean`.

## What "stopping time for `{X_t}`" and "given `{X_s}_{s ≤ τ}`" mean here

* The **natural filtration** is `ℱ_t := σ(X_s : s ≤ t)`, realised as
  `pastSigma X t := comap (pastPath X t) pi` and packaged as the mathlib filtration
  `naturalFiltration X hX`.  A stopping time is a `MeasureTheory.IsStoppingTime` for it.
* Because (i)–(vi) are almost-sure statements on an arbitrary sample space, the specific
  stopping times of the paper (hitting times) are stopping times only *up to `P`-null sets*,
  i.e. for the `P`-completion of the natural filtration — the standard "usual" filtration of
  Markov process theory.  We therefore prove the lemma for this weaker notion,
  `IsAEStoppingTime`/`AEMeasurableSetStopped` (`{τ ≤ t}`, resp. `F ∩ {τ ≤ t}`, agrees
  `P`-a.s. with a set of `ℱ_t`), which contains the exact notion
  (`isAEStoppingTime_of_isStoppingTime`, `aemeasurableSetStopped_of_measurableSet`).
* "The conditional law of the future given the past is `P_x`" is stated in the rectangle
  form that is equivalent to the joint-law form used for property (iv) in
  `Theorem16Statement.MarkovProperty` (see its docstring): for every `F` in the stopped
  σ-algebra and every cylinder-measurable `B ⊆ Trajectory V`,

  `P_z (F ∩ {τ < ∞, X_τ = x} ∩ {X_{·+τ} ∈ B}) = P_z (F ∩ {τ < ∞, X_τ = x}) · P_x (B)`.

  `strongMarkov_joint` restates this as a factorisation of the joint law of
  `(past, future)` under `P_z` restricted to the event, the past coordinate being `Ω` with
  the stopped σ-algebra.

## The hypothesis `RightContinuousAtInfty`, and what it is for

Property (ii) controls the paths only at times where `X` is at a vertex; at times where
`X = ∞` it says nothing.  The paper's proof of Lemma 3.10 passes to the limit along
`τ_k ↓ τ` using `X_{s+τ_k} → X_{s+τ}` for every `s` — which needs the same control at the
times where the limit is `∞`.  `RightContinuousAtInfty` supplies exactly that: a.s., for
every `t` with `X_t = ∞` and every vertex `y`, `X ≠ y` on some `(t, t + ε)`.  Together with
(ii) it says that the paths are right-continuous into `VG ∪ {∞}` with its one-point
compactification topology, the natural meaning of "right continuity" for a `VG ∪ {∞}`-valued
path.  The process constructed in (3.26) has this property (`RightContinuityAtInfty.lean`,
the deterministic core of the paper's Lemma 3.11.1), so for it Lemma 3.10 holds with no
extra hypothesis (`Existence.strongMarkov`).

The clause is pathwise: modifying a process at a single random time of continuous law can
destroy it while preserving every finite-dimensional distribution, so it is not determined
by the law, and Theorem 1.6's conclusion — uniqueness *in law*, i.e. of the
finite-dimensional distributions — is unaffected by it.  For exactly this reason it is not
implied by the printed properties (i)–(vi) (`Lemma311.not_hR`), and it is therefore part of
the formal statement: `RightContinuousAtInfty` is defined in `Theorem16Statement.lean` and
is a conjunct of `IsReflectedWalk`, immediately after `RightContinuous`, as the `∞`-side of
property (ii) (an approved modification of the printed statement, documented there and in
`STATEMENT_SPEC.md`).  The lemmas of this file are stated for a bare process `X` under a
measure `P` and so take the clause as an explicit hypothesis `hR`; for a family `𝓧` with
`h : IsReflectedWalk G w hmin 𝓧` it is `(h z).2.2.2.1`.

## Proof architecture (the paper's, made explicit)

1. `strongMarkov_of_countable_range`: for a stopping time `σ` with countably many finite
   values, decompose over the values, use property (iv) at each deterministic time
   (`markov_rectangle`), and resum.
2. `dyadicApprox k τ = 2⁻ᵏ⌈2ᵏ τ⌉`, the smallest point of `[τ, ∞) ∩ 2⁻ᵏℕ`; it has countable
   range, `τ ≤ τ_k < τ + 2⁻ᵏ`, and inherits the stopping-time data from `τ`.
3. `strongMarkov_core`: by right continuity (ii)+(R), on the event, `X_{s+τ_k} = X_{s+τ}` for
   all large `k`, for every `s` (`eventually_futureAt_dyadicApprox_iff`).  Dominated
   convergence for indicator functions passes each vertex cylinder identity to the limit;
   the vertex cylinders form a π-system generating the cylinder σ-algebra
   (`generateFrom_vertexCylinders`), so the identity extends to all measurable `B`.

The state space is countable and discrete, so conditioning is on atoms and no
disintegration is needed anywhere: the whole argument is bookkeeping of
`P(· ∩ {X_τ = x})`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk
namespace Theorem16

variable {V : Type u} {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-! ### Measurability on the discrete state space -/

/-- Every subset of `VG ∪ {∞}` is measurable (the σ-algebra is `⊤`). -/
lemma measurableSet_option (s : Set (Option V)) : MeasurableSet s :=
  MeasurableSpace.measurableSet_top

/-- The past `{X_s}_{s ≤ t}` is a random element of `Set.Iic t → VG ∪ {∞}`. -/
lemma measurable_pastPath {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    Measurable (pastPath X t) :=
  measurable_pi_iff.2 fun s => hX s

/-- The future `{X_{s+t}}_{s ≥ 0}` at a deterministic time is a random trajectory. -/
lemma measurable_shiftedPath {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    Measurable (shiftedPath X t) :=
  measurable_pi_iff.2 fun s => hX (s + t)

/-! ### The natural filtration `σ(X_s : s ≤ t)` -/

set_option warn.classDefReducibility false in
/-- The σ-algebra `ℱ_t = σ(X_s : s ≤ t)` of the past up to time `t`, as the pullback of the
cylinder σ-algebra under `pastPath X t`. -/
def pastSigma (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (pastPath X t) MeasurableSpace.pi

lemma pastSigma_le {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    pastSigma X t ≤ mΩ :=
  measurable_iff_comap_le.1 (measurable_pastPath hX t)

omit mΩ in
lemma pastSigma_mono (X : ℝ≥0 → Ω → Option V) {s t : ℝ≥0} (hst : s ≤ t) :
    pastSigma X s ≤ pastSigma X t := by
  have h : pastPath X s =
      (fun (f : Set.Iic t → Option V) (u : Set.Iic s) => f ⟨u.1, le_trans u.2 hst⟩) ∘
        pastPath X t := rfl
  rw [pastSigma, pastSigma, h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (measurable_iff_comap_le.1 (measurable_pi_iff.2 fun u => measurable_pi_apply _))

omit mΩ in
lemma measurableSet_pastSigma_iff {X : ℝ≥0 → Ω → Option V} {t : ℝ≥0} {G : Set Ω} :
    MeasurableSet[pastSigma X t] G ↔
      ∃ S : Set (Set.Iic t → Option V), MeasurableSet S ∧ pastPath X t ⁻¹' S = G :=
  MeasurableSpace.measurableSet_comap

/-- The natural filtration `{σ(X_s : s ≤ t)}_{t ≥ 0}` of the process `X`; "a stopping time
for `{X_t}_{t ≥ 0}`" in Lemma 3.10 is a `MeasureTheory.IsStoppingTime` for it. -/
def naturalFiltration (X : ℝ≥0 → Ω → Option V) (hX : ∀ t, Measurable (X t)) :
    Filtration ℝ≥0 mΩ where
  seq := pastSigma X
  mono' _ _ hst := pastSigma_mono X hst
  le' := pastSigma_le hX

@[simp] lemma naturalFiltration_apply {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    (t : ℝ≥0) : naturalFiltration X hX t = pastSigma X t := rfl

/-! ### Stopping times up to null sets (the `P`-completion of the natural filtration) -/

/-- `τ` is a stopping time for the `P`-completion of `ℱ`: for every `t`, the event
`{τ ≤ t}` agrees `P`-a.s. with a set of `ℱ_t`.  Every genuine `ℱ`-stopping time qualifies
(`isAEStoppingTime_of_isStoppingTime`); so do the hitting times of a process whose regularity
is only almost sure, which a raw natural filtration cannot accommodate. -/
def IsAEStoppingTime (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, ∃ G : Set Ω, MeasurableSet[ℱ t] G ∧ {ω | τ ω ≤ (t : WithTop ℝ≥0)} =ᵐ[P] G

/-- `F` belongs to the stopped σ-algebra `ℱ_τ` of the `P`-completion of `ℱ`: for every `t`,
`F ∩ {τ ≤ t}` agrees `P`-a.s. with a set of `ℱ_t`.  This is the meaning of "given
`{X_s}_{s ≤ τ}`" in Lemma 3.10; it contains the exact `hτ.measurableSpace`
(`aemeasurableSetStopped_of_measurableSet`). -/
def AEMeasurableSetStopped (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (τ : Ω → WithTop ℝ≥0)
    (F : Set Ω) : Prop :=
  ∀ t : ℝ≥0, ∃ G : Set Ω, MeasurableSet[ℱ t] G ∧ F ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)} =ᵐ[P] G

lemma isAEStoppingTime_of_isStoppingTime {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (P : Measure Ω) : IsAEStoppingTime ℱ P τ :=
  fun t => ⟨_, hτ t, EventuallyEq.rfl⟩

lemma aemeasurableSetStopped_of_measurableSet {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) {F : Set Ω} (hF : MeasurableSet[hτ.measurableSpace] F)
    (P : Measure Ω) : AEMeasurableSetStopped ℱ P τ F :=
  fun t => ⟨_, ((hτ.measurableSet F).1 hF).2 t, EventuallyEq.rfl⟩

/-! ### The future at a stopping time and the event `{τ < ∞, X_τ = x}` -/

/-- The future `{X_{s+τ}}_{s ≥ 0}` of the outcome `ω` at the stopping time `τ`, as a
trajectory.  On `{τ = ∞}` the value is junk (`untopA`), matching `stoppedValue`. -/
noncomputable def futureAt (X : ℝ≥0 → Ω → Option V) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Trajectory V :=
  fun s => X (s + (τ ω).untopA) ω

/-- The event `{τ < ∞, X_τ = x}` of Lemma 3.10. -/
def stopEvent (X : ℝ≥0 → Ω → Option V) (τ : Ω → WithTop ℝ≥0) (x : V) : Set Ω :=
  {ω | τ ω ≠ ⊤ ∧ stoppedValue X τ ω = some x}

variable {X : ℝ≥0 → Ω → Option V} {τ : Ω → WithTop ℝ≥0}

lemma untopA_coe (t : ℝ≥0) : (t : WithTop ℝ≥0).untopA = t := rfl

omit mΩ in
lemma futureAt_apply_zero (ω : Ω) : futureAt X τ ω 0 = stoppedValue X τ ω := by
  simp [futureAt, stoppedValue]

omit mΩ in
lemma futureAt_of_eq {ω : Ω} {t : ℝ≥0} (h : τ ω = t) : futureAt X τ ω = shiftedPath X t ω := by
  ext s; simp only [futureAt, shiftedPath, h]; rfl

omit mΩ in
lemma stoppedValue_of_eq {ω : Ω} {t : ℝ≥0} (h : τ ω = t) : stoppedValue X τ ω = X t ω := by
  rw [stoppedValue, h]; rfl

/-! `RightContinuousAtInfty` — a.s., for every `t ≥ 0` with `X_t = ∞` and every vertex `y`
there is `ε > 0` with `X_s ≠ y` for all `s ∈ (t, t + ε)` — is defined in
`Theorem16Statement.lean`, where it is the `∞`-side of property (ii) and a conjunct of
`IsReflectedWalk`.  See the module docstring for why Lemma 3.10 needs it. -/

omit mΩ in
/-- Pointwise content of (ii) + right continuity at `∞` at one outcome: for every `t` and
vertex `y`, on a right neighbourhood `[t, t + ε)` the predicate `X_s = y` is constant. -/
lemma exists_Ico_iff_of_rightContinuous {ω : Ω}
    (hii : ∀ t : ℝ≥0, (∃ x : V, X t ω = some x) →
      ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω)
    (hR : ∀ t : ℝ≥0, X t ω = none →
      ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y)
    (t : ℝ≥0) (y : V) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), (X s ω = some y ↔ X t ω = some y) := by
  rcases h : X t ω with _ | y'
  · obtain ⟨ε, hε, h'⟩ := hR t h y
    refine ⟨ε, hε, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.1 with rfl | hlt
    · rw [h]
    · simp [h' s ⟨hlt, hs.2⟩]
  · obtain ⟨ε, hε, h'⟩ := hii t ⟨y', h⟩
    refine ⟨ε, hε, fun s hs => ?_⟩
    rw [h' s hs, h]

/-! ### Dyadic approximation of a stopping time (paper: `τ_k := 2⁻ᵏ⌈2ᵏ τ⌉`) -/

/-- `2⁻ᵏ ⌈2ᵏ a⌉`, the smallest element of `[a, ∞) ∩ 2⁻ᵏℕ`. -/
noncomputable def dyadicCeil (k : ℕ) (a : ℝ≥0) : ℝ≥0 := (⌈a * 2 ^ k⌉₊ : ℝ≥0) / 2 ^ k

/-- The mesh `2⁻ᵏℕ ⊆ [0, ∞)`. -/
def dyadicMesh (k : ℕ) : Set ℝ≥0 := Set.range fun n : ℕ => (n : ℝ≥0) / 2 ^ k

/-- The paper's `τ_k := 2⁻ᵏ⌈2ᵏ τ⌉`, with `τ_k = ∞` iff `τ = ∞`. -/
noncomputable def dyadicApprox (k : ℕ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  (τ ω).map (dyadicCeil k)

lemma two_pow_pos' (k : ℕ) : (0 : ℝ≥0) < 2 ^ k := pow_pos two_pos k

lemma dyadicMesh_countable (k : ℕ) : (dyadicMesh k).Countable := Set.countable_range _

lemma dyadicCeil_mem (k : ℕ) (a : ℝ≥0) : dyadicCeil k a ∈ dyadicMesh k := ⟨_, rfl⟩

lemma le_dyadicCeil (k : ℕ) (a : ℝ≥0) : a ≤ dyadicCeil k a := by
  rw [dyadicCeil, le_div_iff₀ (two_pow_pos' k)]
  exact Nat.le_ceil _

lemma dyadicCeil_lt (k : ℕ) (a : ℝ≥0) : dyadicCeil k a < a + (2 ^ k)⁻¹ := by
  rw [dyadicCeil, div_lt_iff₀ (two_pow_pos' k), add_mul, inv_mul_cancel₀ (two_pow_pos' k).ne']
  exact Nat.ceil_lt_add_one (by positivity)

lemma dyadicCeil_le_iff {k : ℕ} {a : ℝ≥0} {n : ℕ} :
    dyadicCeil k a ≤ (n : ℝ≥0) / 2 ^ k ↔ a ≤ (n : ℝ≥0) / 2 ^ k := by
  rw [dyadicCeil, div_le_div_iff_of_pos_right (two_pow_pos' k), Nat.cast_le, Nat.ceil_le,
    le_div_iff₀ (two_pow_pos' k)]

omit mΩ in
lemma dyadicApprox_top {k : ℕ} {ω : Ω} (h : τ ω = ⊤) : dyadicApprox k τ ω = ⊤ := by
  rw [dyadicApprox, h]; rfl

omit mΩ in
lemma dyadicApprox_coe {k : ℕ} {ω : Ω} {a : ℝ≥0} (h : τ ω = a) :
    dyadicApprox k τ ω = ((dyadicCeil k a : ℝ≥0) : WithTop ℝ≥0) := by
  rw [dyadicApprox, h]; rfl

omit mΩ in
lemma dyadicApprox_eq_top_iff {k : ℕ} {ω : Ω} : dyadicApprox k τ ω = ⊤ ↔ τ ω = ⊤ := by
  cases h : τ ω with
  | top => simp [dyadicApprox_top h]
  | coe a => rw [dyadicApprox_coe h]; exact iff_of_false WithTop.coe_ne_top WithTop.coe_ne_top

omit mΩ in
lemma le_dyadicApprox (k : ℕ) (ω : Ω) : τ ω ≤ dyadicApprox k τ ω := by
  cases h : τ ω with
  | top => simp [dyadicApprox_top h]
  | coe a => rw [dyadicApprox_coe h]; exact WithTop.coe_le_coe.2 (le_dyadicCeil k a)

omit mΩ in
lemma dyadicApprox_lt {k : ℕ} {ω : Ω} {a : ℝ≥0} (h : τ ω = a) :
    dyadicApprox k τ ω < ((a + (2 ^ k)⁻¹ : ℝ≥0) : WithTop ℝ≥0) := by
  rw [dyadicApprox_coe h]; exact WithTop.coe_lt_coe.2 (dyadicCeil_lt k a)

omit mΩ in
lemma dyadicApprox_le_iff {k : ℕ} {ω : Ω} {n : ℕ} :
    dyadicApprox k τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0) ↔
      τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0) := by
  cases h : τ ω with
  | top => simp [dyadicApprox_top h]
  | coe a => rw [dyadicApprox_coe h, WithTop.coe_le_coe, WithTop.coe_le_coe, dyadicCeil_le_iff]

omit mΩ in
lemma dyadicApprox_mem {k : ℕ} {ω : Ω} (h : dyadicApprox k τ ω ≠ ⊤) :
    ∃ d ∈ dyadicMesh k, dyadicApprox k τ ω = d := by
  cases h' : τ ω with
  | top => exact absurd (dyadicApprox_top h') h
  | coe a => exact ⟨dyadicCeil k a, dyadicCeil_mem k a, dyadicApprox_coe h'⟩

omit mΩ in
/-- `τ ≤ τ_k < τ + 2⁻ᵏ` on `{τ < ∞}`, in the form used for the limiting argument: for every
`ε > 0`, `τ_k ∈ [τ, τ + ε)` for all large `k`. -/
lemma eventually_dyadicApprox_mem_Ico {ω : Ω} {a : ℝ≥0} (h : τ ω = a) {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ b : ℝ≥0, dyadicApprox k τ ω = b ∧ b ∈ Set.Ico a (a + ε) := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ≥0) < 1)
  refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
  refine ⟨dyadicCeil k a, dyadicApprox_coe h, le_dyadicCeil k a, ?_⟩
  calc dyadicCeil k a < a + (2 ^ k)⁻¹ := dyadicCeil_lt k a
    _ ≤ a + (2⁻¹) ^ K := by
        gcongr
        rw [← inv_pow]
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) hk
    _ ≤ a + ε := by gcongr

/-! ### Vertex cylinders: a π-system generating the cylinder σ-algebra -/

/-- The cylinder `{f : f(i) = g(i) ∈ VG for all i ∈ I}` prescribing **vertex** values at
finitely many times. -/
def vertexCylinder (I : Finset ℝ≥0) (g : ℝ≥0 → V) : Set (Trajectory V) :=
  {f | ∀ i ∈ I, f i = some (g i)}

/-- The family of all vertex cylinders. -/
def vertexCylinders (V : Type u) : Set (Set (Trajectory V)) :=
  {B | ∃ (I : Finset ℝ≥0) (g : ℝ≥0 → V), B = vertexCylinder I g}

lemma measurableSet_vertexCylinder (I : Finset ℝ≥0) (g : ℝ≥0 → V) :
    MeasurableSet (vertexCylinder I g) := by
  have : vertexCylinder I g = ⋂ i ∈ I, (fun f : Trajectory V => f i) ⁻¹' {some (g i)} := by
    ext f; simp [vertexCylinder]
  rw [this]
  exact MeasurableSet.biInter I.countable_toSet fun i _ =>
    measurable_pi_apply i (measurableSet_option _)

lemma univ_mem_vertexCylinders (x : V) : (Set.univ : Set (Trajectory V)) ∈ vertexCylinders V :=
  ⟨∅, fun _ => x, by ext f; simp [vertexCylinder]⟩

lemma isPiSystem_vertexCylinders : IsPiSystem (vertexCylinders V) := by
  classical
  rintro _ ⟨I, g, rfl⟩ _ ⟨I', g', rfl⟩ ⟨f₀, hf₀, hf₀'⟩
  refine ⟨I ∪ I', fun i => if i ∈ I then g i else g' i, ?_⟩
  ext f
  simp only [vertexCylinder, mem_inter_iff, mem_ofPred_eq, Finset.mem_union]
  constructor
  · rintro ⟨h, h'⟩ i hi
    by_cases hiI : i ∈ I
    · simp [hiI, h i hiI]
    · simp [hiI, h' i (hi.resolve_left hiI)]
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [hi] using h i (Or.inl hi)
    · have hf := h i (Or.inr hi)
      by_cases hiI : i ∈ I
      · have e : some (g i) = some (g' i) := (hf₀ i hiI).symm.trans (hf₀' i hi)
        simpa [hiI, Option.some_inj.1 e] using hf
      · simpa [hiI] using hf

lemma generateFrom_vertexCylinders [Countable V] :
    (MeasurableSpace.pi : MeasurableSpace (Trajectory V)) =
      MeasurableSpace.generateFrom (vertexCylinders V) := by
  apply le_antisymm
  · show (⨆ i : ℝ≥0, MeasurableSpace.comap (fun f : Trajectory V => f i)
      (⊤ : MeasurableSpace (Option V))) ≤ _
    refine iSup_le fun i => MeasurableSpace.comap_le_iff_le_map.2 fun s _ => ?_
    show MeasurableSet[MeasurableSpace.generateFrom (vertexCylinders V)]
      ((fun f : Trajectory V => f i) ⁻¹' s)
    have hsingle : ∀ y : V, MeasurableSet[MeasurableSpace.generateFrom (vertexCylinders V)]
        ((fun f : Trajectory V => f i) ⁻¹' {some y}) := fun y =>
      MeasurableSpace.measurableSet_generateFrom ⟨{i}, fun _ => y, by ext f; simp [vertexCylinder]⟩
    have hs : (fun f : Trajectory V => f i) ⁻¹' s =
        ⋃ a ∈ s, (fun f : Trajectory V => f i) ⁻¹' {a} := by ext f; simp
    rw [hs]
    refine MeasurableSet.biUnion s.to_countable fun a _ => ?_
    cases a with
    | none =>
      have : (fun f : Trajectory V => f i) ⁻¹' {none} =
          (⋃ y : V, (fun f : Trajectory V => f i) ⁻¹' {some y})ᶜ := by
        ext f
        simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, not_exists]
        cases f i <;> simp
      rw [this]
      exact (MeasurableSet.iUnion hsingle).compl
    | some y => exact hsingle y
  · exact MeasurableSpace.generateFrom_le fun B ⟨I, g, hB⟩ => hB ▸ measurableSet_vertexCylinder I g

/-! ### Property (iv) on a rectangle -/

variable {P : Measure Ω} {μ : V → Measure (Trajectory V)}

/-- Property (iv) evaluated on the rectangle `S ×ˢ B`: for every `t`, every measurable set
`S` of pasts and every measurable set `B` of trajectories,
`P(F ∩ {X_t = x} ∩ {X_{·+t} ∈ B}) = P(F ∩ {X_t = x}) · μ x (B)` with `F = pastPath X t ⁻¹' S`.
This is the textbook Markov property at the deterministic time `t`. -/
lemma markov_rectangle [∀ x, SFinite (μ x)] (hX : ∀ t, Measurable (X t))
    (hM : MarkovProperty μ P X) (t : ℝ≥0)
    (x : V) {S : Set (Set.Iic t → Option V)} (hS : MeasurableSet S) {B : Set (Trajectory V)}
    (hB : MeasurableSet B) :
    P (pastPath X t ⁻¹' S ∩ {ω | X t ω = some x} ∩ shiftedPath X t ⁻¹' B) =
      P (pastPath X t ⁻¹' S ∩ {ω | X t ω = some x}) * μ x B := by
  have hpair : Measurable fun ω => (pastPath X t ω, shiftedPath X t ω) :=
    (measurable_pastPath hX t).prodMk (measurable_shiftedPath hX t)
  have h : ((P.restrict {ω | X t ω = some x}).map
      (fun ω => (pastPath X t ω, shiftedPath X t ω))) (S ×ˢ B) =
      (((P.restrict {ω | X t ω = some x}).map (pastPath X t)).prod (μ x)) (S ×ˢ B) := by
    rw [hM t x]
  rw [Measure.map_apply hpair (hS.prod hB), Measure.prod_prod,
    Measure.map_apply (measurable_pastPath hX t) hS,
    Measure.restrict_apply ((measurable_pastPath hX t) hS),
    Measure.restrict_apply (hpair (hS.prod hB))] at h
  convert h using 2
  ext ω
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_prod]
  tauto

/-! ### Step 1: the countable-valued case (paper: "if `τ` takes values in a deterministic
countable subset of `[0,∞)`, the result follows easily from Property (iv)") -/

omit mΩ in
/-- For `σ` with values in `D ∪ {∞}`, the level set `{σ = d}` is `{σ ≤ d}` minus the union of
`{σ ≤ d'}` over the smaller mesh points `d' ∈ D`. -/
lemma setOf_eq_coe_eq_diff {σ : Ω → WithTop ℝ≥0} {D : Set ℝ≥0}
    (hσD : ∀ ω, σ ω ≠ ⊤ → ∃ d ∈ D, σ ω = d) (d : ℝ≥0) :
    {ω | σ ω = d} = {ω | σ ω ≤ (d : WithTop ℝ≥0)} \
      ⋃ p : {p : D // (p.1 : ℝ≥0) < d}, {ω | σ ω ≤ ((p.1.1 : ℝ≥0) : WithTop ℝ≥0)} := by
  ext ω
  constructor
  · intro h
    have h' : σ ω = d := h
    refine ⟨h'.le, fun hmem => ?_⟩
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hmem
    have hle : σ ω ≤ ((p.1.1 : ℝ≥0) : WithTop ℝ≥0) := hp
    rw [h', WithTop.coe_le_coe] at hle
    exact absurd hle (not_le.2 p.2)
  · rintro ⟨hle, hnot⟩
    have hle' : σ ω ≤ (d : WithTop ℝ≥0) := hle
    obtain ⟨d'', hd'', h''⟩ := hσD ω (ne_top_of_le_ne_top WithTop.coe_ne_top hle')
    show σ ω = d
    rw [h''] at hle' ⊢
    rw [WithTop.coe_le_coe] at hle'
    rcases hle'.lt_or_eq with hlt | heq
    · exact absurd (Set.mem_iUnion.2 ⟨⟨⟨d'', hd''⟩, hlt⟩, h''.le⟩) hnot
    · rw [heq]

/-- **Lemma 3.10, countable-valued case.**  Let `σ` take values in a countable set
`D ⊆ [0,∞)` together with `∞`, and let the stopping-time data of `σ` and of `F` be given at
the mesh points: `{σ ≤ d}` and `F ∩ {σ ≤ d}` agree `P`-a.s. with sets of `ℱ_d = σ(X_s : s ≤ d)`
for every `d ∈ D`.  Then on `{σ < ∞, X_σ = x}` the conditional law of `{X_{s+σ}}_{s ≥ 0}`
given `F` is `μ x`:

`P(F ∩ {σ < ∞, X_σ = x} ∩ {X_{·+σ} ∈ B}) = P(F ∩ {σ < ∞, X_σ = x}) · μ x (B)`.

Proof: decompose over the atoms `{σ = d}`, `d ∈ D`, apply property (iv) at the deterministic
time `d` on each, and resum.  Only (iv) is used. -/
theorem strongMarkov_of_countable_range [Countable V] [∀ x, SFinite (μ x)]
    (hX : ∀ t, Measurable (X t))
    (hM : MarkovProperty μ P X) {σ : Ω → WithTop ℝ≥0} {D : Set ℝ≥0} (hD : D.Countable)
    (hσD : ∀ ω, σ ω ≠ ⊤ → ∃ d ∈ D, σ ω = d)
    (hσ : ∀ d ∈ D, ∃ G, MeasurableSet[pastSigma X d] G ∧
      {ω | σ ω ≤ (d : WithTop ℝ≥0)} =ᵐ[P] G)
    {F : Set Ω}
    (hF : ∀ d ∈ D, ∃ G, MeasurableSet[pastSigma X d] G ∧
      F ∩ {ω | σ ω ≤ (d : WithTop ℝ≥0)} =ᵐ[P] G)
    (x : V) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    P (F ∩ stopEvent X σ x ∩ futureAt X σ ⁻¹' B) = P (F ∩ stopEvent X σ x) * μ x B := by
  classical
  have : Countable D := hD.to_subtype
  -- the atoms `F ∩ {σ = d}` are a.s. in `ℱ_d`
  have key : ∀ d : D, ∃ G, MeasurableSet[pastSigma X d] G ∧ F ∩ {ω | σ ω = d} =ᵐ[P] G := by
    intro d
    obtain ⟨G, hG, hGe⟩ := hF d d.2
    choose G' hG' hG'e using hσ
    refine ⟨G \ ⋃ p : {p : D // (p.1 : ℝ≥0) < d}, G' p.1.1 p.1.2, ?_, ?_⟩
    · exact hG.diff (MeasurableSet.iUnion fun p => pastSigma_mono X p.2.le _ (hG' p.1.1 p.1.2))
    · rw [setOf_eq_coe_eq_diff hσD, ← Set.inter_sdiff_assoc, Set.sdiff_eq, Set.sdiff_eq]
      exact ae_eq_set_inter hGe (ae_eq_set_compl_compl.2
        (EventuallyEqSet.countable_iUnion fun p => hG'e p.1.1 p.1.2))
  -- the pieces
  set A : Set (Trajectory V) → D → Set Ω := fun C d =>
    F ∩ {ω | σ ω = d} ∩ ({ω | X d ω = some x} ∩ shiftedPath X d ⁻¹' C) with hA
  have hdecomp : ∀ C : Set (Trajectory V),
      F ∩ stopEvent X σ x ∩ futureAt X σ ⁻¹' C = ⋃ d : D, A C d := by
    intro C; ext ω
    simp only [hA, mem_inter_iff, mem_iUnion, mem_ofPred_eq, stopEvent, mem_preimage]
    constructor
    · rintro ⟨⟨hFω, hne, hval⟩, hfut⟩
      obtain ⟨d, hd, hσd⟩ := hσD ω hne
      refine ⟨⟨d, hd⟩, ⟨hFω, hσd⟩, ?_, ?_⟩
      · rwa [stoppedValue_of_eq hσd] at hval
      · rwa [futureAt_of_eq hσd] at hfut
    · rintro ⟨⟨d, hd⟩, ⟨hFω, hσd⟩, hval, hfut⟩
      exact ⟨⟨hFω, by rw [hσd]; exact WithTop.coe_ne_top, by rwa [stoppedValue_of_eq hσd]⟩,
        by rwa [futureAt_of_eq hσd]⟩
  have hnull : ∀ (C : Set (Trajectory V)), MeasurableSet C → ∀ d : D,
      NullMeasurableSet (A C d) P := by
    intro C hC d
    obtain ⟨G, hG, hGe⟩ := key d
    have hXd : MeasurableSet {ω | X d ω = some x} := hX d (measurableSet_option {some x})
    have hK : MeasurableSet ({ω | X d ω = some x} ∩ shiftedPath X d ⁻¹' C) :=
      hXd.inter (measurable_shiftedPath hX d hC)
    exact ((pastSigma_le hX d _ hG).inter hK).nullMeasurableSet.congr
      (ae_eq_set_inter hGe.symm EventuallyEq.rfl)
  have hdisj : ∀ C : Set (Trajectory V), Pairwise fun d d' => AEDisjoint P (A C d) (A C d') := by
    intro C d d' hne
    refine (Set.disjoint_left.2 fun ω h h' => hne ?_).aedisjoint
    exact Subtype.ext (WithTop.coe_injective (h.1.2.symm.trans h'.1.2))
  have hterm : ∀ (C : Set (Trajectory V)), MeasurableSet C → ∀ d : D,
      P (A C d) = P (A univ d) * μ x C := by
    intro C hC d
    obtain ⟨G, hG, hGe⟩ := key d
    obtain ⟨S, hS, rfl⟩ := measurableSet_pastSigma_iff.1 hG
    simp only [hA, preimage_univ, inter_univ]
    rw [measure_congr (ae_eq_set_inter hGe EventuallyEq.rfl),
      measure_congr (ae_eq_set_inter hGe EventuallyEq.rfl), ← Set.inter_assoc]
    exact markov_rectangle hX hM d x hS hC
  have hdu := hdecomp univ
  simp only [preimage_univ, inter_univ] at hdu
  rw [hdecomp B, hdu, measure_iUnion₀ (hdisj B) (hnull B hB),
    measure_iUnion₀ (hdisj univ) (hnull univ MeasurableSet.univ), ← ENNReal.tsum_mul_right]
  exact tsum_congr fun d => hterm B hB d


/-! ### Step 2: measurability along the dyadic approximations -/

omit mΩ in
/-- The `Option`-valued analogue of "two values agree iff they agree on every vertex test". -/
lemma option_eq_of_forall_some_iff {a b : Option V}
    (h : ∀ y : V, (a = some y ↔ b = some y)) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => exact absurd ((h y).2 rfl) (by simp)
  | some y => exact ((h y).1 rfl).symm

lemma measurableSet_eventually_atTop {p : ℕ → Ω → Prop} (hp : ∀ k, MeasurableSet {ω | p k ω}) :
    MeasurableSet {ω | ∀ᶠ k in atTop, p k ω} := by
  have : {ω | ∀ᶠ k in atTop, p k ω} = ⋃ N : ℕ, ⋂ k : ℕ, ⋂ (_ : N ≤ k), {ω | p k ω} := by
    ext ω; simp [Filter.eventually_atTop]
  rw [this]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hp k

/-- `{τ = ∞}` is measurable for measurable `τ`. -/
lemma measurableSet_eq_top (hτ : Measurable τ) : MeasurableSet {ω | τ ω = ⊤} := by
  have : {ω | τ ω = ⊤} = (⋃ n : ℕ, {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists]
    constructor
    · intro h n; rw [h]; exact fun h' => absurd h' (not_le.2 (WithTop.coe_lt_top _))
    · intro h
      cases hτω : τ ω with
      | top => rfl
      | coe a =>
        obtain ⟨n, hn⟩ := exists_nat_ge a
        exact absurd (by rw [hτω]; exact WithTop.coe_le_coe.2 hn) (h n)
  rw [this]
  exact (MeasurableSet.iUnion fun n => hτ measurableSet_Iic).compl

/-- The level sets `{τ_k = d}`, `d ∈ 2⁻ᵏℕ`, of the dyadic approximation of a measurable `τ`
are measurable. -/
lemma measurableSet_dyadicApprox_eq (hτ : Measurable τ) (k : ℕ) {d : ℝ≥0} (hd : d ∈ dyadicMesh k) :
    MeasurableSet {ω | dyadicApprox k τ ω = d} := by
  have : Countable (dyadicMesh k) := (dyadicMesh_countable k).to_subtype
  rw [setOf_eq_coe_eq_diff (fun ω h => dyadicApprox_mem h) d]
  have hle : ∀ d' ∈ dyadicMesh k,
      MeasurableSet {ω | dyadicApprox k τ ω ≤ (d' : WithTop ℝ≥0)} := by
    rintro _ ⟨n, rfl⟩
    have : {ω | dyadicApprox k τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0)} =
        {ω | τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0)} :=
      Set.ext fun ω => dyadicApprox_le_iff
    rw [this]
    exact hτ measurableSet_Iic
  exact (hle d hd).diff (MeasurableSet.iUnion fun p => hle p.1.1 p.1.2)

/-- For `σ` with values in a countable set `D ∪ {∞}` whose level sets are measurable, the
position `X_{s+σ}` is a random variable. -/
lemma measurable_eval_stopped [Countable V] (hX : ∀ t, Measurable (X t))
    {σ : Ω → WithTop ℝ≥0} {D : Set ℝ≥0} (hD : D.Countable)
    (hσD : ∀ ω, σ ω ≠ ⊤ → ∃ d ∈ D, σ ω = d)
    (hlev : ∀ d ∈ D, MeasurableSet {ω | σ ω = d}) (htop : MeasurableSet {ω | σ ω = ⊤})
    (s : ℝ≥0) : Measurable fun ω => X (s + (σ ω).untopA) ω := by
  refine measurable_to_countable' fun a => ?_
  have : (fun ω => X (s + (σ ω).untopA) ω) ⁻¹' {a} =
      ({ω | σ ω = ⊤} ∩ {ω | X (s + (⊤ : WithTop ℝ≥0).untopA) ω = a}) ∪
        ⋃ d ∈ D, {ω | σ ω = d} ∩ {ω | X (s + d) ω = a} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
      mem_iUnion, exists_prop]
    constructor
    · intro h
      by_cases hω : σ ω = ⊤
      · left; exact ⟨hω, by rw [hω] at h; exact h⟩
      · right
        obtain ⟨d, hd, hσ⟩ := hσD ω hω
        exact ⟨d, hd, hσ, by rw [hσ] at h; exact h⟩
    · rintro (⟨hω, h⟩ | ⟨d, hd, hσ, h⟩)
      · rw [hω]; exact h
      · rw [hσ]; exact h
  rw [this]
  exact (htop.inter (hX _ (measurableSet_option {a}))).union
    (MeasurableSet.biUnion hD fun d hd => (hlev d hd).inter (hX _ (measurableSet_option {a})))

/-- `X_{s+τ_k}` is a random variable for every `k` and `s` (`τ` measurable). -/
lemma measurable_futureAt_dyadicApprox [Countable V] (hX : ∀ t, Measurable (X t))
    (hτ : Measurable τ) (k : ℕ) (s : ℝ≥0) :
    Measurable fun ω => futureAt X (dyadicApprox k τ) ω s := by
  have htop : MeasurableSet {ω | dyadicApprox k τ ω = ⊤} := by
    have : {ω | dyadicApprox k τ ω = ⊤} = {ω | τ ω = ⊤} := Set.ext fun ω => dyadicApprox_eq_top_iff
    rw [this]; exact measurableSet_eq_top hτ
  exact measurable_eval_stopped hX (dyadicMesh_countable k) (fun ω h => dyadicApprox_mem h)
    (fun d hd => measurableSet_dyadicApprox_eq hτ k hd) htop s

/-! ### The right-limit trajectory along `τ_k ↓ τ` -/

open scoped Classical in
/-- The trajectory `s ↦ lim_k X_{s+τ_k}`, where the limit of a sequence in the discrete space
`VG ∪ {∞}` is the eventual vertex value if there is one and `∞` otherwise.  By right
continuity (ii)+(R) it coincides with `{X_{s+τ}}_{s ≥ 0}` a.s.; unlike the latter it is
measurable by construction. -/
noncomputable def dyadicLimitFuture (X : ℝ≥0 → Ω → Option V) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Trajectory V := fun s =>
  if h : ∃ y : V, ∀ᶠ k in atTop, futureAt X (dyadicApprox k τ) ω s = some y then some h.choose
  else none

omit mΩ in
lemma dyadicLimitFuture_eq_some_iff {ω : Ω} {s : ℝ≥0} {y : V} :
    dyadicLimitFuture X τ ω s = some y ↔
      ∀ᶠ k in atTop, futureAt X (dyadicApprox k τ) ω s = some y := by
  simp only [dyadicLimitFuture]
  split_ifs with h
  · constructor
    · intro hy
      rw [Option.some_inj] at hy
      rw [← hy]; exact h.choose_spec
    · intro hy
      obtain ⟨k, h1, h2⟩ := (h.choose_spec.and hy).exists
      rw [h1, Option.some_inj] at h2
      rw [h2]
  · exact iff_of_false (by simp) fun hy => h ⟨y, hy⟩

lemma measurable_dyadicLimitFuture [Countable V] (hX : ∀ t, Measurable (X t))
    (hτ : Measurable τ) : Measurable (dyadicLimitFuture X τ) := by
  refine measurable_pi_iff.2 fun s => measurable_to_countable' fun a => ?_
  have hsome : ∀ y : V, MeasurableSet {ω | dyadicLimitFuture X τ ω s = some y} := by
    intro y
    simp_rw [dyadicLimitFuture_eq_some_iff]
    exact measurableSet_eventually_atTop fun k =>
      measurable_futureAt_dyadicApprox hX hτ k s (measurableSet_option {some y})
  cases a with
  | none =>
    have : (fun ω => dyadicLimitFuture X τ ω s) ⁻¹' {none} =
        (⋃ y : V, {ω | dyadicLimitFuture X τ ω s = some y})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, mem_ofPred_eq]
      cases dyadicLimitFuture X τ ω s <;> simp
    rw [this]
    exact (MeasurableSet.iUnion hsome).compl
  | some y => exact hsome y

omit mΩ in
/-- Along `τ_k ↓ τ`, right continuity (ii)+(R) at one outcome gives, for every `s` and every
vertex `y`: `X_{s+τ_k} = y` for all large `k` iff `X_{s+τ} = y`.  (On `{τ = ∞}` both sides
are the same junk value.) -/
lemma eventually_futureAt_dyadicApprox_iff {ω : Ω}
    (hii : ∀ t : ℝ≥0, (∃ x : V, X t ω = some x) →
      ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω)
    (hR : ∀ t : ℝ≥0, X t ω = none →
      ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y)
    (s : ℝ≥0) (y : V) :
    ∀ᶠ k in atTop, (futureAt X (dyadicApprox k τ) ω s = some y ↔ futureAt X τ ω s = some y) := by
  cases h : τ ω with
  | top =>
    refine Eventually.of_forall fun k => ?_
    simp only [futureAt, dyadicApprox_top h, h]
  | coe a =>
    obtain ⟨ε, hε, hεs⟩ := exists_Ico_iff_of_rightContinuous hii hR (s + a) y
    filter_upwards [eventually_dyadicApprox_mem_Ico h hε] with k hk
    obtain ⟨b, hb, hb1, hb2⟩ := hk
    simp only [futureAt, hb, h]
    exact hεs (s + b) ⟨by gcongr, by rw [add_assoc]; gcongr⟩

omit mΩ in
/-- The same, with the right-limit trajectory in place of `{X_{s+τ}}`. -/
lemma eventually_futureAt_dyadicApprox_iff_limit {ω : Ω}
    (hii : ∀ t : ℝ≥0, (∃ x : V, X t ω = some x) →
      ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω)
    (hR : ∀ t : ℝ≥0, X t ω = none →
      ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y)
    (s : ℝ≥0) (y : V) :
    ∀ᶠ k in atTop,
      (futureAt X (dyadicApprox k τ) ω s = some y ↔ dyadicLimitFuture X τ ω s = some y) := by
  have h1 := eventually_futureAt_dyadicApprox_iff (τ := τ) hii hR s y
  have h2 : futureAt X τ ω s = some y ↔ dyadicLimitFuture X τ ω s = some y := by
    rw [dyadicLimitFuture_eq_some_iff]
    constructor
    · intro hB; exact h1.mono fun k hk => hk.2 hB
    · intro h'
      obtain ⟨k, hk1, hk2⟩ := (h1.and h').exists
      exact hk1.1 hk2
  exact h1.mono fun k hk => hk.trans h2

omit mΩ in
/-- At a right-continuous outcome, `{X_{s+τ}}_{s ≥ 0}` is the right-limit trajectory. -/
lemma futureAt_eq_dyadicLimitFuture {ω : Ω}
    (hii : ∀ t : ℝ≥0, (∃ x : V, X t ω = some x) →
      ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X s ω = X t ω)
    (hR : ∀ t : ℝ≥0, X t ω = none →
      ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ioo t (t + ε), X s ω ≠ some y) :
    futureAt X τ ω = dyadicLimitFuture X τ ω := by
  funext s
  refine option_eq_of_forall_some_iff fun y => ?_
  rw [dyadicLimitFuture_eq_some_iff]
  have h1 := eventually_futureAt_dyadicApprox_iff (τ := τ) hii hR s y
  constructor
  · intro hB; exact h1.mono fun k hk => hk.2 hB
  · intro h'
    obtain ⟨k, hk1, hk2⟩ := (h1.and h').exists
    exact hk1.1 hk2

/-! ### Step 3: the general case -/

/-- **Lemma 3.10, core form.**  Let `X` be a process with property (iv) (with laws `μ`),
property (ii), and right continuity at `∞`, under the finite measure `P`.  Let `τ` be a
measurable stopping time of the `P`-completion of the natural filtration and `F` a
measurable set in its stopped σ-algebra (both up to null sets).  Then for every `x ∈ VG`
and every cylinder-measurable `B`,

`P(F ∩ {τ < ∞, X_τ = x} ∩ {X_{·+τ} ∈ B}) = P(F ∩ {τ < ∞, X_τ = x}) · μ x (B)`.

Proof (the paper's): apply the countable-valued case to `τ_k = 2⁻ᵏ⌈2ᵏτ⌉`; on the event,
`X_{s+τ_k} = X_{s+τ}` for all large `k` and every `s` by right continuity, so dominated
convergence gives the identity for every vertex cylinder; these form a π-system generating
the cylinder σ-algebra. -/
theorem strongMarkov_core [Countable V] [∀ x, IsFiniteMeasure (μ x)] [IsFiniteMeasure P]
    (hX : ∀ t, Measurable (X t)) (hM : MarkovProperty μ P X)
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X)
    (hτm : Measurable τ) (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ)
    {F : Set Ω} (hFm : MeasurableSet F)
    (hF : AEMeasurableSetStopped (naturalFiltration X hX) P τ F)
    (x : V) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    P (F ∩ stopEvent X τ x ∩ futureAt X τ ⁻¹' B) = P (F ∩ stopEvent X τ x) * μ x B := by
  classical
  -- (1) the countable-valued case at each `τ_k`
  have hstep : ∀ (k : ℕ) (C : Set (Trajectory V)), MeasurableSet C →
      P (F ∩ stopEvent X (dyadicApprox k τ) x ∩ futureAt X (dyadicApprox k τ) ⁻¹' C) =
        P (F ∩ stopEvent X (dyadicApprox k τ) x) * μ x C := by
    intro k C hC
    refine strongMarkov_of_countable_range hX hM (dyadicMesh_countable k)
      (fun ω h => dyadicApprox_mem h) ?_ ?_ x hC
    · rintro _ ⟨n, rfl⟩
      obtain ⟨G, hG, hGe⟩ := hτ ((n : ℝ≥0) / 2 ^ k)
      refine ⟨G, hG, ?_⟩
      have : {ω | dyadicApprox k τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0)} =
          {ω | τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0)} :=
        Set.ext fun ω => dyadicApprox_le_iff
      rw [this]; exact hGe
    · rintro _ ⟨n, rfl⟩
      obtain ⟨G, hG, hGe⟩ := hF ((n : ℝ≥0) / 2 ^ k)
      refine ⟨G, hG, ?_⟩
      have : {ω | dyadicApprox k τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0)} =
          {ω | τ ω ≤ (((n : ℝ≥0) / 2 ^ k : ℝ≥0) : WithTop ℝ≥0)} :=
        Set.ext fun ω => dyadicApprox_le_iff
      rw [this]; exact hGe
  -- (2) the a.s. set of right-continuous outcomes
  have hgood := hii.and hR
  -- (3) measurable versions of the future and of the event
  have hfut'_m : Measurable (dyadicLimitFuture X τ) := measurable_dyadicLimitFuture hX hτm
  have hfut_ae : futureAt X τ =ᵐ[P] dyadicLimitFuture X τ := by
    filter_upwards [hgood] with ω hω
    exact futureAt_eq_dyadicLimitFuture hω.1 hω.2
  have hfut_aem : AEMeasurable (futureAt X τ) P := ⟨_, hfut'_m, hfut_ae⟩
  set E' : Set Ω := {ω | τ ω ≠ ⊤ ∧ dyadicLimitFuture X τ ω 0 = some x} with hE'
  have hE'm : MeasurableSet E' :=
    (measurableSet_eq_top hτm).compl.inter
      ((measurable_pi_apply 0).comp hfut'_m (measurableSet_option {some x}))
  have hE_ae : stopEvent X τ x =ᵐ[P] E' := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hgood] with ω hω
    simp only [stopEvent, hE', mem_ofPred_eq, ← futureAt_apply_zero,
      futureAt_eq_dyadicLimitFuture hω.1 hω.2]
  have hFE_ae : F ∩ stopEvent X τ x =ᵐ[P] F ∩ E' := ae_eq_set_inter EventuallyEq.rfl hE_ae
  have hFE_null : NullMeasurableSet (F ∩ stopEvent X τ x) P :=
    (hFm.inter hE'm).nullMeasurableSet.congr hFE_ae.symm
  -- (4) the limit of the vertex-cylinder identities
  have hAk : ∀ (k : ℕ) (I : Finset ℝ≥0) (g : ℝ≥0 → V),
      MeasurableSet (F ∩ stopEvent X (dyadicApprox k τ) x ∩
        futureAt X (dyadicApprox k τ) ⁻¹' vertexCylinder I g) := by
    intro k I g
    have h0 : MeasurableSet {ω | stoppedValue X (dyadicApprox k τ) ω = some x} := by
      simp_rw [← futureAt_apply_zero]
      exact measurable_futureAt_dyadicApprox hX hτm k 0 (measurableSet_option {some x})
    have htop : MeasurableSet {ω | dyadicApprox k τ ω = ⊤} := by
      have : {ω | dyadicApprox k τ ω = ⊤} = {ω | τ ω = ⊤} :=
        Set.ext fun ω => dyadicApprox_eq_top_iff
      rw [this]; exact measurableSet_eq_top hτm
    exact (hFm.inter (htop.compl.inter h0)).inter
      ((measurable_pi_iff.2 (measurable_futureAt_dyadicApprox hX hτm k))
        (measurableSet_vertexCylinder I g))
  have hconv : ∀ (I : Finset ℝ≥0) (g : ℝ≥0 → V),
      Tendsto (fun k => P (F ∩ stopEvent X (dyadicApprox k τ) x ∩
          futureAt X (dyadicApprox k τ) ⁻¹' vertexCylinder I g)) atTop
        (𝓝 (P (F ∩ E' ∩ dyadicLimitFuture X τ ⁻¹' vertexCylinder I g))) := by
    intro I g
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      ((hFm.inter hE'm).inter (hfut'_m (measurableSet_vertexCylinder I g))) (hAk · I g) ?_
    filter_upwards [hgood] with ω hω
    have h0 := eventually_futureAt_dyadicApprox_iff_limit (τ := τ) hω.1 hω.2 0 x
    have hI : ∀ᶠ k in atTop, ∀ i ∈ I,
        (futureAt X (dyadicApprox k τ) ω i = some (g i) ↔
          dyadicLimitFuture X τ ω i = some (g i)) :=
      (eventually_all_finset I).2 fun i _ =>
        eventually_futureAt_dyadicApprox_iff_limit (τ := τ) hω.1 hω.2 i (g i)
    filter_upwards [h0, hI] with k hk0 hkI
    simp only [mem_inter_iff, mem_preimage, stopEvent, hE', vertexCylinder, mem_ofPred_eq,
      ← futureAt_apply_zero, ne_eq, dyadicApprox_eq_top_iff, hk0]
    exact and_congr Iff.rfl (forall₂_congr hkI)
  have hcyl : ∀ (I : Finset ℝ≥0) (g : ℝ≥0 → V),
      P (F ∩ E' ∩ dyadicLimitFuture X τ ⁻¹' vertexCylinder I g) =
        P (F ∩ E') * μ x (vertexCylinder I g) := by
    intro I g
    have h1 := hconv I g
    have h2 := hconv ∅ (fun _ => x)
    have huniv : vertexCylinder (∅ : Finset ℝ≥0) (fun _ => x) = (univ : Set (Trajectory V)) := by
      ext; simp [vertexCylinder]
    simp only [huniv, preimage_univ, inter_univ] at h2
    have h3 : Tendsto (fun k => P (F ∩ stopEvent X (dyadicApprox k τ) x ∩
        futureAt X (dyadicApprox k τ) ⁻¹' vertexCylinder I g)) atTop
        (𝓝 (P (F ∩ E') * μ x (vertexCylinder I g))) := by
      have : (fun k => P (F ∩ stopEvent X (dyadicApprox k τ) x ∩
          futureAt X (dyadicApprox k τ) ⁻¹' vertexCylinder I g)) =
          fun k => P (F ∩ stopEvent X (dyadicApprox k τ) x) * μ x (vertexCylinder I g) :=
        funext fun k => hstep k _ (measurableSet_vertexCylinder I g)
      rw [this]
      exact ENNReal.Tendsto.mul_const h2 (Or.inr (measure_ne_top _ _))
    exact tendsto_nhds_unique h1 h3
  -- (5) from vertex cylinders to all measurable sets
  have hFE_eq : P (F ∩ stopEvent X τ x) = P (F ∩ E') := measure_congr hFE_ae
  have hC : ∀ C ∈ vertexCylinders V,
      (P.restrict (F ∩ stopEvent X τ x)).map (futureAt X τ) C =
        (P (F ∩ stopEvent X τ x) • μ x) C := by
    rintro _ ⟨I, g, rfl⟩
    rw [Measure.map_apply_of_aemeasurable hfut_aem.restrict (measurableSet_vertexCylinder I g),
      Measure.restrict_apply₀' hFE_null, Measure.smul_apply, smul_eq_mul, hFE_eq, ← hcyl I g,
      inter_comm]
    exact measure_congr (ae_eq_set_inter hFE_ae (hfut_ae.preimage _))
  have hν : (P.restrict (F ∩ stopEvent X τ x)).map (futureAt X τ) =
      P (F ∩ stopEvent X τ x) • μ x :=
    ext_of_generate_finite (vertexCylinders V) generateFrom_vertexCylinders
      isPiSystem_vertexCylinders hC (hC _ (univ_mem_vertexCylinders x))
  have hνB : ((P.restrict (F ∩ stopEvent X τ x)).map (futureAt X τ)) B =
      (P (F ∩ stopEvent X τ x) • μ x) B := by rw [hν]
  rwa [Measure.map_apply_of_aemeasurable hfut_aem.restrict hB, Measure.restrict_apply₀' hFE_null,
    Measure.smul_apply, smul_eq_mul, inter_comm] at hνB


/-! ### Consequences of right continuity: the future at `τ` is a random trajectory -/

/-- Under (ii)+(R), the future `{X_{s+τ}}_{s ≥ 0}` at a measurable `τ` is a.e.-measurable. -/
lemma aemeasurable_futureAt [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (hτm : Measurable τ) :
    AEMeasurable (futureAt X τ) P := by
  refine ⟨dyadicLimitFuture X τ, measurable_dyadicLimitFuture hX hτm, ?_⟩
  filter_upwards [hii.and hR] with ω hω
  exact futureAt_eq_dyadicLimitFuture hω.1 hω.2

/-- Under (ii)+(R), the event `{τ < ∞, X_τ = x}` is null-measurable. -/
lemma nullMeasurableSet_stopEvent [Countable V] (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X) (hτm : Measurable τ) (x : V) :
    NullMeasurableSet (stopEvent X τ x) P := by
  have hE'm : MeasurableSet {ω | τ ω ≠ ⊤ ∧ dyadicLimitFuture X τ ω 0 = some x} :=
    (measurableSet_eq_top hτm).compl.inter
      ((measurable_pi_apply 0).comp (measurable_dyadicLimitFuture hX hτm)
        (measurableSet_option {some x}))
  refine hE'm.nullMeasurableSet.congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hii.and hR] with ω hω
  simp only [stopEvent, mem_ofPred_eq, ← futureAt_apply_zero,
    futureAt_eq_dyadicLimitFuture hω.1 hω.2]

/-! ### Step 4: removing the measurability side conditions on `F` and `τ` -/

/-- `strongMarkov_core` for an arbitrary (not necessarily measurable) `F` in the stopped
σ-algebra up to null sets: replace `F ∩ {τ < ∞}` by its measurable version
`⋃ n, G n ∩ {τ ≤ n}`. -/
theorem strongMarkov_of_measurable [Countable V] [∀ x, IsFiniteMeasure (μ x)]
    [IsFiniteMeasure P] (hX : ∀ t, Measurable (X t)) (hM : MarkovProperty μ P X)
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X)
    (hτm : Measurable τ) (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ)
    {F : Set Ω} (hF : AEMeasurableSetStopped (naturalFiltration X hX) P τ F)
    (x : V) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    P (F ∩ stopEvent X τ x ∩ futureAt X τ ⁻¹' B) = P (F ∩ stopEvent X τ x) * μ x B := by
  choose G hG hGe using hF
  set F' : Set Ω := ⋃ n : ℕ, G n ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} with hF'
  have hF'm : MeasurableSet F' :=
    MeasurableSet.iUnion fun n => (pastSigma_le hX _ _ (hG n)).inter (hτm measurableSet_Iic)
  have hcover : F ∩ {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, F ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hFω, hne⟩
      cases h : τ ω with
      | top => exact absurd h hne
      | coe a =>
        obtain ⟨n, hn⟩ := exists_nat_ge a
        exact ⟨n, hFω, WithTop.coe_le_coe.2 hn⟩
    · rintro ⟨n, hFω, hle⟩
      exact ⟨hFω, ne_top_of_le_ne_top WithTop.coe_ne_top hle⟩
  have hF'ae : F' =ᵐ[P] F ∩ {ω | τ ω ≠ ⊤} := by
    rw [hcover]
    refine EventuallyEqSet.countable_iUnion fun n => ?_
    have h1 : G n ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[P]
        F ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} :=
      ae_eq_set_inter (hGe n).symm EventuallyEqSet.rfl
    rwa [inter_assoc, inter_self] at h1
  have hsub : ∀ S : Set Ω, S ⊆ {ω | τ ω ≠ ⊤} → F ∩ {ω | τ ω ≠ ⊤} ∩ S = F ∩ S := by
    intro S hS; ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hS h2⟩, h2⟩
  have h1 : F' ∩ stopEvent X τ x =ᵐ[P] F ∩ stopEvent X τ x := by
    have := ae_eq_set_inter hF'ae (EventuallyEqSet.rfl (s := stopEvent X τ x))
    rwa [hsub _ fun ω hω => hω.1] at this
  have hF'stop : AEMeasurableSetStopped (naturalFiltration X hX) P τ F' := by
    intro t
    refine ⟨G t, hG t, ?_⟩
    have := ae_eq_set_inter hF'ae (EventuallyEqSet.rfl (s := {ω | τ ω ≤ (t : WithTop ℝ≥0)}))
    rw [hsub {ω | τ ω ≤ (t : WithTop ℝ≥0)} fun ω hω =>
      ne_top_of_le_ne_top WithTop.coe_ne_top hω] at this
    exact this.trans (hGe t)
  rw [← measure_congr (ae_eq_set_inter h1 (EventuallyEqSet.rfl (s := futureAt X τ ⁻¹' B))),
    ← measure_congr h1]
  exact strongMarkov_core hX hM hii hR hτm hτ hF'm hF'stop x hB

/-- **Lemma 3.10 for the `P`-completion of the natural filtration**, in the generic form:
`τ` is a.e.-measurable and a stopping time up to null sets, `F` is in its stopped σ-algebra
up to null sets.  Obtained from the measurable case by replacing `τ` with an a.e.-equal
measurable function. -/
theorem strongMarkov_of_aemeasurable [Countable V] [∀ x, IsFiniteMeasure (μ x)]
    [IsFiniteMeasure P] (hX : ∀ t, Measurable (X t)) (hM : MarkovProperty μ P X)
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X)
    (hτm : AEMeasurable τ P) (hτ : IsAEStoppingTime (naturalFiltration X hX) P τ)
    {F : Set Ω} (hF : AEMeasurableSetStopped (naturalFiltration X hX) P τ F)
    (x : V) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    P (F ∩ stopEvent X τ x ∩ futureAt X τ ⁻¹' B) = P (F ∩ stopEvent X τ x) * μ x B := by
  set τ' := hτm.mk τ with hτ'
  have hτ'm : Measurable τ' := hτm.measurable_mk
  have hae : τ =ᵐ[P] τ' := hτm.ae_eq_mk
  have hle : ∀ t : ℝ≥0,
      {ω | τ' ω ≤ (t : WithTop ℝ≥0)} =ᵐ[P] {ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
    intro t
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hae] with ω hω
    simp only [hω]
  have hτ'st : IsAEStoppingTime (naturalFiltration X hX) P τ' := by
    intro t
    obtain ⟨G, hG, hGe⟩ := hτ t
    exact ⟨G, hG, (hle t).trans hGe⟩
  have hF' : AEMeasurableSetStopped (naturalFiltration X hX) P τ' F := by
    intro t
    obtain ⟨G, hG, hGe⟩ := hF t
    exact ⟨G, hG, (ae_eq_set_inter EventuallyEqSet.rfl (hle t)).trans hGe⟩
  have hstop : stopEvent X τ' x =ᵐ[P] stopEvent X τ x := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hae] with ω hω
    simp only [stopEvent, stoppedValue, mem_ofPred_eq, hω]
  have hfut : futureAt X τ' =ᵐ[P] futureAt X τ := by
    filter_upwards [hae] with ω hω
    funext s; simp only [futureAt, hω]
  have h1 : F ∩ stopEvent X τ' x =ᵐ[P] F ∩ stopEvent X τ x :=
    ae_eq_set_inter EventuallyEqSet.rfl hstop
  have h2 : F ∩ stopEvent X τ' x ∩ futureAt X τ' ⁻¹' B =ᵐ[P]
      F ∩ stopEvent X τ x ∩ futureAt X τ ⁻¹' B :=
    ae_eq_set_inter h1 (hfut.preimage B)
  rw [← measure_congr h2, ← measure_congr h1]
  exact strongMarkov_of_measurable hX hM hii hR hτ'm hτ'st hF' x hB

end Theorem16

/-! ## Lemma 3.10 for a process satisfying the properties of Theorem 1.6 -/

namespace ProcessFamily

variable {V : Type*} (𝓧 : ProcessFamily V)

/-- The laws `P_x` of `{X_s}_{s ≥ 0}` are probability measures. -/
instance (x : V) : IsProbabilityMeasure (𝓧.law x) := by
  unfold ProcessFamily.law; infer_instance

/-- The natural filtration `σ(X_s : s ≤ t)` of the process of the family. -/
noncomputable def naturalFiltration : Filtration ℝ≥0 𝓧.mΩ :=
  Theorem16.naturalFiltration 𝓧.X 𝓧.measurable_X

end ProcessFamily

namespace Theorem16

variable {V : Type*} {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}

/-- **Lemma 3.10 (Gwynne–Sung, p. 25), strong Markov property.**  Let `𝓧` satisfy the
properties of Theorem 1.6 (`IsReflectedWalk`); `hR` is right continuity at `∞` under `P_z`,
the `∞`-side of (ii), which `IsReflectedWalk` contains (`(h z).2.2.2.1`) and which is kept
as an explicit argument (see the module docstring).  Let `τ` be a stopping
time for `{X_t}_{t ≥ 0}` (for the natural filtration) and `x ∈ VG`.  Then on the event
`{τ < ∞, X_τ = x}` the `P_z`-conditional law of `{X_{s+τ}}_{s ≥ 0}` given `{X_s}_{s ≤ τ}` is
the `P_x`-law of `{X_s}_{s ≥ 0}`: for every `F ∈ 𝓕_τ` and every measurable set `B` of
trajectories,

`P_z (F ∩ {τ < ∞, X_τ = x} ∩ {X_{·+τ} ∈ B}) = P_z (F ∩ {τ < ∞, X_τ = x}) · P_x (B)`. -/
theorem strongMarkov [Countable V] (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : RightContinuousAtInfty (𝓧.P z) 𝓧.X)
    {τ : 𝓧.Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓧.naturalFiltration τ) (x : V)
    {F : Set 𝓧.Ω} (hF : MeasurableSet[hτ.measurableSpace] F)
    {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    𝓧.P z (F ∩ stopEvent 𝓧.X τ x ∩ futureAt 𝓧.X τ ⁻¹' B) =
      𝓧.P z (F ∩ stopEvent 𝓧.X τ x) * 𝓧.law x B :=
  strongMarkov_core 𝓧.measurable_X (h z).2.2.2.2.2.1 (h z).2.2.1 hR hτ.measurable'
    (isAEStoppingTime_of_isStoppingTime hτ _) (hτ.measurableSpace_le _ hF)
    (aemeasurableSetStopped_of_measurableSet hτ hF _) x hB

/-- **Lemma 3.10 for the usual completion.**  The same conclusion for `τ` an a.e.-measurable
stopping time of the `P_z`-completion of the natural filtration and `F` in its stopped
σ-algebra (both up to `P_z`-null sets).  This is the form applicable to the hitting times of
Section 3.4, which are stopping times only up to null sets. -/
theorem strongMarkov_completed [Countable V] (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : RightContinuousAtInfty (𝓧.P z) 𝓧.X)
    {τ : 𝓧.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (𝓧.P z))
    (hτ : IsAEStoppingTime 𝓧.naturalFiltration (𝓧.P z) τ) (x : V)
    {F : Set 𝓧.Ω} (hF : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P z) τ F)
    {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    𝓧.P z (F ∩ stopEvent 𝓧.X τ x ∩ futureAt 𝓧.X τ ⁻¹' B) =
      𝓧.P z (F ∩ stopEvent 𝓧.X τ x) * 𝓧.law x B :=
  strongMarkov_of_aemeasurable 𝓧.measurable_X (h z).2.2.2.2.2.1 (h z).2.2.1 hR hτm hτ hF x hB

/-! ### The joint-law form -/

/-- `Ω` carrying the stopped σ-algebra `𝓕_τ`: the "past up to `τ`" as a measurable space.
It plays for a stopping time the role that `Set.Iic t → VG ∪ {∞}` plays for a deterministic
time in `MarkovProperty`. -/
def StoppedPast {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (_hτ : IsStoppingTime ℱ τ) : Type u := Ω

instance {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) : MeasurableSpace (StoppedPast hτ) := hτ.measurableSpace

/-- The past `{X_s}_{s ≤ τ}` of the outcome `ω`: the identity `Ω → (Ω, 𝓕_τ)`. -/
def toStoppedPast {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (ω : Ω) : StoppedPast hτ := ω

lemma measurable_toStoppedPast {Ω : Type u} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) : Measurable (toStoppedPast hτ) :=
  fun _ hs => hτ.measurableSpace_le _ hs

/-- **Lemma 3.10, joint-law form**, in the convention of `MarkovProperty`: under `P_z`
restricted to `{τ < ∞, X_τ = x}`, the pair `({X_s}_{s ≤ τ}, {X_{s+τ}}_{s ≥ 0})` has the
product law `(law of the past) ⊗ P_x`, the past being `Ω` with the stopped σ-algebra
`𝓕_τ`.  Equivalent to `strongMarkov` by evaluating on rectangles. -/
theorem strongMarkov_joint [Countable V] (h : IsReflectedWalk G w hmin 𝓧) (z : V)
    (hR : RightContinuousAtInfty (𝓧.P z) 𝓧.X)
    {τ : 𝓧.Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓧.naturalFiltration τ) (x : V) :
    ((𝓧.P z).restrict (stopEvent 𝓧.X τ x)).map
        (fun ω => (toStoppedPast hτ ω, futureAt 𝓧.X τ ω)) =
      (((𝓧.P z).restrict (stopEvent 𝓧.X τ x)).map (toStoppedPast hτ)).prod (𝓧.law x) := by
  have hE : NullMeasurableSet (stopEvent 𝓧.X τ x) (𝓧.P z) :=
    nullMeasurableSet_stopEvent 𝓧.measurable_X (h z).2.2.1 hR hτ.measurable' x
  have hfut : AEMeasurable (futureAt 𝓧.X τ) ((𝓧.P z).restrict (stopEvent 𝓧.X τ x)) :=
    (aemeasurable_futureAt 𝓧.measurable_X (h z).2.2.1 hR hτ.measurable').restrict
  have hpair := (measurable_toStoppedPast hτ).aemeasurable.prodMk hfut
  refine (Measure.prod_eq (μ := ((𝓧.P z).restrict (stopEvent 𝓧.X τ x)).map (toStoppedPast hτ))
    (ν := 𝓧.law x) fun s t hs ht => ?_).symm
  rw [Measure.map_apply_of_aemeasurable hpair (hs.prod ht),
    Measure.map_apply (measurable_toStoppedPast hτ) hs, Measure.restrict_apply₀' hE,
    Measure.restrict_apply₀' hE]
  have hset : (fun ω => (toStoppedPast hτ ω, futureAt 𝓧.X τ ω)) ⁻¹' (s ×ˢ t) ∩
      stopEvent 𝓧.X τ x =
      toStoppedPast hτ ⁻¹' s ∩ stopEvent 𝓧.X τ x ∩ futureAt 𝓧.X τ ⁻¹' t := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    tauto
  rw [hset]
  exact strongMarkov h z hR hτ x hs ht

end Theorem16
end ReflectedWalk
