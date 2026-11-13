/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.BracketTimeAverage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalNondegeneracy
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainStatement
import LatticeProb.Bonanno.ReflectedGMS.Forms.PredictableCompletionModification
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Analysis.Normed.Group.InfiniteSum
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ConditionalTemporalAveraging

/-!
# The bracket law of large numbers as a directional time average

`ReflectedGMS/Limit/ActualArrayBracketLimit.lean` reduces `p:lem:bracketlimit` for the
actual array of `Φ(Y)` to the single open hypothesis

```
hLLN : ∀ᵐ ω ∂P, ∀ i j : Fin 2,
  Tendsto (fun T : ℝ => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω / T) atTop
    (𝓝 (Sigma i j))
```

which — by `MartingaleLimit.tendsto_ordinaryEdgeBracket_div_iff` — *is* the Birkhoff time
average `T⁻¹ ∫₀ᵀ Γ(Y_s)_{ij} ds → Σ_{ij}`.  This module builds the bridge from the
temporal-ergodic front to `hLLN` in two steps, both of which are steps of the manuscript's
own proof.

## 1. Polarization (tex:1574, "polarize to obtain the cross terms")

* the entries `Γ_{ij}` are **not** of one sign, so the transfer step of the manuscript's
  temporal ergodic theorem `p:prop:timeergodic` (tex:1553-1562), which is carried out for a
  **nonnegative** functional, does not apply to them directly;
* the directional densities `s ↦ ξᵀ Γ(Y_s) ξ` *are* nonnegative at every state
  (`MartingaleLimit.stateBracketDensity_quadraticForm_nonneg`, reflection times included),
  and the transfer step applies to each of them;
* three directions suffice: `(1,0)`, `(0,1)` and `(1,1)`.

`tendsto_ordinaryEdgeBracket_div_of_directional` and its almost-sure form
`bracketLLN_of_directional` are this reduction, and
`canonicalBracket_bracket_limit_of_directional` is
`MartingaleLimit.canonicalBracket_bracket_limit` with `hLLN` discharged in favour of the
three directional inputs.

## 2. From block averages to the Cesàro average (tex:1553-1562)

The checked temporal corpus
(`ReflectedGMS.ConditionalTemporalAveraging.tendsto_setAverageReal_chain_ae`) converges
**block averages** `|J|⁻¹ ∫_J F(θ_t Ω) dt` along the dyadic chain, not the interval
averages `T⁻¹ ∫₀ᵀ`.  The manuscript closes that gap by a direct argument: an origin dyadic
block `J ⊇ [0,T]` with `|J| ≤ (1+δ)T` sandwiches the interval average between multiples of
the block average.  `setAvg` is exactly the block average
(`setAverageReal_eq_setAvg`), `directionalAverage_eq_setAvg` identifies the directional
time average with the block average over `(0,T]`, and

* `intervalAverage_le_ratio_mul_setAvg` is the pointwise sandwich;
* `eventually_intervalAverage_le` is the manuscript's upper bound, for a general
  nonnegative density and with no boundedness assumption;
* `eventually_le_intervalAverage` is the matching lower bound for a *bounded* nonnegative
  density, and `eventually_le_intervalAverage_mono` is the comparison by which the
  manuscript transports it from `f ⊓ K` to `f` (truncation, tex:1561);
* `tendsto_intervalAverage` squeezes the two bounds into the Cesàro limit;
* `tendsto_directionalAverage_of_bounds` is the same for `directionalAverage`, i.e. for
  exactly the three inputs of step 1.

## What is *not* proved here

The temporal ergodic theorem itself.  The single named atomic input left open is the
**block data** `hblk`: for every `δ > 0` and all large `T`, an origin dyadic block `J`
containing `(0,T]` of length at most `(1+δ)T` whose block average is within `δ` of the
limit.  In the manuscript this comes from the complete-chain convergence
`p:lem:timeconverge` — which is checked, as
`ConditionalTemporalAveraging.tendsto_setAverageReal_chain_ae` — together with the
strictly positive grid probability `p:eq:gridprob` and the identification of the limit as
`𝔼[Γ]`, i.e. `p:lem:regeninvariant` plus environment ergodicity.  None of that is done
here.

Nothing in this file certifies `p:prop:timeergodic`, `p:thm:areaclt` or either main
theorem; no ergodicity, no triviality of a tail σ-field and no time-shift invariance of any
law is assumed or asserted.
-/

-- Merged from `ReflectedGMS/Limit/ActualArrayBracketLimit.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ActualArrayBracketLimit

/-!
# `p:lem:bracketlimit` for the actual quenched array of `Φ(Y)`

This module states and proves, for the **actual** ordinary-edge bracket
`MartingaleIngredients.ordinaryEdgeBracket cells Φ X i j` of the manuscript's own
harmonic coordinate `Φ` along the reflected path `X`, the structural clauses of manuscript
Lemma `p:lem:bracketlimit` (`tex:1564`) that do not require the temporal ergodic theorem,
and it reduces the remaining clauses to a short list of named atomic inputs.

The distinction with `ReflectedGMS/Forms/ActualHarmonicBracketIdentification.lean` matters
and is the reason this module exists.  That module identifies the predictable covariation
of the **Fukushima martingale limits** `fullEnergyMartingaleLimit` with
`ordinaryEdgeBracket`; the coordinate-path identification
`fullEnergyMartingaleLimit … = Φ(Y_t) - Φ(Y_0)` was its residual #1, and until that
identification exists nothing there is literally a statement about `Φ(Y)`.  Everything
proved here is stated **directly** about `ordinaryEdgeBracket cells Φ X i j`, which is the
object that `MartingaleIngredients.HasOrdinaryEdgeBracket cells Φ P F X M` names as the
predictable bracket of the actual plane-valued martingale `M`, namely the regular spatial
extension of `Φ` along the area path in `InvarianceMainStatement.FixedStartConclusions`.
So residual #1 is *bypassed*, not assumed: no Fukushima object occurs in any statement
below, and `bracket_limit_of_hasOrdinaryEdgeBracket` consumes the actual `M` directly.

## What is proved unconditionally

* `tendstoUniformlyOn_Icc_zero_of_eventually_monotoneOn` — a Pólya-type theorem: a family
  of functions that is eventually monotone in the *variable* and converges pointwise to a
  continuous limit converges uniformly on `[0, b]`.  This is the manuscript's
  "monotonicity and a finite mesh in `t`".  Mathlib has no such statement: its
  `Mathlib/Topology/UniformSpace/Dini.lean` assumes monotonicity in the *index*, which is a
  different hypothesis and does not apply to a rescaled bracket family.
* `tendstoUniformlyOn_diffusiveScaling_of_monotoneOn` — the diffusive rescaling: for a
  monotone `A` with `A 0 = 0` and `A T / T → σ`, the parabolically rescaled family
  `t ↦ ε² A (t / ε²)` converges to `t ↦ t σ` uniformly on every `[0, b]` as `ε ↓ 0`.
  Applied to a bracket this is exactly the passage from `p:eq:bracketLLN` to the
  manuscript's "brackets of `M^ε` converge to `tΣ` uniformly on compact time intervals".
* `stateBracketDensity_quadraticForm_nonneg` — the manuscript's `Γ` is pointwise positive
  semidefinite on the compactified state type, with the `1_{Y_r ∈ V}` convention (`0` at
  every collapsed end state) included.  The vertex-level statement underneath it is
  **reused**, not reproved: it is
  `DirectionalNondegeneracy.quadraticForm_bracketDensity_nonneg`.
* `monotoneOn_directional_ordinaryEdgeBracket` — consequently every directional form
  `t ↦ ξᵀ ⟨M⟩_t ξ` of the actual bracket is nondecreasing.  Off-diagonal *entries* are not
  monotone; this is precisely why the manuscript polarizes.
* `array_bracket_limit` — the abstract two-dimensional statement: symmetry and positive
  semidefiniteness of `Σ`, and the entrywise locally uniform diffusive limit, from the
  entrywise law of large numbers plus directional monotonicity.
* `quenched_ordinaryEdgeBracket_bracket_limit` and
  `bracket_limit_of_hasOrdinaryEdgeBracket` — the same for the actual quenched array.
* `symmetricPositiveDefinite_of_quadraticForm_ne_zero` — `Σ` is symmetric **positive
  definite** once the single atomic nondegeneracy input `hnull` is supplied.
* `canonicalBracket_bracket_limit` — the same at the **canonical shape of the main
  theorem**: the decoded environment `Code.decode e`, the manuscript coordinate `Φ.at e`,
  the exponential area-clock path `AreaClocks.exponentialAreaPath (decode e) D`, the
  completed filtration `InvarianceMainStatement.areaFiltration e D P`, and the bracket
  predicate `InvarianceMainStatement.CanonicalBracket e D Φ P M` that is verbatim the
  `hbracket` input of `InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`.
  At this shape the environment geometry is **not** an input: it is `Code.decode_geometry`,
  which is unconditional.  `hLLN` is the only hypothesis left.
* `eq_inl_of_collapse_eq_some`, `spatialExtension_eq_of_collapse` and
  `phi_bracket_limit_of_canonicalBracket` — the statement **for `Φ(Y)` itself**.  The two
  pathwise clauses of `InvarianceAssembly.PathwiseClockClauses` that relate the lifted path
  to the area path and `M` to `Φ` (`collapse (Xexp t ω) = Y t ω` and
  `RegularSpatialExtension (decode e) (Φ.at e) (Xexp · ω) (M · ω)`) give
  `M t ω = Φ.at e v` at every time with `Y t ω = some v`; the conclusion therefore asserts,
  on one and the same almost-sure event, that the actual martingale *is* `Φ(Y)` at every
  ordinary time and that its rescaled brackets converge to `t Σ` locally uniformly.
* `tendsto_ordinaryEdgeBracket_div_iff` — the open input `hLLN` written in the
  manuscript's own form: the Birkhoff time average `T⁻¹ ∫₀ᵀ Γ(Y_s) ds` of the bracket
  density along the path.
* `canonicalBracket_of_parts` — the producer side, recorded here because it is what makes
  the hypothesis `hM` of the two theorems above reachable: `CanonicalBracket` from its
  three clauses with the **predictability clause discharged**, from
  `PredictableCompletionModification.isStronglyPredictable_ordinaryEdgeBracket_exponentialAreaPath`
  (checked, and carrying neither a joint-measurability nor a filtration-domination side
  hypothesis).  What is left to the caller is only the local-square-integrable martingale
  property, the pathwise càdlàg/integrability clause, the pathwise
  `A_0 = 0` / continuity / bounded-variation clause, and the compensated local-martingale
  clause — plus the manuscript's own data (reflected walk for the area clock, connected
  graph, positive summable cell areas, finite-energy coordinates).

## THIS IS AN HONESTLY CONDITIONAL RESULT

Every theorem below whose name mentions a bracket limit carries its open inputs as
**explicit named hypotheses**.  Nothing here certifies those inputs, and nothing here
certifies `p:thm:areaclt`, the `hlimit` input of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`, or either main
theorem.  The named open inputs are:

1. `hLLN` — `p:eq:bracketLLN`: `T⁻¹ ⟨M^i, M^j⟩_T → Σ_{ij}` quenched almost surely.  The
   manuscript obtains it from `p:prop:timeergodic` applied to each entry of `Γ` together
   with `p:thm:martingale`.  That is the temporal-homogenization front and is owned
   elsewhere.
2. `hint` — interval integrability of each bracket density along the path.  This is
   *verbatim* the second clause of `MartingaleIngredients.HasOrdinaryEdgeBracket`, so any
   producer of that predicate supplies it; `bracket_limit_of_hasOrdinaryEdgeBracket`
   consumes it in that form rather than as a separate assumption, so it is an open input
   of `quenched_ordinaryEdgeBracket_bracket_limit` only.
3. `hnull` — no nonzero deterministic null vector for `Σ`.  This is exactly the content of
   the manuscript's positive-definiteness paragraph (zero-specific-energy detection in
   `s:lem:localcontrol`, connectedness, and the corrector bound).  It is *not* proved here,
   and it is an open input of `symmetricPositiveDefinite_of_quadraticForm_ne_zero` only.

`hcells : Geometry cells` is **not** an open input: it is the environment's own geometry,
a hypothesis carried by the main theorem.  An earlier draft of this module instead assumed
summability of the squared-increment rows of `Φ`; that assumption has been discharged from
`Geometry` via the reused `DirectionalNondegeneracy` lemma and is gone.

So the only genuinely open mathematical input of
`bracket_limit_of_hasOrdinaryEdgeBracket`, the theorem a consumer would use, is `hLLN`.

Nothing in this file assumes tightness, a Lindeberg condition, a Brownian identification,
the localizer/exit producer, or the corrector/interpolation transfer of `tex:1648`–`1652`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.MartingaleLimit

open ReflectedGMS.MartingaleIngredients

/-! ### One stability property of uniform convergence

Mathlib already supplies the difference rule as `TendstoUniformlyOn.fun_sub` (the
eta-expanded `to_additive` form of `TendstoUniformlyOn.div`), so only the scalar multiple
is recorded here, and it is obtained from mathlib's
`UniformContinuous.comp_tendstoUniformlyOn` rather than reproved by hand. -/

/-! ### A Pólya-type uniform convergence theorem -/

/-! ### The diffusive rescaling of a monotone additive functional -/

/-! ### Pointwise structure of the ordinary-edge density -/

/-- The manuscript's `Γ` is a symmetric matrix at every state, with the `1_{Y_r ∈ V}`
convention at a collapsed end state.

(For the vertex-level statement `bracketDensity F Φ v i j = bracketDensity F Φ v j i`
itself, `ReflectedGMS/InvarianceAssembly.lean` already carries a copy as
`InvarianceAssembly.bracketDensity_symm`; that module sits far above this one in
the import graph, so it cannot be reused here.) -/
theorem stateBracketDensity_symm {V : Type*} (cells : IndexedCells V) (Φ : V → Plane)
    (q : Option V) (i j : Fin 2) :
    stateBracketDensity cells Φ q i j = stateBracketDensity cells Φ q j i := by
  cases q with
  | none => simp
  | some v =>
      simp only [stateBracketDensity_some, StatementIngredients.bracketDensity]
      exact congrArg _ (tsum_congr fun w => by ring)

/-! The vertex-level positive semidefiniteness of `Γ` is **not** reproved here:
`ReflectedGMS/Limit/DirectionalNondegeneracy.lean` already carries it as
`DirectionalNondegeneracy.quadraticForm_bracketDensity_nonneg`, and from the strictly
better hypothesis `Geometry cells` (finite degree makes each conductance row finitely
supported) rather than from an assumed summability of the squared-increment rows.  Reusing
it removes that summability from the open-input list of this module entirely. -/

/-- The same on the compactified state type: at a collapsed end state the manuscript's
`1_{Y_r ∈ V}` factor makes the density `0`, so the quadratic form is nonnegative at every
state, reflection times included. -/
theorem stateBracketDensity_quadraticForm_nonneg {V : Type*} [Countable V]
    (cells : IndexedCells V) (hcells : Geometry cells) (Φ : V → Plane)
    (q : Option V) (ξ : Fin 2 → ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ξ i * stateBracketDensity cells Φ q i j * ξ j := by
  cases q with
  | none => simp
  | some v =>
      simpa using
        DirectionalNondegeneracy.quadraticForm_bracketDensity_nonneg cells hcells Φ v ξ

/-! ### The actual bracket in real time -/

/-- The actual ordinary-edge bracket read at a nonnegative real time. -/
theorem ordinaryEdgeBracket_toNNReal_eq {Ω V : Type*} (cells : IndexedCells V)
    (Φ : V → Plane) (X : ℝ≥0 → Ω → Option V) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) (i j : Fin 2) :
    ordinaryEdgeBracket cells Φ X i j (Real.toNNReal t) ω =
      ∫ s in (0 : ℝ)..t, stateBracketDensity cells Φ (X (Real.toNNReal s) ω) i j := by
  simp only [ordinaryEdgeBracket, Real.coe_toNNReal t ht]

/-! ### The abstract two-dimensional bracket limit -/

/-! ### `p:lem:bracketlimit` for the actual quenched array -/

/-! ### The open input in the manuscript's own time-average form -/

/-! ### `p:lem:bracketlimit` at the canonical shape, and for `Φ(Y)` itself

Everything above is stated for an abstract `(cells, Φ, X, P, F, M)`.  This section
specialises it to the **actual** objects of `ReflectedGMS.InvarianceMainStatement`, so that
the result composes directly with the `hbracket` input of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` and with the pathwise
clauses of `InvarianceAssembly.PathwiseClockClauses`.  Nothing here is proved about `hLLN`;
it remains the single open input, and none of these theorems certifies `p:thm:areaclt` or
either main theorem. -/

open ReflectedWalk ReflectedGMS.PredictableCompletionModification

/-! ### Making the hypothesis `hM` reachable: the predictability clause is free -/

end ReflectedGMS.MartingaleLimit

end Merged_ActualArrayBracketLimit

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.BracketTimeAverage

open ReflectedGMS.MartingaleIngredients ReflectedGMS.MartingaleLimit

/-! ### Directions and the two-dimensional polarization identity -/

/-- The quadratic form of a two-by-two real matrix, in the shape already used by
`ReflectedGMS.MartingaleLimit.array_bracket_limit` and
`MartingaleLimit.stateBracketDensity_quadraticForm_nonneg`. -/
def dirForm (M : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ξ i * M i j * ξ j

/-- The direction `(a, b)` of the plane. -/
def dirVec (a b : ℝ) : Fin 2 → ℝ := fun k => if k = 0 then a else b

@[simp] theorem dirVec_zero (a b : ℝ) : dirVec a b 0 = a := if_pos rfl

@[simp] theorem dirVec_one (a b : ℝ) : dirVec a b 1 = b :=
  if_neg (by decide : ¬((1 : Fin 2) = 0))

/-- The quadratic form in an explicit direction. -/
theorem dirForm_dirVec (M : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) :
    dirForm M (dirVec a b) =
      a * a * M 0 0 + a * b * M 0 1 + b * a * M 1 0 + b * b * M 1 1 := by
  simp only [dirForm, Fin.sum_univ_two, dirVec_zero, dirVec_one]
  ring

theorem dirForm_dirVec_one_zero (M : Matrix (Fin 2) (Fin 2) ℝ) :
    dirForm M (dirVec 1 0) = M 0 0 := by
  rw [dirForm_dirVec]; ring

theorem dirForm_dirVec_zero_one (M : Matrix (Fin 2) (Fin 2) ℝ) :
    dirForm M (dirVec 0 1) = M 1 1 := by
  rw [dirForm_dirVec]; ring

/-- **The polarization identity in two dimensions.**  For a symmetric matrix the
off-diagonal entry is recovered from the three directional forms `(1,1)`, `(1,0)` and
`(0,1)`, each of which is nonnegative when the matrix is positive semidefinite.  This is
the manuscript's "polarize to obtain the cross terms". -/
theorem entry_eq_dirForm (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M 1 0 = M 0 1) :
    M 0 1 =
      (dirForm M (dirVec 1 1) - dirForm M (dirVec 1 0) - dirForm M (dirVec 0 1)) / 2 := by
  rw [dirForm_dirVec, dirForm_dirVec, dirForm_dirVec, hM]
  ring

/-- The quadratic form written as one sum over the index pairs. -/
theorem dirForm_eq_prodSum (M : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℝ) :
    dirForm M ξ = ∑ p : Fin 2 × Fin 2, ξ p.1 * M p.1 p.2 * ξ p.2 := by
  simp only [dirForm, Fintype.sum_prod_type, Fin.sum_univ_two]

/-! ### The directional time average of the manuscript's `Γ` -/

/-- **The manuscript's `T⁻¹ ∫₀ᵀ ξᵀΓ(Y_s)ξ ds`.**

By `MartingaleLimit.stateBracketDensity_quadraticForm_nonneg` the integrand is
nonnegative at every state, reflection times included; this is precisely the situation in
which the transfer step of `p:prop:timeergodic` (tex:1553-1562) operates. -/
noncomputable def directionalAverage {Ω V : Type*} (cells : IndexedCells V) (Φ : V → Plane)
    (X : ℝ≥0 → Ω → Option V) (ω : Ω) (ξ : Fin 2 → ℝ) (T : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..T, dirForm (stateBracketDensity cells Φ (X (Real.toNNReal s) ω)) ξ) / T

/-- **The directional form of the bracket is the time integral of the directional form of
the density.**

The only input is the interval integrability of the entries along the path, which is the
second clause of `MartingaleIngredients.HasOrdinaryEdgeBracket`. -/
theorem dirForm_ordinaryEdgeBracket {Ω V : Type*} (cells : IndexedCells V) (Φ : V → Plane)
    (X : ℝ≥0 → Ω → Option V) (ω : Ω) (ξ : Fin 2 → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hint : ∀ i j : Fin 2, IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X (Real.toNNReal s) ω) i j) volume 0 T) :
    dirForm (fun i j => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω) ξ =
      ∫ s in (0 : ℝ)..T,
        dirForm (stateBracketDensity cells Φ (X (Real.toNNReal s) ω)) ξ := by
  have hE : ∀ i j : Fin 2, ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω =
      ∫ s in (0 : ℝ)..T, stateBracketDensity cells Φ (X (Real.toNNReal s) ω) i j :=
    fun i j => ordinaryEdgeBracket_toNNReal_eq cells Φ X hT ω i j
  have hmul : ∀ p : Fin 2 × Fin 2,
      (∫ s in (0 : ℝ)..T,
        ξ p.1 * stateBracketDensity cells Φ (X (Real.toNNReal s) ω) p.1 p.2 * ξ p.2) =
      ξ p.1 *
        (∫ s in (0 : ℝ)..T, stateBracketDensity cells Φ (X (Real.toNNReal s) ω) p.1 p.2) *
        ξ p.2 := by
    intro p
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  -- `simp` will not rewrite `dirForm` applied to a lambda, so the left-hand occurrence is
  -- expanded by an explicitly instantiated `rw`.
  rw [dirForm_eq_prodSum
    (fun i j => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω) ξ]
  simp only [dirForm_eq_prodSum, hE]
  rw [intervalIntegral.integral_finsetSum
    fun p _ => ((hint p.1 p.2).const_mul (ξ p.1)).mul_const (ξ p.2)]
  simp only [hmul]

/-- **The actual bracket array is symmetric at every time.** -/
theorem ordinaryEdgeBracket_symm {Ω V : Type*} (cells : IndexedCells V) (Φ : V → Plane)
    (X : ℝ≥0 → Ω → Option V) (i j : Fin 2) (t : ℝ≥0) (ω : Ω) :
    ordinaryEdgeBracket cells Φ X i j t ω = ordinaryEdgeBracket cells Φ X j i t ω := by
  simp only [ordinaryEdgeBracket]
  exact intervalIntegral.integral_congr
    (fun s _ => stateBracketDensity_symm cells Φ (X (Real.toNNReal s) ω) i j)

/-- The directional time average expanded in the entries of the bracket array. -/
theorem directionalAverage_eq {Ω V : Type*} (cells : IndexedCells V) (Φ : V → Plane)
    (X : ℝ≥0 → Ω → Option V) (ω : Ω) (a b : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hint : ∀ i j : Fin 2, IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X (Real.toNNReal s) ω) i j) volume 0 T) :
    directionalAverage cells Φ X ω (dirVec a b) T =
      (a * a * ordinaryEdgeBracket cells Φ X 0 0 (Real.toNNReal T) ω +
        a * b * ordinaryEdgeBracket cells Φ X 0 1 (Real.toNNReal T) ω +
        b * a * ordinaryEdgeBracket cells Φ X 1 0 (Real.toNNReal T) ω +
        b * b * ordinaryEdgeBracket cells Φ X 1 1 (Real.toNNReal T) ω) / T := by
  have h1 : dirForm (fun i j => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω)
      (dirVec a b) =
      ∫ s in (0 : ℝ)..T,
        dirForm (stateBracketDensity cells Φ (X (Real.toNNReal s) ω)) (dirVec a b) :=
    dirForm_ordinaryEdgeBracket cells Φ X ω (dirVec a b) hT hint
  have h2 : dirForm (fun i j => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω)
      (dirVec a b) =
      a * a * ordinaryEdgeBracket cells Φ X 0 0 (Real.toNNReal T) ω +
        a * b * ordinaryEdgeBracket cells Φ X 0 1 (Real.toNNReal T) ω +
        b * a * ordinaryEdgeBracket cells Φ X 1 0 (Real.toNNReal T) ω +
        b * b * ordinaryEdgeBracket cells Φ X 1 1 (Real.toNNReal T) ω :=
    dirForm_dirVec _ a b
  show (∫ s in (0 : ℝ)..T,
      dirForm (stateBracketDensity cells Φ (X (Real.toNNReal s) ω)) (dirVec a b)) / T = _
  rw [← h1, h2]

/-! ### The polarization reduction of `hLLN` -/

/-- **`hLLN` from three nonnegative directional time averages, pathwise.**

`hdir0`, `hdir1` and `hdirSum` are the conclusions of the manuscript's temporal ergodic
theorem `p:prop:timeergodic` applied to the three nonnegative unmarked functionals
`ξᵀΓξ`, `ξ ∈ {(1,0), (0,1), (1,1)}`; `hint` is the interval integrability clause of
`HasOrdinaryEdgeBracket`.  Nothing here proves any of them. -/
theorem tendsto_ordinaryEdgeBracket_div_of_directional {Ω V : Type*}
    (cells : IndexedCells V) (Φ : V → Plane) (X : ℝ≥0 → Ω → Option V) (ω : Ω)
    (Sigma : Matrix (Fin 2) (Fin 2) ℝ) (hSsymm : ∀ i j, Sigma i j = Sigma j i)
    (hint : ∀ (i j : Fin 2) (T : ℝ), 0 ≤ T → IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X (Real.toNNReal s) ω) i j) volume 0 T)
    (hdir0 : Tendsto (directionalAverage cells Φ X ω (dirVec 1 0)) atTop
      (𝓝 (dirForm Sigma (dirVec 1 0))))
    (hdir1 : Tendsto (directionalAverage cells Φ X ω (dirVec 0 1)) atTop
      (𝓝 (dirForm Sigma (dirVec 0 1))))
    (hdirSum : Tendsto (directionalAverage cells Φ X ω (dirVec 1 1)) atTop
      (𝓝 (dirForm Sigma (dirVec 1 1)))) :
    ∀ i j : Fin 2, Tendsto
      (fun T : ℝ => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω / T) atTop
      (𝓝 (Sigma i j)) := by
  have hEv : ∀ᶠ T : ℝ in atTop, (0 : ℝ) ≤ T := eventually_ge_atTop 0
  have hsym : ∀ T : ℝ, ordinaryEdgeBracket cells Φ X 1 0 (Real.toNNReal T) ω =
      ordinaryEdgeBracket cells Φ X 0 1 (Real.toNNReal T) ω :=
    fun T => ordinaryEdgeBracket_symm cells Φ X 1 0 (Real.toNNReal T) ω
  have e00 : Tendsto
      (fun T : ℝ => ordinaryEdgeBracket cells Φ X 0 0 (Real.toNNReal T) ω / T) atTop
      (𝓝 (Sigma 0 0)) := by
    rw [← dirForm_dirVec_one_zero Sigma]
    refine hdir0.congr' ?_
    filter_upwards [hEv] with T hT
    show directionalAverage cells Φ X ω (dirVec 1 0) T =
      ordinaryEdgeBracket cells Φ X 0 0 (Real.toNNReal T) ω / T
    rw [directionalAverage_eq cells Φ X ω 1 0 hT fun i j => hint i j T hT]
    ring
  have e11 : Tendsto
      (fun T : ℝ => ordinaryEdgeBracket cells Φ X 1 1 (Real.toNNReal T) ω / T) atTop
      (𝓝 (Sigma 1 1)) := by
    rw [← dirForm_dirVec_zero_one Sigma]
    refine hdir1.congr' ?_
    filter_upwards [hEv] with T hT
    show directionalAverage cells Φ X ω (dirVec 0 1) T =
      ordinaryEdgeBracket cells Φ X 1 1 (Real.toNNReal T) ω / T
    rw [directionalAverage_eq cells Φ X ω 0 1 hT fun i j => hint i j T hT]
    ring
  have e01 : Tendsto
      (fun T : ℝ => ordinaryEdgeBracket cells Φ X 0 1 (Real.toNNReal T) ω / T) atTop
      (𝓝 (Sigma 0 1)) := by
    have hcomb : Tendsto (fun T : ℝ =>
        (directionalAverage cells Φ X ω (dirVec 1 1) T -
          directionalAverage cells Φ X ω (dirVec 1 0) T -
          directionalAverage cells Φ X ω (dirVec 0 1) T) / 2) atTop
        (𝓝 ((dirForm Sigma (dirVec 1 1) - dirForm Sigma (dirVec 1 0) -
          dirForm Sigma (dirVec 0 1)) / 2)) :=
      ((hdirSum.sub hdir0).sub hdir1).div_const 2
    rw [← entry_eq_dirForm Sigma (hSsymm 1 0)] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [hEv] with T hT
    show (directionalAverage cells Φ X ω (dirVec 1 1) T -
        directionalAverage cells Φ X ω (dirVec 1 0) T -
        directionalAverage cells Φ X ω (dirVec 0 1) T) / 2 =
      ordinaryEdgeBracket cells Φ X 0 1 (Real.toNNReal T) ω / T
    rw [directionalAverage_eq cells Φ X ω 1 1 hT fun i j => hint i j T hT,
      directionalAverage_eq cells Φ X ω 1 0 hT fun i j => hint i j T hT,
      directionalAverage_eq cells Φ X ω 0 1 hT fun i j => hint i j T hT, hsym T]
    ring
  have e10 : Tendsto
      (fun T : ℝ => ordinaryEdgeBracket cells Φ X 1 0 (Real.toNNReal T) ω / T) atTop
      (𝓝 (Sigma 1 0)) := by
    rw [hSsymm 1 0]
    simpa only [hsym] using e01
  exact Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨e00, e01⟩, Fin.forall_fin_two.2 ⟨e10, e11⟩⟩

/-- **`hLLN` from three nonnegative directional time averages, almost surely.**

This conclusion is the hypothesis `hLLN` of
`ReflectedGMS.MartingaleLimit.bracket_limit_of_hasOrdinaryEdgeBracket` and of
`MartingaleLimit.canonicalBracket_bracket_limit`, verbatim. -/
theorem bracketLLN_of_directional {Ω V : Type*} [MeasurableSpace Ω]
    (cells : IndexedCells V) (Φ : V → Plane) (X : ℝ≥0 → Ω → Option V) (P : Measure Ω)
    (Sigma : Matrix (Fin 2) (Fin 2) ℝ) (hSsymm : ∀ i j, Sigma i j = Sigma j i)
    (hint : ∀ᵐ ω ∂P, ∀ (i j : Fin 2) (T : ℝ), 0 ≤ T → IntervalIntegrable
      (fun s : ℝ => stateBracketDensity cells Φ (X (Real.toNNReal s) ω) i j) volume 0 T)
    (hdir : ∀ᵐ ω ∂P,
      Tendsto (directionalAverage cells Φ X ω (dirVec 1 0)) atTop
        (𝓝 (dirForm Sigma (dirVec 1 0))) ∧
      Tendsto (directionalAverage cells Φ X ω (dirVec 0 1)) atTop
        (𝓝 (dirForm Sigma (dirVec 0 1))) ∧
      Tendsto (directionalAverage cells Φ X ω (dirVec 1 1)) atTop
        (𝓝 (dirForm Sigma (dirVec 1 1)))) :
    ∀ᵐ ω ∂P, ∀ i j : Fin 2, Tendsto
      (fun T : ℝ => ordinaryEdgeBracket cells Φ X i j (Real.toNNReal T) ω / T) atTop
      (𝓝 (Sigma i j)) := by
  filter_upwards [hint, hdir] with ω hintω hdirω
  exact tendsto_ordinaryEdgeBracket_div_of_directional cells Φ X ω Sigma hSsymm hintω
    hdirω.1 hdirω.2.1 hdirω.2.2

/-! ### The three inputs are already in the manuscript's time-average form

`MartingaleLimit.tendsto_ordinaryEdgeBracket_div_iff` records that `hLLN` is literally the
Birkhoff time average of `Γ`.  The directional inputs above are already stated as time
averages, so a producer working on the temporal-ergodic front never has to convert. -/

/-- The integrand of the directional average is nonnegative at every state, reflection
times included.  This is what makes the transfer step of `p:prop:timeergodic` applicable
to it, and it is what fails for the individual entries `Γ_{ij}`. -/
theorem dirForm_stateBracketDensity_nonneg {V : Type*} [Countable V]
    (cells : IndexedCells V) (hcells : Geometry cells) (Φ : V → Plane) (q : Option V)
    (ξ : Fin 2 → ℝ) : 0 ≤ dirForm (stateBracketDensity cells Φ q) ξ :=
  stateBracketDensity_quadraticForm_nonneg cells hcells Φ q ξ

/-! ## From the manuscript's block averages to the Cesàro average

This section is the transfer step of `p:prop:timeergodic` (tex:1553-1562), stated for a
general nonnegative locally integrable density on the time axis.  It is purely
deterministic: the probabilistic production of the blocks `J` (the independent uniform
dyadic grid and the constant `p_δ` of `p:eq:gridprob`) is *not* carried out here; it enters
as the hypothesis `hblk`. -/

/-- `|J|⁻¹ ∫_J f`.  With `f t = F (θ t ω)` this is exactly
`ReflectedGMS.ConditionalTemporalAveraging.setAverageReal θ J F ω`, the object whose
convergence along the manuscript's dyadic chain is the checked
`ConditionalTemporalAveraging.tendsto_setAverageReal_chain_ae`. -/
noncomputable def setAvg (J : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  (volume J).toReal⁻¹ * ∫ t in J, f t

theorem volume_Ioc_zero (T : ℝ) : volume (Set.Ioc (0 : ℝ) T) = ENNReal.ofReal T := by
  rw [Real.volume_Ioc, sub_zero]

/-- Splitting a block into the interval `(0,T]` and the rest. -/
theorem setIntegral_block_decomp {f : ℝ → ℝ} {T : ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : Set.Ioc (0 : ℝ) T ⊆ J)
    (hfJ : IntegrableOn f J volume) :
    ∫ s in J, f s = (∫ s in Set.Ioc (0 : ℝ) T, f s) + ∫ s in J \ Set.Ioc (0 : ℝ) T, f s := by
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) T) (J \ Set.Ioc (0 : ℝ) T) :=
    Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  have hmeas : MeasurableSet (J \ Set.Ioc (0 : ℝ) T) := hJ.diff measurableSet_Ioc
  have h1 : IntegrableOn f (Set.Ioc (0 : ℝ) T) volume := hfJ.mono_set hsub
  have h2 : IntegrableOn f (J \ Set.Ioc (0 : ℝ) T) volume := hfJ.mono_set Set.diff_subset
  have hu : Set.Ioc (0 : ℝ) T ∪ (J \ Set.Ioc (0 : ℝ) T) = J := Set.union_diff_cancel hsub
  calc ∫ s in J, f s
      = ∫ s in Set.Ioc (0 : ℝ) T ∪ (J \ Set.Ioc (0 : ℝ) T), f s := by rw [hu]
    _ = (∫ s in Set.Ioc (0 : ℝ) T, f s) + ∫ s in J \ Set.Ioc (0 : ℝ) T, f s :=
        setIntegral_union hdisj hmeas h1 h2

theorem intervalIntegral_le_setIntegral {f : ℝ → ℝ} (hf : ∀ s, 0 ≤ f s) {T : ℝ} (hT : 0 ≤ T)
    {J : Set ℝ} (hJ : MeasurableSet J) (hsub : Set.Ioc (0 : ℝ) T ⊆ J)
    (hfJ : IntegrableOn f J volume) :
    (∫ s in (0 : ℝ)..T, f s) ≤ ∫ s in J, f s := by
  rw [intervalIntegral.integral_of_le hT, setIntegral_block_decomp hJ hsub hfJ]
  have h : 0 ≤ ∫ s in J \ Set.Ioc (0 : ℝ) T, f s :=
    setIntegral_nonneg (hJ.diff measurableSet_Ioc) fun x _ => hf x
  linarith

/-- **The comparison used by the manuscript's truncation** (tex:1561): a lower bound for a
smaller density transfers upwards.  With `g = f ⊓ K` this is how the bounded lower bound is
extended to a general nonnegative `f`. -/
theorem eventually_le_intervalAverage_mono {f g : ℝ → ℝ} (hle : ∀ s, g s ≤ f s)
    (hfint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable f volume 0 T)
    (hgint : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable g volume 0 T) {c : ℝ}
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, c - ε ≤ (∫ s in (0 : ℝ)..T, g s) / T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, c - ε ≤ (∫ s in (0 : ℝ)..T, f s) / T := by
  intro ε hε
  filter_upwards [hg ε hε, eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  refine le_trans hT ?_
  have hmono : (∫ s in (0 : ℝ)..T, g s) ≤ ∫ s in (0 : ℝ)..T, f s :=
    intervalIntegral.integral_mono_on hTpos.le (hgint T hTpos.le) (hfint T hTpos.le)
      fun x _ => hle x
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.2 hTpos.le)

/-- **The squeeze**: the two halves of the transfer give the Cesàro limit. -/
theorem tendsto_intervalAverage {f : ℝ → ℝ} {c : ℝ}
    (hU : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, (∫ s in (0 : ℝ)..T, f s) / T ≤ c + ε)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, c - ε ≤ (∫ s in (0 : ℝ)..T, f s) / T) :
    Tendsto (fun T : ℝ => (∫ s in (0 : ℝ)..T, f s) / T) atTop (𝓝 c) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hL ((c - a) / 2) (by linarith)] with T hT
    linarith
  · filter_upwards [hU ((b - c) / 2) (by linarith)] with T hT
    linarith

/-! ### `p:lem:bracketlimit` for the actual quenched array, with `hLLN` discharged -/

open ReflectedWalk

end ReflectedGMS.BracketTimeAverage
