/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Step1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide
import LatticeProb.Bonanno.ReflectedWalk.TimeChange
import LatticeProb.Bonanno.ReflectedWalk.Theorem16

/-!
# Step 1 of the uniqueness proof, assembled (Gwynne–Sung, arXiv:2506.18827, p. 26)

`Theorem16.lean` proves Theorem 1.6 from one explicitly named hypothesis, `hstep1`: Step 1 of
the uniqueness proof, in the two pieces Step 1 produces — measurable time changes `X̃ⁿ` of an
arbitrary process `X̃` satisfying (i)–(vi), approximating `X̃` at fixed times
(`Theorem16.ApproximatedAtFixedTimes`), and the identity in law `X̃ⁿ =ᵈ Xⁿ` at one time, i.e.
one-time marginals given by a family `q` that does not depend on the process.  This file
**discharges `hstep1`** (`Theorem16.step1`) by joining the two files that prove its halves
independently:

* the **law side**, `UniquenessGeneralSide.lean`: the pair `((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)` of the
  embedded chain of (3.31) and its holding times has the law
  `E.chainLaw hG n z ⊗ₘ holdingKernel w` (`map_embeddedPairOf_exhaustion`), so the time change
  (3.32) `processTildeN` has — after replacement by a genuinely measurable version,
  `exists_measurable_processTildeN` — the one-time marginals of the constructed chain `Xⁿ` of
  (3.15), which are the transition function `(chainFamily E w hG n).transition`
  (`ContinuousTimeChain.chainFamily_transition_eq`);
* the **pathwise side**, `TimeChange.lean`: Step 2 for the time change (3.32) `processN`,
  `approximatedAtFixedTimes_processN`, from the covering lemma and the rewind bound
  (3.33)–(3.34) in the orientation in which they hold, under two distributional hypotheses on
  the recursion (3.31): that it never gets stuck (`StepTimesFinite`, which is
  `ae_forall_definedAt` through `mem_definedAt_iff`), and that the level-`n` holding times
  diverge (`∑_j Tⁿ_j = ∞` a.s.).

The two files render (3.32) as `jumpPath` of the pair, along the stopping times of the *same*
recursion, and differ only in how the holding times are cast to `ℝ` (`holdingSeq`, through
`[0,∞)`, against `holdingSeqOf`, through `ENNReal.toReal`); `processN_eq_processTildeN` shows
that they agree wherever the recursion does not get stuck, which is almost surely.

## What is carried

One hypothesis remains, `HoldingTimesDiverge G hmin E`: the divergence `∑_j Tⁿ_j = ∞` a.s. of
the holding times of (3.31) at the levels of the exhaustion `E`, the paper's "By Property (v),
a.s. `X̃` returns to its starting point infinitely many times … a.s. `lim_k ∑_{j ≤ k} Tⁿ_j = ∞`"
(p. 26).  It is `HoldingDivergence.lean`'s `Theorem16.ae_tsum_stepHolding_eq_top`, quantified
over the rate function, the process family and the starting point; it is named here rather
than imported so that this file does not depend on a file under construction, and
`theorem16_of_holdingTimesDiverge` is closed by the substitution recorded in its docstring.

Right continuity at `∞` (`RightContinuousAtInfty`), which every theorem of
`UniquenessGeneralSide.lean` carries as `hR`, is a conjunct of `IsReflectedWalk` (the
user-approved completion of property (ii), recorded in `Theorem16Statement.lean`), and
`step1` reads it off there: `(h𝓨 v).2.2.2.1`.

The `hstep1` of `theorem16` is quantified before the antecedents `Countable V`, `Infinite V`,
`G.toSimpleGraph.Connected` of `Theorem16Statement`; the exhaustion of `G` that defines `q`
needs them (Step 1 is about countably infinite connected graphs), and they are available after
introducing the statement, which is where `theorem16_of_holdingTimesDiverge` supplies `hstep1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk
namespace Theorem16

variable {V : Type u} {Ω : Type u} [mΩ : MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V}

/-! ## 1.  The two renderings of (3.32) agree -/

omit mΩ in
/-- **(3.32), once.**  `TimeChange.processN` and `UniquenessGeneralSide.processTildeN` are both
`ContinuousTimeChain.jumpPath` of the embedded chain and the holding times of the recursion
(3.31); the embedded chains are definitionally the same sequence, and the holding times agree
as real sequences wherever every `tⁿ_j` is finite (`TimeChange.stepHolding_eq_coe`, with
`stepHolding` definitionally `holdingTime`). -/
lemma TimeChange.processN_eq_processTildeN (Gn : Finset V) (v₀ : V) {ω : Ω}
    (hfin : TimeChange.StepTimesFinite X Gn ω) (t : ℝ≥0) :
    TimeChange.processN X Gn v₀ t ω = processTildeN X Gn v₀ t ω := by
  have h : TimeChange.holdingSeq X Gn ω = holdingSeqOf X Gn ω := by
    funext j
    show ((TimeChange.holdAt X Gn j ω : ℝ≥0) : ℝ) = (holdingTime X Gn j ω).toReal
    rw [show holdingTime X Gn j ω = TimeChange.stepHolding X Gn j ω from rfl,
      TimeChange.stepHolding_eq_coe hfin j]
    rfl
  exact congrArg (fun s => ContinuousTimeChain.jumpPath (embeddedChainOf X Gn v₀ ω, s) t) h

/-! ## 2.  The divergence of the holding times, named -/

/-- **The holding times of (3.31) diverge at every level of the exhaustion `E`** (p. 26): for
every rate function `w > 0`, every process family satisfying (i)–(vi), every starting point `x`
and every level `n`, almost surely `∑_j Tⁿ_j = ∞` — "By Property (v), a.s. `X̃` returns to its
starting point infinitely many times … a.s. `lim_k ∑_{j ≤ k} Tⁿ_j = ∞`".  This is the one
distributional input of `TimeChange.approximatedAtFixedTimes_processN` that
`UniquenessGeneralSide.lean` does not supply.  It is exactly the conclusion of
`HoldingDivergence.lean`'s `Theorem16.ae_tsum_stepHolding_eq_top`, quantified over `w`, the
family and the starting point. -/
def HoldingTimesDiverge (G : ConductanceGraph V) (hmin : G.EnergyMinimizer)
    (E : G.Exhaustion) : Prop :=
  ∀ (w : V → ℝ), (∀ x, 0 < w x) → ∀ 𝓨 : ProcessFamily V, IsReflectedWalk G w hmin 𝓨 →
    ∀ (x : V) (n : ℕ), ∀ᵐ ω ∂𝓨.P x, ∑' j, TimeChange.stepHolding 𝓨.X (E.Gsub n) j ω = ⊤

/-! ## 3.  Step 1 for one process -/

section Assembly

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓨 : ProcessFamily V}

/-- **Step 1 of the uniqueness proof, for one process and one starting point** (p. 26).  For a
process family `𝓨` satisfying (i)–(vi) and a starting point `x`, the measurable versions of the
time changes `X̃ⁿ` of (3.32) at the levels `n_x + n` of the exhaustion `E`
(`exists_measurable_processTildeN`) approximate `X̃` at fixed times
(`TimeChange.approximatedAtFixedTimes_processN`, transported along the a.s. identification of
the two renderings of (3.32)), and their one-time marginals are the transition function of the
constructed chain `Xⁿ` of (3.15) at the same level.

`hR` is right continuity at `∞`, in the form in which `UniquenessGeneralSide.lean` carries it;
`hdiv` is the divergence of the holding times at the levels used. -/
theorem exists_approximant (h : IsReflectedWalk G w hmin 𝓨) (hG : G.toSimpleGraph.Connected)
    (hw : ∀ x, 0 < w x) (hR : ∀ v, RightContinuousAtInfty (𝓨.P v) 𝓨.X) (E : G.Exhaustion)
    (x : V)
    (hdiv : ∀ n, ∀ᵐ ω ∂𝓨.P x,
      ∑' j, TimeChange.stepHolding 𝓨.X (E.Gsub (E.nz x + n)) j ω = ⊤) :
    ∃ Xn : ℕ → ℝ≥0 → 𝓨.Ω → Option V, (∀ n s, Measurable (Xn n s)) ∧
      ApproximatedAtFixedTimes (𝓨.P x) 𝓨.X Xn ∧
      ∀ n t y, 𝓨.P x {ω | Xn n t ω = some y} =
        (ContinuousTimeChain.chainFamily E w hG n).transition x t y := by
  obtain ⟨Xn, hXn, hae, hlaw⟩ := exists_measurable_processTildeN h hG hw hR E x x
  refine ⟨Xn, hXn, ?_, fun n t y =>
    (hlaw n t y).trans (ContinuousTimeChain.chainFamily_transition_eq hG E w hw n x t y).symm⟩
  have hdef : ∀ n, ∀ᵐ ω ∂𝓨.P x, TimeChange.StepTimesFinite 𝓨.X (E.Gsub (E.nz x + n)) ω := by
    intro n
    filter_upwards [ae_forall_definedAt h hG x hR (E.nonempty (E.nz x + n))] with ω hω
    exact fun j => ((mem_definedAt_iff _ j ω).1 (hω j)).1
  refine TimeChange.approximatedAtFixedTimes_congr
    (Xn := fun n => TimeChange.processN 𝓨.X (E.Gsub (E.nz x + n)) x) (fun n => ?_) ?_
  · filter_upwards [hae n, hdef n] with ω hω hfin t
    show Xn n t ω = TimeChange.processN 𝓨.X (E.Gsub (E.nz x + n)) x t ω
    rw [hω t, TimeChange.processN_eq_processTildeN (E.Gsub (E.nz x + n)) x hfin t]
  · exact TimeChange.approximatedAtFixedTimes_processN (Gn := fun n => E.Gsub (E.nz x + n))
      (z := x) (fun m n hmn => Finset.coe_subset.2 (E.subset_of_le (Nat.add_le_add_left hmn _)))
      (fun v => ⟨E.nz v, E.subset_of_le (Nat.le_add_left _ _) (E.mem_Gsub_nz v)⟩)
      𝓨.measurable_X (h x).2.1 (h x).2.2.1 (hR x) hdef hdiv

end Assembly

/-! ## 4.  `hstep1` -/

/-- **Step 1 of the uniqueness proof** (p. 26), in the form `theorem16` consumes as `hstep1`:
for every rate function `w > 0` there is one family of laws `q` — the transition function of the
continuous-time chain (3.15) at the levels `n_x + n` of the exhaustion `E`,
`ContinuousTimeChain.chainFamily_transition_eq` — such that every process family satisfying
(i)–(vi) is approximated at fixed times by measurable time changes with one-time marginals `q`.
Right continuity at `∞` is read off `IsReflectedWalk` (`(h𝓨 v).2.2.2.1`). -/
theorem step1 [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
    {G : ConductanceGraph V} (hmin : G.EnergyMinimizer) (hG : G.toSimpleGraph.Connected)
    (E : G.Exhaustion) (hdiv : HoldingTimesDiverge G hmin E) (w : V → ℝ)
    (hw : ∀ x, 0 < w x) :
    ∃ q : V → ℕ → ℝ≥0 → V → ℝ≥0∞, ∀ 𝓨 : ProcessFamily V, IsReflectedWalk G w hmin 𝓨 →
      ∀ x : V, ∃ Xn : ℕ → ℝ≥0 → 𝓨.Ω → Option V,
        (∀ n s, Measurable (Xn n s)) ∧
          ApproximatedAtFixedTimes (𝓨.P x) 𝓨.X Xn ∧
          ∀ n t y, 𝓨.P x {ω | Xn n t ω = some y} = q x n t y :=
  ⟨fun x n t y => (ContinuousTimeChain.chainFamily E w hG n).transition x t y,
    fun 𝓨 h𝓨 x => exists_approximant h𝓨 hG hw (fun v => (h𝓨 v).2.2.2.1) E x
      fun n => hdiv w hw 𝓨 h𝓨 x (E.nz x + n)⟩

end Theorem16

variable {V : Type*}

/-! ## 5.  Theorem 1.6, closed -/

/-- **Theorem 1.6** (Gwynne–Sung, p. 5), with `hstep1` discharged: `theorem16` applied to
`Theorem16.step1`, with the exhaustion of `G` (`Existence.exists_exhaustion`) and the discrete
σ-algebra on `V` supplied after the antecedents of `Theorem16Statement` are introduced.

The only hypothesis is the divergence of the holding times of (3.31),
`Theorem16.HoldingTimesDiverge G hmin E`, under the same antecedents (which the instances of
`HoldingDivergence.lean` need).  It is discharged by

  `fun _ hinf hG E w hw 𝓨 h𝓨 x n =>
    let _ : MeasurableSpace V := ⊤
    have _ : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
    Theorem16.ae_tsum_stepHolding_eq_top h𝓨 hG hw (fun v => (h𝓨 v).2.2.2.1) E x n`

(`HoldingDivergence.lean`; `Countable V` and `Nontrivial V` are the local instances `_` and
`hinf`). -/
theorem theorem16_of_holdingTimesDiverge (G : ConductanceGraph V) (hmin : G.EnergyMinimizer)
    (hdiv : Countable V → Infinite V → G.toSimpleGraph.Connected →
      ∀ E : G.Exhaustion, Theorem16.HoldingTimesDiverge G hmin E) :
    Theorem16Statement G hmin := by
  intro hV hinf hG
  have : Countable V := hV
  let _ : MeasurableSpace V := ⊤
  have _ : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  obtain ⟨E⟩ := Existence.exists_exhaustion hG
  exact theorem16 G hmin (Theorem16.step1 hmin hG E (hdiv hV hinf hG E)) hV hinf hG

end ReflectedWalk
