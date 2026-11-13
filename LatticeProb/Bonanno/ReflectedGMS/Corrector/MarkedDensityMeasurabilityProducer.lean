/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedDensityMeasurabilityProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The input `hdens` of the harmonic-coordinate assembly, discharged

`HarmonicCoordinateAssembly.MarkedDensityMeasurability ν ms` is the named open input that
bundles the four measurability statements the approximation clause (7) of
`HarmonicMainStatement.IsHarmonicCoordinate` needs:

1. the graph-neighbourhood errors `markedGraphNeighborhoodError ms radius m`;
2. the rooted specific energy of every stage `φ_m`;
3. the rooted specific energy of the gradient errors `φ_m − Φ`
   (`markedSpecificGradientError`);
4. the rooted specific energy of the marked limit `Φ` itself.

The assembly records that the project had **no producer** for any of them — the same gap that
`hΓmeas` used to carry in `InvarianceAssembly`.  This module discharges the whole input from
the manuscript's own hypotheses, the measurability input `hmeas` of the assembly, and nothing
else: `markedDensityMeasurability_of_massTransport`.

## Clauses 2–4: the rooted specific energy

These are instances of `MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity`,
which is unconditional.  Mass transport and the (FE) moment enter only through
`HarmonicCoordinateAssembly.ae_mem_sublinearEvent`, which identifies the gated interpolant
`gatedApproximant m` — the field `hmeas` asserts to be measurable — with the concrete `phi` at
the active labels of almost every marked environment.  Clause 4 needs neither: the marked
limit already *is* a measurable label field.

## Clause 1: the graph-neighbourhood error

This is the genuinely new ingredient.  The supremum runs over the ball of the **graph
metric** of the decoded environment, around a root selected by a geometric test, in a vertex
type that varies with the environment; none of that is a composition of measurable coordinate
maps.

The route replaces the graph ball by a label-level predicate.  `LazyReach e r k n` says that
the label `n` is joined to `r` by a chain of at most `k` positive conductance entries of the
code `e`, allowing repetitions.  It is defined by recursion on `k`, so each of its level sets
is a countable union of measurable conditions (`measurableSet_lazyReach`).  Two walk lemmas
identify it with the graph ball:

* `lazyReach_of_walk` — every walk of the decoded simple graph yields a chain of its own
  length, by induction on the walk;
* `edist_le_of_lazyReach` — every chain of length `k` bounds the graph `edist` by `k`, by the
  triangle inequality and `SimpleGraph.edist_eq_one_iff_adj`; the intermediate labels are
  automatically active because an absent label carries no positive conductance
  (`Code.AdmissibleConductance.absent`).

Together they give `mem_ball_iff_lazyReach`, and the supremum over the ball becomes a
supremum over **all** labels of a clipped term that vanishes off the ball
(`labelNeighborhoodError_eq`).  Clipping at `1` makes every term lie in `[0, 1]`, so the
conditional suprema are bounded without any finiteness of the ball.  The root is then handled
by the slot-sum technique of `Spatial/RootedFiniteEnergyDensityMeasurable`: at most one label
has the origin in its cell interior, and on the boundary mask the observable is zero by
convention.

## Scope

Nothing here proves that the neighbourhood errors converge (that is the separate input
`hnbr`), that the specific energies are finite (that is `hspec`), or that the concrete
interpolants are measurable (that is `hmeas`, which enters only as a hypothesis).  This file
proves no main theorem: `harmonicCoordinateConclusions_of_named_inputs_of_nine` is the
assembly's reduction with one of its ten inputs removed, and its nine remaining hypotheses
are open.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Classical

namespace ReflectedGMS.MarkedDensityMeasurabilityProducer

open Code StatementIngredients EnvironmentLaws RootDensities
open DyadicApproximation HarmonicLawIngredients HarmonicMainStatement
open RootedFiniteEnergyDensityMeasurable MarkedRootedSpecificEnergyMeasurability
open HarmonicCoordinateAssembly

/-! ### Bounded reachability at the level of code labels -/

/-- **Bounded lazy reachability of code labels.**  `LazyReach e r k n` holds when the label
`n` is joined to `r` by a chain of at most `k` positive conductance entries of `e`;
repetitions are allowed, so the predicate is monotone in `k` by construction.  Intermediate
labels are automatically active: an absent label carries no positive conductance. -/
def LazyReach (e : Env) (r : ℕ) : ℕ → ℕ → Prop := fun k =>
  Nat.rec (motive := fun _ => ℕ → Prop) (fun n => n = r)
    (fun _ ih n => ih n ∨ ∃ u : ℕ, ih u ∧ 0 < e.val.2 u n) k

theorem lazyReach_succ (e : Env) (r k n : ℕ) :
    LazyReach e r (k + 1) n ↔
      LazyReach e r k n ∨ ∃ u : ℕ, LazyReach e r k u ∧ 0 < e.val.2 u n := Iff.rfl

theorem lazyReach_mono (e : Env) (r : ℕ) {k l : ℕ} (hkl : k ≤ l) {n : ℕ}
    (h : LazyReach e r k n) : LazyReach e r l n := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ l _ ih => exact Or.inl ih

/-- From an **absent** root no label but the root itself is reachable. -/
theorem eq_of_lazyReach_of_absent {e : Env} {r : ℕ} (hr : e.val.1 r = none) :
    ∀ (k n : ℕ), LazyReach e r k n → n = r := by
  intro k
  induction k with
  | zero => intro n h; exact h
  | succ k ih =>
      intro n h
      rcases h with h | ⟨u, hu, hc⟩
      · exact ih n h
      · have hur : u = r := ih u hu
        rw [hur, (admissible e).absent r n (Or.inl hr)] at hc
        exact absurd hc (lt_irrefl 0)

/-! ### The graph ball is a level set of lazy reachability -/

/-- Every walk of the decoded simple graph yields a chain of its own length. -/
theorem lazyReach_of_walk (e : Env) {v r : Vertex e.val}
    (p : (decode e).graph.toSimpleGraph.Walk v r) :
    LazyReach e r.val p.length v.val := by
  induction p with
  | nil => exact rfl
  | @cons u w x h q ih =>
      have hpos : 0 < e.val.2 w.val u.val := by
        rw [(admissible e).symm w.val u.val]
        exact h
      exact Or.inr ⟨w.val, ih, hpos⟩

/-- Every chain of length `k` bounds the graph distance to the root by `k`. -/
theorem edist_le_of_lazyReach (e : Env) (r : Vertex e.val) :
    ∀ (k n : ℕ), LazyReach e r.val k n →
      ∃ h : (e.val.1 n).isSome,
        (decode e).graph.toSimpleGraph.edist (⟨n, h⟩ : Vertex e.val) r ≤ (k : ℕ∞) := by
  intro k
  induction k with
  | zero =>
      intro n h
      have hn : n = r.val := h
      subst hn
      exact ⟨r.property, by simp⟩
  | succ k ih =>
      intro n h
      rcases h with h | ⟨u, hu, hc⟩
      · obtain ⟨hn, hle⟩ := ih n h
        refine ⟨hn, hle.trans ?_⟩
        exact_mod_cast Nat.le_succ k
      · obtain ⟨hu', hle⟩ := ih u hu
        have hn : (e.val.1 n).isSome := by
          by_contra hcon
          have hnone : e.val.1 n = none := by
            rw [← Option.not_isSome_iff_eq_none]
            exact hcon
          rw [(admissible e).absent u n (Or.inr hnone)] at hc
          exact absurd hc (lt_irrefl 0)
        refine ⟨hn, ?_⟩
        have hadj : (decode e).graph.toSimpleGraph.Adj (⟨n, hn⟩ : Vertex e.val) ⟨u, hu'⟩ := by
          show 0 < e.val.2 n u
          rw [(admissible e).symm n u]
          exact hc
        have h1 : (decode e).graph.toSimpleGraph.edist (⟨n, hn⟩ : Vertex e.val) ⟨u, hu'⟩ = 1 :=
          SimpleGraph.edist_eq_one_iff_adj.2 hadj
        have hcast : (1 : ℕ∞) + (k : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) := by
          push_cast
          ring
        calc (decode e).graph.toSimpleGraph.edist (⟨n, hn⟩ : Vertex e.val) r
            ≤ (decode e).graph.toSimpleGraph.edist (⟨n, hn⟩ : Vertex e.val) ⟨u, hu'⟩
              + (decode e).graph.toSimpleGraph.edist (⟨u, hu'⟩ : Vertex e.val) r :=
              SimpleGraph.edist_triangle
          _ ≤ 1 + (k : ℕ∞) := by
              rw [h1]
              exact add_le_add (le_refl (1 : ℕ∞)) hle
          _ = ((k + 1 : ℕ) : ℕ∞) := hcast

/-- **The graph ball of radius `radius + 1` is the level set of lazy reachability at
`radius`.**  This is the statement that replaces the graph metric by a countable label
condition. -/
theorem mem_ball_iff_lazyReach (e : Env) (r v : Vertex e.val) (radius : ℕ) :
    v ∈ (decode e).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞)
      ↔ LazyReach e r.val radius v.val := by
  have hsucc : ((radius : ℕ) : ℕ∞) < ((radius + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self radius
  constructor
  · intro hv
    have hlt : (decode e).graph.toSimpleGraph.edist v r < ((radius + 1 : ℕ) : ℕ∞) := hv
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top (ne_top_of_lt hlt)
    have hplen : ((p.length : ℕ) : ℕ∞) < ((radius + 1 : ℕ) : ℕ∞) := by
      rw [hp]
      exact hlt
    have hle : p.length ≤ radius := by
      have hlt' : p.length < radius + 1 := by exact_mod_cast hplen
      omega
    exact lazyReach_mono e r.val hle (lazyReach_of_walk e p)
  · intro h
    obtain ⟨hn, hle⟩ := edist_le_of_lazyReach e r radius v.val h
    have hv : (⟨v.val, hn⟩ : Vertex e.val) = v := rfl
    rw [hv] at hle
    show (decode e).graph.toSimpleGraph.edist v r < ((radius + 1 : ℕ) : ℕ∞)
    exact lt_of_le_of_lt hle hsucc

/-! ### The label form of the neighbourhood error -/

section LabelForm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The clipped neighbourhood error read at a code label, with the normalizing root given by
its own label.  It vanishes at inactive labels and off the reachability level set, so the
supremum over all labels is the supremum over the graph ball. -/
noncomputable def labelBallTerm (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ)
    (ω : Ω) (r n : ℕ) : ℝ :=
  if ((E ω).val.1 n).isSome ∧ LazyReach (E ω) r radius n then
    min 1 ‖(Θ ω n - Θ ω r) - Ψ ω n‖
  else 0

theorem labelBallTerm_le_one (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ)
    (ω : Ω) (r n : ℕ) : labelBallTerm E Θ Ψ radius ω r n ≤ 1 := by
  unfold labelBallTerm
  split
  · exact min_le_left _ _
  · exact zero_le_one

/-- The label form of the neighbourhood error: the supremum over **all** labels. -/
noncomputable def labelNeighborhoodError (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ)
    (ω : Ω) (r : ℕ) : ℝ :=
  ⨆ n : ℕ, labelBallTerm E Θ Ψ radius ω r n

theorem bddAbove_labelBallTerm (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ)
    (ω : Ω) (r : ℕ) :
    BddAbove (Set.range fun n : ℕ => labelBallTerm E Θ Ψ radius ω r n) := by
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  exact labelBallTerm_le_one E Θ Ψ radius ω r n

/-- **From an absent root the label form vanishes.** -/
theorem labelNeighborhoodError_of_absent (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ)
    (ω : Ω) {r : ℕ} (hr : (E ω).val.1 r = none) :
    labelNeighborhoodError E Θ Ψ radius ω r = 0 := by
  have hz : ∀ n : ℕ, labelBallTerm E Θ Ψ radius ω r n = 0 := by
    intro n
    refine if_neg ?_
    rintro ⟨hn, hreach⟩
    have hnr : n = r := eq_of_lazyReach_of_absent hr radius n hreach
    rw [hnr, hr] at hn
    exact absurd hn (by simp)
  show (⨆ n : ℕ, labelBallTerm E Θ Ψ radius ω r n) = 0
  simp only [hz]
  exact ciSup_const

/-- **The label form is the supremum over the graph ball.**  The two fields `f` and `g` are
the normalized approximant and the limit, read on the decoded vertex type. -/
theorem labelNeighborhoodError_eq (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ) (ω : Ω)
    (r : Vertex (E ω).val) (f g : Vertex (E ω).val → Plane)
    (hf : ∀ v : Vertex (E ω).val, f v = Θ ω v.val - Θ ω r.val)
    (hg : ∀ v : Vertex (E ω).val, g v = Ψ ω v.val) :
    labelNeighborhoodError E Θ Ψ radius ω r.val
      = ⨆ v : (decode (E ω)).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
          min 1 ‖f v.val - g v.val‖ := by
  have hball : r ∈ (decode (E ω)).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞) := by
    refine SimpleGraph.mem_ball_self ?_
    exact_mod_cast Nat.succ_pos radius
  have hbdd2 : BddAbove (Set.range fun v :
      ↥((decode (E ω)).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞)) =>
        min 1 ‖f v.val - g v.val‖) := by
    refine ⟨1, ?_⟩
    rintro x ⟨v, rfl⟩
    exact min_le_left _ _
  haveI : Nonempty
      ↥((decode (E ω)).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞)) := ⟨⟨r, hball⟩⟩
  have hterm : ∀ (n : ℕ) (hn : ((E ω).val.1 n).isSome),
      LazyReach (E ω) r.val radius n →
        labelBallTerm E Θ Ψ radius ω r.val n
          = min 1 ‖f (⟨n, hn⟩ : Vertex (E ω).val) - g ⟨n, hn⟩‖ := by
    intro n hn hreach
    rw [hf ⟨n, hn⟩, hg ⟨n, hn⟩]
    exact if_pos ⟨hn, hreach⟩
  show (⨆ n : ℕ, labelBallTerm E Θ Ψ radius ω r.val n) = _
  refine le_antisymm (ciSup_le fun n => ?_) (ciSup_le fun v => ?_)
  · by_cases hcond : ((E ω).val.1 n).isSome ∧ LazyReach (E ω) r.val radius n
    · have hmem : (⟨n, hcond.1⟩ : Vertex (E ω).val) ∈
          (decode (E ω)).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞) :=
        (mem_ball_iff_lazyReach (E ω) r ⟨n, hcond.1⟩ radius).2 hcond.2
      rw [hterm n hcond.1 hcond.2]
      exact le_ciSup hbdd2 ⟨⟨n, hcond.1⟩, hmem⟩
    · have h0 : labelBallTerm E Θ Ψ radius ω r.val n = 0 := if_neg hcond
      rw [h0]
      refine le_trans ?_ (le_ciSup hbdd2 ⟨r, hball⟩)
      exact le_min zero_le_one (norm_nonneg _)
  · have hreach : LazyReach (E ω) r.val radius v.val.val :=
      (mem_ball_iff_lazyReach (E ω) r v.val radius).1 v.property
    have hval : (⟨v.val.val, v.val.property⟩ : Vertex (E ω).val) = v.val := rfl
    have := hterm v.val.val v.val.property hreach
    rw [hval] at this
    rw [← this]
    exact le_ciSup (bddAbove_labelBallTerm E Θ Ψ radius ω r.val) v.val.val

end LabelForm

/-! ### Measurability of the label form -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_lazyReach {E : Ω → Env} (hE : Measurable E) (r : ℕ) :
    ∀ (k n : ℕ), MeasurableSet {ω : Ω | LazyReach (E ω) r k n} := by
  intro k
  induction k with
  | zero =>
      intro n
      by_cases h : n = r
      · have hset : {ω : Ω | LazyReach (E ω) r 0 n} = Set.univ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          exact h
        rw [hset]
        exact MeasurableSet.univ
      · have hset : {ω : Ω | LazyReach (E ω) r 0 n} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact h
        rw [hset]
        exact MeasurableSet.empty
  | succ k ih =>
      intro n
      have hEq : {ω : Ω | LazyReach (E ω) r (k + 1) n}
          = {ω : Ω | LazyReach (E ω) r k n} ∪
            ⋃ u : ℕ, ({ω : Ω | LazyReach (E ω) r k u} ∩
              {ω : Ω | 0 < (E ω).val.2 u n}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
        exact lazyReach_succ (E ω) r k n
      rw [hEq]
      refine (ih n).union (MeasurableSet.iUnion fun u => (ih u).inter ?_)
      exact measurableSet_lt measurable_const ((measurable_conductance_env u n).comp hE)

theorem measurable_labelBallTerm {E : Ω → Env} (hE : Measurable E) {Θ Ψ : Ω → ℕ → Plane}
    (hΘ : ∀ n : ℕ, Measurable fun ω : Ω => Θ ω n)
    (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) (radius r n : ℕ) :
    Measurable fun ω : Ω => labelBallTerm E Θ Ψ radius ω r n := by
  have hset : MeasurableSet
      {ω : Ω | ((E ω).val.1 n).isSome ∧ LazyReach (E ω) r radius n} :=
    (((HarmonicCoordinateAssembly.measurable_slot n).comp hE)
      Spatial.measurableSet_slotIsSome).inter (measurableSet_lazyReach hE r radius n)
  have hval : Measurable fun ω : Ω => min 1 ‖(Θ ω n - Θ ω r) - Ψ ω n‖ :=
    measurable_const.min (((hΘ n).sub (hΘ r)).sub (hΨ n)).norm
  exact Measurable.ite hset hval measurable_const

theorem measurable_labelNeighborhoodError {E : Ω → Env} (hE : Measurable E)
    {Θ Ψ : Ω → ℕ → Plane} (hΘ : ∀ n : ℕ, Measurable fun ω : Ω => Θ ω n)
    (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) (radius r : ℕ) :
    Measurable fun ω : Ω => labelNeighborhoodError E Θ Ψ radius ω r :=
  Measurable.iSup fun n => measurable_labelBallTerm hE hΘ hΨ radius r n

end Measurability

/-! ### The rooted representative of the neighbourhood error -/

section Rooted

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable representative of the rooted neighbourhood error**: the label form
summed over the labels whose cell interior contains the origin, cut off on the global
boundary mask.  At most one term is nonzero. -/
noncomputable def rootedNeighborhoodRepr (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ)
    (ω : Ω) : ℝ :=
  Set.indicator (maskAt E)ᶜ
    (fun ω' : Ω => ∑' r : ℕ, (rootSlotSet E r).indicator
      (fun ω'' : Ω => labelNeighborhoodError E Θ Ψ radius ω'' r) ω') ω

theorem measurable_rootedNeighborhoodRepr {E : Ω → Env} (hE : Measurable E)
    {Θ Ψ : Ω → ℕ → Plane} (hΘ : ∀ n : ℕ, Measurable fun ω : Ω => Θ ω n)
    (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) (radius : ℕ) :
    Measurable (rootedNeighborhoodRepr E Θ Ψ radius) := by
  refine Measurable.indicator ?_ (measurableSet_maskAt hE).compl
  refine Measurable.tsum fun r => ?_
  exact (measurable_labelNeighborhoodError hE hΘ hΨ radius r).indicator
    (measurableSet_rootSlotSet hE r)

/-- **The representative is the rooted neighbourhood error.** -/
theorem rootedNeighborhoodRepr_eq (E : Ω → Env) (Θ Ψ : Ω → ℕ → Plane) (radius : ℕ) (ω : Ω)
    (P : Vertex (E ω).val → Vertex (E ω).val → Plane) (Q : Vertex (E ω).val → Plane)
    (hP : ∀ r v : Vertex (E ω).val, P r v = Θ ω v.val - Θ ω r.val)
    (hQ : ∀ v : Vertex (E ω).val, Q v = Ψ ω v.val) :
    rootedNeighborhoodRepr E Θ Ψ radius ω
      = (rootAt (decode (E ω)) 0).elim 0 fun r =>
          ⨆ v : (decode (E ω)).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
            min 1 ‖P r v.val - Q v.val‖ := by
  by_cases hz : (0 : Plane) ∈ boundaryMask (decode (E ω))
  · have hmem : ω ∉ (maskAt E)ᶜ := fun h => h hz
    rw [rootedNeighborhoodRepr, Set.indicator_of_notMem hmem,
      rootAt_eq_none_of_mem_boundaryMask (decode (E ω)) hz]
    rfl
  · have hgeom := decode_geometry (E ω)
    have hmem : ω ∈ (maskAt E)ᶜ := hz
    obtain ⟨r, hr, hint⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
    have huniq := existsUnique_interiorRoot_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
    have hsingle : ∀ n : ℕ, n ≠ r.val →
        (rootSlotSet E n).indicator
          (fun ω'' : Ω => labelNeighborhoodError E Θ Ψ radius ω'' n) ω = 0 := by
      intro n hn
      cases hcase : (E ω).val.1 n with
      | none =>
          by_cases hmemn : ω ∈ rootSlotSet E n
          · rw [Set.indicator_of_mem hmemn,
              labelNeighborhoodError_of_absent E Θ Ψ radius ω hcase]
          · rw [Set.indicator_of_notMem hmemn]
      | some K =>
          have hsome : ((E ω).val.1 n).isSome := by rw [hcase]; rfl
          have hne : (⟨n, hsome⟩ : Vertex (E ω).val) ≠ r := fun h => hn (congrArg Subtype.val h)
          have hnot : ω ∉ rootSlotSet E n := by
            intro hmemn
            have hmem' : (0 : Plane) ∈
                interior ((decode (E ω)).cell ⟨n, hsome⟩ : Set Plane) := by
              rw [← slotCell_eq_cell (E ω) ⟨n, hsome⟩]
              exact hmemn
            exact hne (huniq.unique hmem' hint)
          rw [Set.indicator_of_notMem hnot]
    have hmemr : ω ∈ rootSlotSet E r.val := by
      show (0 : Plane) ∈ interior (slotCell (E ω) r.val : Set Plane)
      rw [slotCell_eq_cell]
      exact hint
    rw [rootedNeighborhoodRepr, Set.indicator_of_mem hmem, tsum_eq_single r.val hsingle,
      Set.indicator_of_mem hmemr, hr]
    exact labelNeighborhoodError_eq E Θ Ψ radius ω r (P r) Q (fun v => hP r v) hQ

end Rooted

/-! ### The four clauses of `MarkedDensityMeasurability` -/

/-- The label field of the marked limiting potential: the marked difference field read from
the canonical base label.  It is measurable at every label. -/
theorem measurable_markedPotentialLabel (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (n : ℕ) :
    Measurable fun ω : MarkedEnvironment =>
      markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) n) := by
  have hF : Measurable fun q : MarkedEnvironment × ℕ =>
      markedDifferenceField ms q.1 (Nat.pair q.2 n) :=
    measurable_from_prod_countable_left fun k =>
      (measurable_pi_apply (Nat.pair k n)).comp (measurable_markedDifferenceField ms hmeas)
  exact hF.comp (measurable_id.prodMk (measurable_baseLabel.comp measurable_fst))

/-- On the good event the gated interpolants are the concrete block interpolants. -/
theorem phi_eq_gatedApproximant {m : ℕ} {ω : MarkedEnvironment} (hG : ω.1 ∈ SublinearEvent)
    (v : Vertex ω.1.val) : phi (decode ω.1) ω.2 m v = gatedApproximant m ω v.val := by
  rw [gatedApproximant_of_mem m hG v.val, approximationAtLabel_vertex]

/-- The same, as an identity of fields on the decoded vertex type. -/
theorem gatedApproximant_field_eq {m : ℕ} {ω : MarkedEnvironment} (hG : ω.1 ∈ SublinearEvent) :
    (fun v : Vertex ω.1.val => gatedApproximant m ω v.val) = phi (decode ω.1) ω.2 m := by
  funext v
  exact (phi_eq_gatedApproximant hG v).symm

/-- **Clause 1: the graph-neighbourhood errors are almost surely measurable.** -/
theorem aemeasurable_markedGraphNeighborhoodError (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (radius m : ℕ) :
    AEMeasurable (markedGraphNeighborhoodError ms radius m) (ν.prod gridLaw) := by
  refine (measurable_rootedNeighborhoodRepr (E := (Prod.fst : MarkedEnvironment → Env))
    measurable_fst (Θ := fun ω n => gatedApproximant m ω n)
    (Ψ := fun ω n => markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) n))
    (fun n => hmeas m n) (measurable_markedPotentialLabel ms hmeas) radius).aemeasurable.congr ?_
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE)] with ω hG
  refine rootedNeighborhoodRepr_eq (E := (Prod.fst : MarkedEnvironment → Env))
    (Θ := fun ω n => gatedApproximant m ω n)
    (Ψ := fun ω n => markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) n)) radius ω
    (fun r v => normalizedPhi (decode ω.1) ω.2 r m v) (markedPotential ms ω) ?_ ?_
  · intro r v
    show phi (decode ω.1) ω.2 m v - phi (decode ω.1) ω.2 m r
      = gatedApproximant m ω v.val - gatedApproximant m ω r.val
    rw [phi_eq_gatedApproximant hG v, phi_eq_gatedApproximant hG r]
  · intro v
    rfl

/-- **Clause 2: the rooted specific energy of every stage is almost surely measurable.** -/
theorem aemeasurable_rootedSpecificEnergyDensity_phi (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    AEMeasurable (fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0) (ν.prod gridLaw) := by
  refine (measurable_rootedSpecificEnergyDensity (E := (Prod.fst : MarkedEnvironment → Env))
    measurable_fst (Ψ := fun ω n => gatedApproximant m ω n)
    (fun n => hmeas m n)).aemeasurable.congr ?_
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE)] with ω hG
  show rootedSpecificEnergyDensity (decode ω.1)
      (fun v : Vertex ω.1.val => gatedApproximant m ω v.val) 0
    = rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0
  rw [gatedApproximant_field_eq (m := m) hG]

/-- **Clause 3: the rooted specific gradient errors are almost surely measurable.** -/
theorem aemeasurable_markedSpecificGradientError (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    AEMeasurable (markedSpecificGradientError ms m) (ν.prod gridLaw) := by
  refine (measurable_rootedSpecificEnergyDensity (E := (Prod.fst : MarkedEnvironment → Env))
    measurable_fst
    (Ψ := fun ω n => gatedApproximant m ω n - markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) n))
    (fun n => (hmeas m n).sub (measurable_markedPotentialLabel ms hmeas n))).aemeasurable.congr ?_
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE)] with ω hG
  have hEq : (fun v : Vertex ω.1.val => gatedApproximant m ω v.val -
        markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val))
      = fun v : Vertex ω.1.val => phi (decode ω.1) ω.2 m v - markedPotential ms ω v := by
    funext v
    rw [phi_eq_gatedApproximant hG v]
    rfl
  show rootedSpecificEnergyDensity (decode ω.1)
      (fun v : Vertex ω.1.val => gatedApproximant m ω v.val -
        markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val)) 0
    = rootedSpecificEnergyDensity (decode ω.1)
        (fun v : Vertex ω.1.val => phi (decode ω.1) ω.2 m v - markedPotential ms ω v) 0
  rw [hEq]

/-- **Clause 4: the rooted specific energy of the marked limit is measurable.**  This one
needs neither the good event nor any hypothesis on the law. -/
theorem measurable_rootedSpecificEnergyDensity_markedPotential (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0 :=
  measurable_rootedSpecificEnergyDensity (E := (Prod.fst : MarkedEnvironment → Env))
    measurable_fst
    (Ψ := fun ω n => markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) n))
    (measurable_markedPotentialLabel ms hmeas)

/-- **The open input `hdens` of the harmonic-coordinate assembly, discharged.**

All four clauses of `HarmonicCoordinateAssembly.MarkedDensityMeasurability` follow from the
manuscript's own mass-transport hypothesis, its finite (FE) moment, and the measurability
input `hmeas` of the assembly.  Mass transport and the moment are used only through
`ae_mem_sublinearEvent`, to identify the gated interpolants with the concrete `phi`. -/
theorem markedDensityMeasurability_of_massTransport (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    MarkedDensityMeasurability ν ms :=
  ⟨fun radius m => aemeasurable_markedGraphNeighborhoodError ν hν hFE ms hmeas radius m,
    fun m => aemeasurable_rootedSpecificEnergyDensity_phi ν hν hFE hmeas m,
    fun m => aemeasurable_markedSpecificGradientError ν hν hFE ms hmeas m,
    (measurable_rootedSpecificEnergyDensity_markedPotential ms hmeas).aemeasurable⟩

/-! ### The assembly's reduction with `hdens` removed -/

/-- **The harmonic-coordinate reduction with the density-measurability input discharged.**
The remaining **nine** inputs of
`HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs` are unchanged and
remain open; this is an implication, not a proof of the harmonic-coordinate theorem. -/
theorem harmonicCoordinateConclusions_of_nine_inputs (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariant ms)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hharm : MarkedHarmonicity ν ms) (hsub : MarkedCentroidSublinearity ν ms)
    (hnbr : MarkedNeighborhoodConvergence ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    HarmonicCoordinateConclusions ν :=
  harmonicCoordinateConclusions_of_named_inputs ν hν hFE ms hms hmeas hcov hcopies hconv hpatch
    hharm hsub (markedDensityMeasurability_of_massTransport ν hν hFE.ne ms hmeas) hnbr hspec

end ReflectedGMS.MarkedDensityMeasurabilityProducer
