/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.QuenchedFormulation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainStatement
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds

/-!
# Quenched formulation of the reflected spatial conclusions

Manuscript label `r:cor:quenched`: *conditional on almost every environment, the
reflected walk from each starting cell satisfies `r:eq:localbounded` and never
hits an end at spatial infinity*.

The manuscript proof is the countability passage: the deterministic theorem is
applied on the probability-one set where its assumptions hold, and "there are
only countably many possible starting cells in each environment".  This file
performs exactly that passage over the existing
`ReflectedGMS.InvarianceMainStatement` vocabulary.  The starting cells of a coded
environment `e` are `Code.Vertex e.val = {n : ℕ // (e.val.1 n).isSome}`, a
subtype of `ℕ`, so the per-start almost-sure statements are indexed by the fixed
countable type `ℕ` and `MeasureTheory.ae_all_iff` applies uniformly in `e`.  No
measurability of the conclusion event is needed: the `ae` filter has the
countable intersection property because a countable union of null sets is null,
and null sets are defined by the outer measure, not by measurability.

## What is proved

`ae_forall_start_quenchedWalkConclusion` is manuscript `r:cor:quenched` itself, over the
canonical constructed exponential-area-clock reflected walk.  Its conclusion clauses are
exactly the two named in the corollary: `r:eq:localbounded`, i.e.
`sup {|z_{X_t}| : 0 ≤ t ≤ T, X_t ∈ 𝓗} < ∞` simultaneously for all finite `T`, and the
existence of a unique end-labelled lift of the path which never takes an end at spatial
infinity.  Its hypotheses are exactly the corollary's own: the hypotheses of Theorem
`r:thm:main` hold almost surely with environment-dependent `C` and `R_*` (the predicate
`hcut`, whose shape is literally the conclusion of the checked producer
`Spatial/AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses`), a measurable labelling of
the cells by representatives, and conditional reflected-walk laws given the environment for
an admissible clock (`EnvironmentWalkData`).  No open conclusion predicate occurs in the
statement or in the proof.  `ae_quenchedWalkConclusion_of_massTransport`
then discharges `hcut` from mass transport, the manuscript's finite (FE) moment and the
almost-sure ball bound on the rooted (FE) density.

## What is *not* proved

The predicate `QuenchedSpatialConclusion` below is a strictly stronger *packaging* form: it
additionally demands a càdlàg pathwise spatial extension `Z` of the end-labelled path, with
`Z` continuous at every end-valued time.  That extra clause is not part of manuscript
`r:cor:quenched` — `r:eq:localbounded` constrains `|z_{X_t}|` at vertex times only — and the
construction of such an extension is an open obligation elsewhere in the project (see
`Forms/SpatialInfinityAvoidance.lean`).  The theorems below that produce
`QuenchedSpatialConclusion` are therefore still genuine implications from the open predicate
`FixedStartConclusions`, and are labelled as such in their docstrings; they supply the
quenched packaging only.
-/
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.QuenchedFormulation
open Code EnvironmentFields EnvironmentLaws StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement

/-- The start-free part of `InvarianceMainStatement.EnvironmentProcessConclusions`:
the actual reflected-walk properties of the canonical construction for one
environment, one exhaustion and one connectivity witness.  These clauses are
copied verbatim from `EnvironmentProcessConclusions`; separating them is what
allows the exhaustion to be chosen once per environment and then used for every
starting cell. -/
def EnvironmentWalkData (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) : Prop :=
  ∃ hmin : (decode e).graph.EnergyMinimizer,
    (∀ v, 0 < areaRate (decode e) v) ∧
    IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))) ∧
    IsReflectedWalk (decode e).graph (D.rateFunction hG) hmin
      (Existence.processFamily D hG (D.rateFunction hG))

/-- `EnvironmentProcessConclusions` is exactly the environment-level walk data
together with the fixed-start conclusions for every starting cell, with the same
exhaustion and connectivity witness shared by all starts. -/
theorem environmentProcessConclusions_iff (e : Env) (Φ : CellField)
    (target : AnisotropicBrownianTarget) :
    EnvironmentProcessConclusions e Φ target ↔
      ∃ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∃ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG ∧
            ∀ start : Vertex e.val, FixedStartConclusions e D hG Φ target start := by
  constructor
  · rintro ⟨hnt, D, hG, hmin, hrate, hw₁, hw₂, hstart⟩
    exact ⟨hnt, D, hG, ⟨hmin, hrate, hw₁, hw₂⟩, hstart⟩
  · rintro ⟨hnt, D, hG, ⟨hmin, hrate, hw₁, hw₂⟩, hstart⟩
    exact ⟨hnt, D, hG, hmin, hrate, hw₁, hw₂, hstart⟩

/-- The countability passage of the manuscript proof, in the exact dependent
form needed here: the starting cells of a coded environment form a subtype of
`ℕ`, so an almost-sure statement for each label index gives one almost-sure
event on which the statement holds simultaneously at every actual vertex.
The exceptional set is a countable union of null sets; no measurability of the
individual events is required. -/
theorem ae_forall_vertex {ν : Measure Env} {p : (e : Env) → Vertex e.val → Prop}
    (h : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome, p e ⟨n, hn⟩) :
    ∀ᵐ e ∂ν, ∀ v : Vertex e.val, p e v := by
  have h' : ∀ᵐ e ∂ν, ∀ n : ℕ, ∀ hn : (e.val.1 n).isSome, p e ⟨n, hn⟩ :=
    ae_all_iff.2 h
  filter_upwards [h'] with e he v
  exact he v.1 v.2

/-- **The deterministic theorem applied inside one environment, at one starting cell.**
For the canonical constructed reflected walk with any admissible rate `w`, the logarithmic
cutoff hypothesis tuple `hr₀, hC, ho, hD, hW` of manuscript Proposition `r:prop:log` gives
both conclusions of Theorem `r:thm:main` almost surely.

This is exactly the pair of checked theorems
`LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime` and
`LogCutoffSpatialBoundedness.reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity_of_logCutoff`,
specialized to `F = decode e`, the representative rule `z.at e`, and the canonical process
family `Existence.processFamily D hG w`; nothing else is used. -/
theorem walkConclusion_of_logCutoff_hypotheses (e : Env) [Nontrivial (Vertex e.val)]
    (z : CellField) (hz : IsCellRepresentative z)
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    {w : Vertex e.val → ℝ} {hmin : (decode e).graph.EnergyMinimizer}
    (hPF : IsReflectedWalk (decode e).graph w hmin (Existence.processFamily D hG w))
    (hw : ∀ v, 0 < w v) (start : Vertex e.val)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) (ho : ‖z.at e start‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
      Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN (decode e)
          {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
        ≤ ENNReal.ofReal (C * R ^ 2)) :
    ∀ᵐ ω ∂(Existence.sampleLaw D hG start),
      (∀ T : ℝ≥0, ∃ M : ℝ, ∀ t : ℝ≥0, t ≤ T → ∀ v : Vertex e.val,
        Existence.process D w t ω = some v → ‖z.at e v‖ ≤ M) ∧
      (∃! Y : ℝ≥0 → State (decode e),
        (∀ t, collapse (Y t) = Existence.process D w t ω) ∧
        IsEndLabeling (decode e) Y ∧ AvoidsSpatialInfinity (decode e) Y) := by
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    (decode e) (decode_geometry e) (z.at e) (hz e)
    (Existence.processFamily D hG w) hPF hw start hr₀ hC ho hD hW
  have hend :=
    LogCutoffSpatialBoundedness.reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity_of_logCutoff
      (decode e) (decode_geometry e) (z.at e) (hz e)
      (Existence.processFamily D hG w) hPF hw start hr₀ hC ho hD hW
  exact hbdd.and hend

/-- **Conditional quenched wrapper.**  From the environment-level walk data holding almost
surely, together with the fixed-start conclusions holding almost surely for each
individual starting label, one gets a single probability-one set of environments
on which the conclusions hold simultaneously for *every* starting cell.

The exhaustion, the connectivity witness and the walk data are quantified inside
the per-label hypothesis, so the start-free data selected on the left is the same
data used at every start; this is what makes the interchange of `∀ start` and
`∀ᵐ e` legitimate. -/
theorem ae_environmentProcessConclusions_of_ae_fixedStartConclusions
    {ν : Measure Env} {Φ : CellField} {target : AnisotropicBrownianTarget}
    (hdata : ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG)
    (hstart : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
            FixedStartConclusions e D hG Φ target ⟨n, hn⟩) :
    ∀ᵐ e ∂ν, EnvironmentProcessConclusions e Φ target := by
  have hall := ae_forall_vertex (ν := ν)
    (p := fun e v => ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → FixedStartConclusions e D hG Φ target v) hstart
  filter_upwards [hdata, hall] with e hd hv
  obtain ⟨hnt, D, hG, hdat⟩ := hd
  exact (environmentProcessConclusions_iff e Φ target).2
    ⟨hnt, D, hG, hdat, fun start => hv start hnt D hG hdat⟩

end ReflectedGMS.QuenchedFormulation
