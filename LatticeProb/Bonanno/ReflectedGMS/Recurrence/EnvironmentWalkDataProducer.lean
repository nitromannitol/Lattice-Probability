/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.EnvironmentWalkDataProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.QuenchedFormulation
import LatticeProb.Bonanno.ReflectedGMS.Forms.CanonicalFastFormProcess
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalRelabel
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import LatticeProb.Bonanno.ReflectedWalk.Proposition13

/-!
# The `hdata` input of the reflected invariance assembly, reduced to one clock clause

`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs` carries as its
input `hdata` the clause

> almost surely, the canonical construction is a reflected walk for both the area
> clock and the admissible fast clock,

i.e. `∀ᵐ e ∂ν, ∃ hnt, ∃ D hG, QuenchedFormulation.EnvironmentWalkData e D hG`.
This file discharges **every** part of that clause except one, and states the
remainder as a named clock property of the area clock.

## What is proved here, unconditionally

* `infinite_of_geometry` / `nontrivial_vertex` — a coded environment has infinitely
  many cells, hence `Nontrivial (Vertex e.val)`.  The cells are compact and cover a
  dense subset of the plane, which is not compact, so there cannot be finitely many of
  them.  This
  removes the `hnt` existential of `hdata` from the list of assumptions.
* `decode_connected` — the cell graph of *every* `e : Env` is connected; this is a
  field of `Code.decode_geometry`, so the `hG` existential of `hdata` is free too.
* `areaRate_pos` — the area exit rate `π(v)/a(v)` is positive at every cell:
  `π(v) > 0` by connectivity (`pi_pos_of_connected`) and `a(v) > 0` because the cell
  is compact with nonempty interior (`StatementIngredients.cellArea_pos`).
* `energyMinimizer` — the `EnergyMinimizer` existential of `EnvironmentWalkData`
  is discharged from Proposition 1.3 (`ConductanceGraph.energyMin` and its three
  characterising lemmas) at the connectivity witness above.
* the **admissible fast clock** conjunct of `EnvironmentWalkData`, i.e.
  `IsReflectedWalk G (D.rateFunction hG) hmin (Existence.processFamily D hG
  (D.rateFunction hG))`, is `Forms.canonical_isReflectedWalk_of_rate_le` at
  `w = D.rateFunction hG`, where the domination hypothesis is `le_refl`.

## The one residual input

The **area clock** conjunct of `EnvironmentWalkData` is the only part that is not
discharged.  Through `ReflectedWalk.Existence.isReflectedWalk` and the
unconditional `ReflectedWalk.Existence.markovProperty` it needs exactly the
manuscript's (3.16) for `w = areaRate`, and through
`IndexSet.holdingTimesSummable_of` together with the unconditional level-`0`
divergence `Exhaustion.jointLaw_ae_tsum_holding_addr_zero_eq_top` (which holds for
*every* positive rate) it needs exactly the finiteness half of (3.16):

`AreaClockReachesLevelZeroIndices` — for every starting cell, almost surely every
level-`0` index `[(0,K)]` is reached in **finite area time**.

This is the manuscript's local finiteness of the area clock, and it is *not* a
restatement of any conclusion of the main theorem: it is the pathwise statement
that the area clock does not blow up before a fixed index of the coupled chain.
Lemma 3.5 (`Exhaustion.rateFunction_ae_holdingTimesSummable`) is unavailable for it,
because that lemma needs `areaRate ≥ D.rateFunction hG` off a finite set, which no
environment hypothesis supplies; the honest route is the occupation-integral
identity with `Process.AreaClockLocalFiniteness.areaClock_finite_on_compact_times`,
which is *not* performed here.

Every theorem below that depends on the residual carries it as an explicit
hypothesis, so nothing here asserts `hdata`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.EnvironmentWalkDataProducer

open Code EnvironmentFields StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet QuenchedFormulation

/-! ## The unconditional structural clauses -/

/-- Compact cells covering all but an `H¹`-null set force infinitely many cells: a finite
union of compact sets is compact, hence closed, and a closed set containing the dense
complement of the uncovered set is the whole plane, which is not compact. -/
theorem infinite_of_geometry {V : Type*} [Countable V] (F : IndexedCells V)
    (hF : Geometry F) : Infinite V := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have hcompact : IsCompact (⋃ v, (F.cell v : Set Plane)) :=
    isCompact_iUnion fun v => (F.cell v).isCompact
  have hsub : (Set.univ : Set Plane) ⊆ ⋃ v, (F.cell v : Set Plane) := by
    refine subset_of_isClosed_of_inter_compl_subset hF isOpen_univ hcompact.isClosed ?_
    rintro z ⟨-, hz⟩
    exact Set.mem_iUnion.mpr (exists_mem_cell_of_notMem_uncoveredSet hz)
  have hcover : (⋃ v, (F.cell v : Set Plane)) = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) hsub
  rw [hcover] at hcompact
  exact (noncompactSpace_of_neBot (by infer_instance)).1 hcompact

/-- The cell graph of every coded environment is connected: a clause of `Geometry`,
which `Code.decode_geometry` supplies for every `e : Env`. -/
theorem decode_connected (e : Env) : (decode e).graph.toSimpleGraph.Connected :=
  Geometry.graph_connected (decode_geometry e)

/-- Every coded environment has at least two cells. -/
theorem nontrivial_vertex (e : Env) : Nontrivial (Vertex e.val) := by
  have : Infinite (Vertex e.val) := infinite_of_geometry (decode e) (decode_geometry e)
  infer_instance

/-- The area exit rate `π(v)/a(v)` is positive at every cell. -/
theorem areaRate_pos (e : Env) [Nontrivial (Vertex e.val)] (v : Vertex e.val) :
    0 < areaRate (decode e) v :=
  div_pos ((decode e).graph.pi_pos_of_connected (decode_connected e) v)
    (StatementIngredients.cellArea_pos (decode e) (decode_geometry e) v)

/-- The energy-minimising extension of Proposition 1.3, packaged as the
`EnergyMinimizer` record that `IsReflectedWalk` takes. -/
noncomputable def energyMinimizer (e : Env) : (decode e).graph.EnergyMinimizer where
  toFun := (decode e).graph.energyMin (decode_connected e)
  eqOn := fun {_} hA φ => (decode e).graph.energyMin_eqOn (decode_connected e) hA φ
  hasFiniteEnergy := fun {_} hA φ =>
    (decode e).graph.energyMin_hasFiniteEnergy (decode_connected e) hA φ
  le_energy := fun {_} hA φ {_} hf hfA =>
    (decode e).graph.energyMin_le_energy (decode_connected e) hA φ hf hfA

/-- The admissible fast clock half of `EnvironmentWalkData`, unconditionally. -/
theorem isReflectedWalk_fastClock (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) :
    IsReflectedWalk (decode e).graph (D.rateFunction hG) (energyMinimizer e)
      (Existence.processFamily D hG (D.rateFunction hG)) :=
  canonical_isReflectedWalk_of_rate_le D hG (energyMinimizer e)
    (D.rateFunction hG) (D.rateFunction_pos hG) fun _ => le_refl _

/-! ## The residual area-clock clause -/

/-- **The one open input of `hdata`**: local finiteness of the area clock along the
coupled chains.  For every starting cell, almost surely the area time `τ` elapsed
before the level-`0` index `[(0,K)]` is finite, for every `K`.  This is the
finiteness half of the manuscript's (3.16) for `w = areaRate`; its divergence half
holds for every positive rate and is discharged below. -/
def AreaClockReachesLevelZeroIndices (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) : Prop :=
  ∀ z : Vertex e.val, ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
    tau (D.levelSets (D.nz z)) ω.1 (areaRate (decode e)) ω.2
      (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤

/-- (3.16) for the area clock, from the residual clause.  The level-`0` divergence
`∑ₖ T_{[(0,k)]} = ∞` is `Exhaustion.jointLaw_ae_tsum_holding_addr_zero_eq_top`, which
needs only positivity of the rate; the layer form of the finiteness half is
`IndexSet.tau_addr_zero_lt_top_iff`. -/
theorem areaClock_holdingTimesSummable (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate (decode e)) ω.2 := by
  filter_upwards [D.jointLaw_ae_consistent hG (D.nz z) z,
    D.jointLaw_ae_tsum_holding_addr_zero_eq_top hG (D.nz z) (D.mem_Gsub_nz z)
      (areaRate (decode e)) (areaRate_pos e), h3 z] with p hcons h0 hτ
  refine holdingTimesSummable_of _ _ _ _ hcons (D.levelSets_mono (D.nz z))
    (D.exists_mem_levelSets (D.nz z)) h0 fun K => ?_
  exact (tau_addr_zero_lt_top_iff _ _ _ _ hcons (D.levelSets_mono (D.nz z))
    (D.exists_mem_levelSets (D.nz z)) K).mp (hτ K)

/-- The area clock half of `EnvironmentWalkData`, conditional on the residual clause.
Property (iv), the Markov property, is `Existence.markovProperty`, which is
unconditional for every positive rate satisfying (3.16). -/
theorem isReflectedWalk_areaClock (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) :
    IsReflectedWalk (decode e).graph (areaRate (decode e)) (energyMinimizer e)
      (Existence.processFamily D hG (areaRate (decode e))) :=
  Existence.isReflectedWalk D hG (areaRate (decode e)) (areaRate_pos e)
    (energyMinimizer e) (areaClock_holdingTimesSummable e D hG h3)
    (Existence.markovProperty D hG (areaRate (decode e)) (areaRate_pos e)
      (areaClock_holdingTimesSummable e D hG h3))

/-- **`EnvironmentWalkData` for one environment**, conditional only on
`AreaClockReachesLevelZeroIndices`. -/
theorem environmentWalkData_of_areaClockReachesLevelZeroIndices (e : Env)
    [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) :
    EnvironmentWalkData e D hG :=
  ⟨energyMinimizer e, areaRate_pos e, isReflectedWalk_areaClock e D hG h3,
    isReflectedWalk_fastClock e D hG⟩

/-! ## The almost-sure form: the `hdata` input of the invariance assembly -/

/-- The environment-level residual: some exhaustion for which the area clock reaches
every level-`0` index in finite time.  Existence of an exhaustion by itself is free
(`ReflectedWalk.Existence.exists_exhaustion` at the connectivity witness
`decode_connected`); the content is the clock clause. -/
def EnvironmentAreaClockAdmissible (e : Env) : Prop :=
  letI := nontrivial_vertex e
  ∃ D : (decode e).graph.Exhaustion,
    AreaClockReachesLevelZeroIndices e D (decode_connected e)

/-- **The `hdata` input of `InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`,
reduced.**  The statement of the conclusion is copied verbatim from that theorem.  This
is an implication: `hadm` is open, and nothing here certifies it. -/
theorem ae_environmentWalkData_of_ae_areaClockAdmissible (ν : Measure Env)
    (hadm : ∀ᵐ e ∂ν, EnvironmentAreaClockAdmissible e) :
    ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG := by
  filter_upwards [hadm] with e he
  letI := nontrivial_vertex e
  obtain ⟨D, hD⟩ := he
  exact ⟨nontrivial_vertex e, D, decode_connected e,
    environmentWalkData_of_areaClockReachesLevelZeroIndices e D (decode_connected e) hD⟩

end ReflectedGMS.EnvironmentWalkDataProducer
