/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StagePairingBlockOwnership at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PairingOwnershipInstance
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchLabelMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootedBracketMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableSelectedAtIndex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedProjectionProducers
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageFieldCovariance

/-!
# The pairing ownership datum with a *cover-or-vanish* gate, and its two measurability inputs

`Corrector/PairingOwnershipInstance.activePairingOwnership` needs
`hcover : ∀ ω, SelectionCoversOn (decode (R.env ω)) (R.grid ω) m` at **every** configuration in
order to *construct* the `PairingOwnership` datum, and
`Corrector/TransportAeGating` records that this is the one thing it could not gate.  On the
actual marked space `Env × Grid` that hypothesis is false at a general `ω`
(`Corrector/StagePairingSkeletonData` proves it only on `SublinearEvent`), and the recorded
remedy was to re-instantiate the whole transport chain on the good subtype.

**That re-instantiation is unnecessary.**  `hcover` enters the construction through exactly one
step, `PairingOwnershipInstance.coeff_eq_zero_of_no_active_owner`, which concludes that the
signed coefficient `c(e) ⟪ΔΨ, ΔH⟫` vanishes on an unowned edge.  Where the *variation* `H`
vanishes identically that conclusion is free.  So the cover hypothesis may be relaxed to

  `∀ ω, ¬ SelectionCoversOn … → ∀ v, H ω v = 0`,

which is satisfied by every field that is **gated by the good event**, and in particular by
`MarkedStageFieldCovariance.stageDifferenceField` (both stage fields are `0` off
`SublinearEvent`, by `HarmonicCoordinateAssembly.gatedApproximant_of_notMem`).

## What is proved

* `gatedPairingOwnership` — the ownership datum in cover-or-vanish form, for an arbitrary
  `MarkedReRooting`.  Its owner is the canonical `PairingOwnershipInstance.labelOwner`, by
  `rfl` (`gatedPairingOwnership_owner`).
* `ownedByOriginBlock_subset_range_of_owner`, `pairCoeff_labelPair_eq_zero_of_notMem_of_owner`,
  `summable_indicator_ownedByOriginBlock_of_energies`,
  `tsum_indicator_ownedByOriginBlock_eq_zero_of_orthogonality` — the block data `hsum`/`hzero`
  of `Corrector/TransportAeGating.integral_rootedPairingDensity_eq_zero_ae` for **any**
  ownership datum whose owner is `labelOwner`; the corresponding results of
  `PairingOwnershipInstance` are stated only for `activePairingOwnership` and are therefore
  unusable here.  The orthogonality form takes the bare block pairing `⟪Ψ, H⟫_{G_S} = 0`.
* `measurableSet_labelOwner_eq_some` — the open input `howner` of
  `Corrector/PairingTransportWeld`: the `some c` fibre of the owner label is the `ActiveEdge`
  event, a Boolean combination of the selection event
  (`MeasurableSelectedAtIndex.measurableSet_selected`), the conductance slot, and the patch and
  boundary label events of `Corrector/PatchLabelMeasurability`.
* `measurable_pairCoeff_of_labels` — the open input `hcoeff` of the same weld, for any two
  label-indexed fields.

## What is **not** proved

Nothing here concludes any transport identity, and no main theorem is proved.  The block-local
energies feeding `summable_indicator_ownedByOriginBlock_of_energies` and the block orthogonality
feeding `tsum_indicator_ownedByOriginBlock_eq_zero_of_orthogonality` are visible hypotheses.
-/

-- Merged from `ReflectedGMS/Corrector/StagePairingSkeletonData.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_StagePairingSkeletonData

/-!
# The two structural data of the pairing ownership, on the good event

`Corrector/TransportAeGating` records, as the one thing it could **not** gate, that
`PairingOwnershipInstance.activePairingOwnership` needs its two structural hypotheses at every
`ω`, because they are used to *construct* the `PairingOwnership` datum rather than to prove
something about it:

> `hcover` (a `SelectionCovers` hypothesis) and `hH` at every `ω` … Gating those two is a
> separate piece of work.

and `Corrector/NestedProjectionProducers` says of `SelectionCoversOn` that it

> is **not** proved here; it is strictly weaker than, and says nothing about, the pinning
> conclusion below.

**Both are available on the good event, and the covering statement is not an open input at
all.**

* `SelectionCoversOn (decode e) D m` for `m > 0` is *verbatim* the conclusion of the checked
  `Spatial/NonmacroscopicSelectedBlocks.exists_selected_mem`, whose hypotheses are
  `Geometry` (free, `Code.decode_geometry`), `SublinearDiameterDecay (decode e)` — which is
  the *definition* of `HarmonicCoordinateAssembly.SublinearEvent` — and, since the covering
  clause of `Geometry` was weakened to `μH[1] (uncoveredSet F) = 0`, that the point be covered.
  So `hcover` holds at every point of the good subtype `SublinearEvent × Grid`, with no new
  mathematics.  This corrects the recorded "not proved here": the producer exists, one
  `Spatial/` module away.
* `hH` — the pinning `s:eq:pinnested` for the *nested* pair — follows on the same event from
  `NestedProjectionProducers.skeleton_subset_skeleton_of_le` (which consumes exactly the
  covering statement above) together with the pinning clause of
  `DyadicApproximation.IsBlockInterpolation`.

## Consequence for the architecture

The pairing weld
(`Corrector/PairingTransportWeld.integral_rootedPairingDensity_eq_zero_of_massTransport`) must
therefore be instantiated on the **good subtype** `Spatial/GoodMarkedSpace.goodSet × Grid`
(where `goodSet ⊆ SublinearEvent`), not on `Env × Grid`: on the good subtype `hcover` is a
theorem, and `hH` costs only the existence of block interpolants.  This is the same move the
project already made for `OriginChainRegular` in `Spatial/GoodMarkedSpace`.

## What is **not** proved

The existence of block interpolants `∃ f, IsBlockInterpolation (decode e) D k f`, which is the
separately staffed `hmeas`-lane atom (per-square Dirichlet solvability); it is a visible
hypothesis of `phi_eq_cellCentroid_on_skeleton` and
`stageDifferenceField_eq_zero_on_skeleton`.  This file proves no main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StagePairingSkeletonData

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open NestedProjectionProducers NonmacroscopicSelectedBlocks MarkedStageFieldCovariance

/-! ### The covering statement on the good event -/

/-- **`SelectionCoversOn` is the good event.**  Every **covered** point of the plane lies in a
square selected at any positive parameter, as soon as the environment has sublinear diameter
decay — i.e. as soon as `e ∈ SublinearEvent`.  Nothing else is used: `Geometry` is free at a
decoded environment.

The restriction to covered points is the manuscript's own (§3.1) and is not removable: the
covering clause of `Geometry` only asks `μH[1] (uncoveredSet F) = 0`, and the block index of a
square is controlled only through the cells its patch meets, so no square through an uncovered
point need ever be selected. -/
theorem selectionCoversOn_of_mem_sublinearEvent {e : Env} (he : e ∈ SublinearEvent) (D : Grid)
    {m : ℝ} (hm : 0 < m) : SelectionCoversOn (decode e) D m := fun z hz =>
  exists_selected_mem (decode e) (decode_geometry e) D ((mem_sublinearEvent_iff e).1 he) m hm
    z hz

/-! ### The nested pinning `s:eq:pinnested` on the good event -/

/-- **`hmin` for the later stage, on the good event.**  The block interpolant of stage `n` is
the centroid-trace minimizer of every square selected at parameter `n`; this is the hypothesis
`hmin` of the pairing weld, read at the selected origin block. -/
theorem centroidTraceMinimizer_phi {e : Env} (D : Grid) {n : ℕ} (hn : n ≠ 0)
    (hne : ∃ f, IsBlockInterpolation (decode e) D n f)
    {t : SquareIndex} (ht : Selected (decode e) D (n : ℝ) t) :
    CentroidTraceMinimizer (decode e) (square D t) (phi (decode e) D n) :=
  centroidTraceMinimizer_of_isBlockInterpolation (decode e) D hn
    (phi_spec_of_exists (decode e) D n hne) ht

end ReflectedGMS.StagePairingSkeletonData

end Merged_StagePairingSkeletonData

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StagePairingBlockOwnership

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open EnvironmentLaws ActiveBlockEdges NestedProjectionProducers
open OwnedFieldPairingTransport PairingOwnershipInstance
open PatchLabelMeasurability MeasurableSelectedAtIndex HarmonicCoordinateAssembly
open ActualMarkedBlockTransport

/-! ### Measurability of the owner label on `Env × Grid` -/

/-- **The `some c` fibre of the owner label is the active-edge event, hence measurable.**  This
is the hypothesis `howner` of
`Corrector/PairingTransportWeld.integral_rootedPairingDensity_eq_zero_of_massTransport`. -/
theorem measurableSet_labelOwner_eq_some (m : ℝ) (q : ℕ × ℕ) (c : SquareIndex) :
    MeasurableSet {ω : Env × Grid | labelOwner actualReRooting m ω q = some c} := by
  obtain ⟨a, b⟩ := q
  have hEq : {ω : Env × Grid | labelOwner actualReRooting m ω (a, b) = some c}
      = ((((({ω : Env × Grid | (ω.1.val.1 a).isSome} ∩ {ω | (ω.1.val.1 b).isSome}) ∩
          {ω | Selected (decode ω.1) ω.2 m c}) ∩ {ω | 0 < ω.1.val.2 a b}) ∩
          patchLabelEvent c a) ∩ patchLabelEvent c b) ∩
        (boundaryLabelEvent c a ∩ boundaryLabelEvent c b)ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · intro h
      by_cases ha : (ω.1.val.1 a).isSome
      · by_cases hb : (ω.1.val.1 b).isSome
        · rw [labelOwner_pair actualReRooting m ω a b ha hb] at h
          obtain ⟨hsel, hadj, hpa, hpb, hnb⟩ :=
            activeEdge_of_activeOwner_eq_some (decode ω.1) ω.2 m h
          have hadj' : 0 < ω.1.val.2 a b := hadj
          refine ⟨⟨⟨⟨⟨⟨ha, hb⟩, hsel⟩, hadj'⟩, (mem_patchLabelEvent_iff ha).2 hpa⟩,
            (mem_patchLabelEvent_iff hb).2 hpb⟩, ?_⟩
          rintro ⟨hba, hbb⟩
          exact hnb ⟨(mem_boundaryLabelEvent_iff ha).1 hba, (mem_boundaryLabelEvent_iff hb).1 hbb⟩
        · rw [labelOwner_eq_none_of_snd actualReRooting m ω a hb] at h
          exact absurd h (by simp)
      · rw [labelOwner_eq_none_of_fst actualReRooting m ω ha b] at h
        exact absurd h (by simp)
    · rintro ⟨⟨⟨⟨⟨⟨ha, hb⟩, hsel⟩, hadj⟩, hpa⟩, hpb⟩, hnb⟩
      rw [labelOwner_pair actualReRooting m ω a b ha hb]
      have hadj' : (decode ω.1).graph.toSimpleGraph.Adj ⟨a, ha⟩ ⟨b, hb⟩ := hadj
      refine activeOwner_eq_some_of_activeEdge (decode ω.1) (decode_geometry ω.1).1 ω.2 m
        ⟨hsel, hadj', (mem_patchLabelEvent_iff ha).1 hpa, (mem_patchLabelEvent_iff hb).1 hpb, ?_⟩
      rintro ⟨hba, hbb⟩
      exact hnb ⟨(mem_boundaryLabelEvent_iff ha).2 hba, (mem_boundaryLabelEvent_iff hb).2 hbb⟩
  rw [hEq]
  have h1 : MeasurableSet ((fun ω : Env × Grid => ω.1.val.1 a) ⁻¹' {o | o.isSome}) :=
    measurable_markedSlot a Spatial.measurableSet_slotIsSome
  have h2 : MeasurableSet ((fun ω : Env × Grid => ω.1.val.1 b) ⁻¹' {o | o.isSome}) :=
    measurable_markedSlot b Spatial.measurableSet_slotIsSome
  have h3 : MeasurableSet {ω : Env × Grid | 0 < ω.1.val.2 a b} :=
    measurableSet_lt measurable_const
      ((RootedFiniteEnergyDensityMeasurable.measurable_conductance_env a b).comp measurable_fst)
  exact (((((h1.inter h2).inter (measurableSet_selected m c)).inter h3).inter
    (measurableSet_patchLabelEvent c a)).inter (measurableSet_patchLabelEvent c b)).inter
    ((measurableSet_boundaryLabelEvent c a).inter (measurableSet_boundaryLabelEvent c b)).compl

/-! ### Measurability of the signed pairing coefficient -/

/-- The signed pairing coefficient of two label-indexed fields, written as an indicator. -/
theorem pairCoeff_eq_indicator {Ω : Type*} (E : Ω → Env) (LΨ LH : Ω → ℕ → Plane) (a b : ℕ)
    (ω : Ω) :
    pairCoeff (E ω) (fun v => LΨ ω v.val) (fun v => LH ω v.val) (a, b)
      = Set.indicator {ω : Ω | ((E ω).val.1 a).isSome ∧ ((E ω).val.1 b).isSome}
          (fun ω => (E ω).val.2 a b * inner ℝ (LΨ ω b - LΨ ω a) (LH ω b - LH ω a)) ω := by
  by_cases ha : ((E ω).val.1 a).isSome
  · by_cases hb : ((E ω).val.1 b).isSome
    · have hmem : ω ∈ {ω : Ω | ((E ω).val.1 a).isSome ∧ ((E ω).val.1 b).isSome} := ⟨ha, hb⟩
      rw [Set.indicator_of_mem hmem]
      exact pairCoeffAt_of_isSome (E ω) _ _ ha hb
    · have hmem : ω ∉ {ω : Ω | ((E ω).val.1 a).isSome ∧ ((E ω).val.1 b).isSome} :=
        fun h => hb h.2
      rw [Set.indicator_of_notMem hmem]
      exact pairCoeffAt_of_not_isSome_right (E ω) _ _ a hb
  · have hmem : ω ∉ {ω : Ω | ((E ω).val.1 a).isSome ∧ ((E ω).val.1 b).isSome} :=
      fun h => ha h.1
    rw [Set.indicator_of_notMem hmem]
    exact pairCoeffAt_of_not_isSome_left (E ω) _ _ ha b

/-- **The signed pairing coefficient of two label-indexed fields is measurable.**  This is the
hypothesis `hcoeff` of `Corrector/PairingTransportWeld`. -/
theorem measurable_pairCoeff_of_labels {Ω : Type*} [MeasurableSpace Ω] {E : Ω → Env}
    (hE : Measurable E) {LΨ LH : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω => LΨ ω n)
    (hH : ∀ n : ℕ, Measurable fun ω => LH ω n) (q : ℕ × ℕ) :
    Measurable fun ω : Ω =>
      pairCoeff (E ω) (fun v => LΨ ω v.val) (fun v => LH ω v.val) q := by
  obtain ⟨a, b⟩ := q
  have hEq : (fun ω : Ω => pairCoeff (E ω) (fun v => LΨ ω v.val) (fun v => LH ω v.val) (a, b))
      = Set.indicator {ω : Ω | ((E ω).val.1 a).isSome ∧ ((E ω).val.1 b).isSome}
          (fun ω => (E ω).val.2 a b * inner ℝ (LΨ ω b - LΨ ω a) (LH ω b - LH ω a)) :=
    funext fun ω => pairCoeff_eq_indicator E LΨ LH a b ω
  rw [hEq]
  have hset : MeasurableSet {ω : Ω | ((E ω).val.1 a).isSome ∧ ((E ω).val.1 b).isSome} := by
    have h1 : MeasurableSet ((fun ω : Ω => (E ω).val.1 a) ⁻¹' {o | o.isSome}) :=
      ((RootedBracketMeasurability.measurable_slot a).comp hE) Spatial.measurableSet_slotIsSome
    have h2 : MeasurableSet ((fun ω : Ω => (E ω).val.1 b) ⁻¹' {o | o.isSome}) :=
      ((RootedBracketMeasurability.measurable_slot b).comp hE) Spatial.measurableSet_slotIsSome
    exact h1.inter h2
  refine Measurable.indicator ?_ hset
  have hc : Measurable fun ω : Ω => (E ω).val.2 a b :=
    (RootedFiniteEnergyDensityMeasurable.measurable_conductance_env a b).comp hE
  have hΨab : Measurable fun ω : Ω => LΨ ω b - LΨ ω a := (hΨ b).sub (hΨ a)
  have hHab : Measurable fun ω : Ω => LH ω b - LH ω a := (hH b).sub (hH a)
  have hinner : Measurable fun ω : Ω => inner ℝ (LΨ ω b - LΨ ω a) (LH ω b - LH ω a) :=
    Measurable.inner hΨab hHab
  exact hc.mul hinner

/-! ### The ownership datum with a cover-or-vanish hypothesis -/

section Gated

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The ownership datum of the signed pairing coefficient, cover-or-vanish form.**  The owner
of an edge is the unique selected square of which it is an active edge; the variation vanishes
on the skeleton, and wherever the selected squares fail to cover the plane the variation
vanishes identically.  This is `PairingOwnershipInstance.activePairingOwnership` with the
pathwise cover hypothesis relaxed to a gate on the variation, which is what a field gated by
the good event supplies. -/
noncomputable def gatedPairingOwnership (R : MarkedReRooting Ω) (m : ℝ)
    (Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane)
    (hcover : ∀ ω : Ω, ¬ SelectionCoversOn (decode (R.env ω)) (R.grid ω) m →
      ∀ v : Vertex (R.env ω).val, H ω v = 0)
    (hH : ∀ (ω : Ω) (v : Vertex (R.env ω).val),
      v ∈ skeleton (decode (R.env ω)) (R.grid ω) m → H ω v = 0) :
    PairingOwnership R m Ψ H where
  owner := labelOwner R m
  owner_symm := labelOwner_symm R m
  owner_selected := by
    intro ω p s h
    obtain ⟨a, b⟩ := p
    by_cases ha : ((R.env ω).val.1 a).isSome
    · by_cases hb : ((R.env ω).val.1 b).isSome
      · rw [labelOwner_pair R m ω a b ha hb] at h
        exact (activeEdge_of_activeOwner_eq_some (decode (R.env ω)) (R.grid ω) m h).1
      · rw [labelOwner_eq_none_of_snd R m ω a hb] at h
        exact absurd h (by simp)
    · rw [labelOwner_eq_none_of_fst R m ω ha b] at h
      exact absurd h (by simp)
  pairCoeff_eq_zero_of_owner_eq_none := by
    intro ω p h
    obtain ⟨a, b⟩ := p
    by_cases ha : ((R.env ω).val.1 a).isSome
    · by_cases hb : ((R.env ω).val.1 b).isSome
      · rw [labelOwner_pair R m ω a b ha hb] at h
        have hval : pairCoeff (R.env ω) (Ψ ω) (H ω) (a, b)
            = (decode (R.env ω)).graph.c ⟨a, ha⟩ ⟨b, hb⟩ *
              inner ℝ (Ψ ω ⟨b, hb⟩ - Ψ ω ⟨a, ha⟩) (H ω ⟨b, hb⟩ - H ω ⟨a, ha⟩) :=
          pairCoeffAt_of_isSome (R.env ω) (Ψ ω) (H ω) ha hb
        rw [hval]
        by_cases hcov : SelectionCoversOn (decode (R.env ω)) (R.grid ω) m
        · exact coeff_eq_zero_of_no_active_owner (decode (R.env ω)) (decode_geometry (R.env ω))
            (R.grid ω) m hcov (hH ω)
            (not_activeEdge_of_activeOwner_eq_none (decode (R.env ω)) (R.grid ω) m h)
        · rw [hcover ω hcov, hcover ω hcov, sub_zero, inner_zero_right, mul_zero]
      · exact pairCoeffAt_of_not_isSome_right (R.env ω) (Ψ ω) (H ω) a hb
    · exact pairCoeffAt_of_not_isSome_left (R.env ω) (Ψ ω) (H ω) ha b

/-! ### The block data `hsum` and `hzero` for a canonical-owner datum -/

variable {R : MarkedReRooting Ω} {m : ℝ} {Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane}

/-- The owner block of the origin is covered by the ordered pairs of its patch vertices, for
any ownership datum whose owner is the canonical `labelOwner`. -/
theorem ownedByOriginBlock_subset_range_of_owner (O : PairingOwnership R m Ψ H)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), O.owner ω q = labelOwner R m ω q) (ω : Ω) :
    (posField O).ownedByOriginBlock ω ⊆
      Set.range (labelPair (R.env ω)
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)))) := by
  rintro ⟨a, b⟩ hp
  have h : labelOwner R m ω (a, b)
      = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := by
    rw [← hO]
    exact hp
  by_cases ha : ((R.env ω).val.1 a).isSome
  · by_cases hb : ((R.env ω).val.1 b).isSome
    · rw [labelOwner_pair R m ω a b ha hb] at h
      have hact := activeEdge_of_activeOwner_eq_some (decode (R.env ω)) (R.grid ω) m h
      exact ⟨(⟨⟨a, ha⟩, hact.2.2.1⟩, ⟨⟨b, hb⟩, hact.2.2.2.1⟩), rfl⟩
    · rw [labelOwner_eq_none_of_snd R m ω a hb] at h
      exact absurd h (by simp)
  · rw [labelOwner_eq_none_of_fst R m ω ha b] at h
    exact absurd h (by simp)

/-- A pair of patch vertices outside the owner block of the origin carries no pairing
coefficient, for any ownership datum whose owner is the canonical `labelOwner`. -/
theorem pairCoeff_labelPair_eq_zero_of_notMem_of_owner (O : PairingOwnership R m Ψ H)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), O.owner ω q = labelOwner R m ω q)
    (hH : ∀ (ω : Ω) (v : Vertex (R.env ω).val),
      v ∈ skeleton (decode (R.env ω)) (R.grid ω) m → H ω v = 0) (ω : Ω)
    (hsel : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k)
    (q : (patchVertices (decode (R.env ω))
        (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))) ×
      (patchVertices (decode (R.env ω))
        (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
    (hq : labelPair (R.env ω)
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))) q ∉
      (posField O).ownedByOriginBlock ω) :
    pairCoeff (R.env ω) (Ψ ω) (H ω)
      (labelPair (R.env ω)
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))) q) = 0 := by
  have hblock : Selected (decode (R.env ω)) (R.grid ω) m
      (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := originSelected_blockLevel hsel
  have hlab : labelOwner R m ω (q.1.1.1, q.2.1.1)
      = activeOwner (decode (R.env ω)) (R.grid ω) m (q.1.1, q.2.1) :=
    labelOwner_pair R m ω q.1.1.1 q.2.1.1 q.1.1.2 q.2.1.2
  have hne : activeOwner (decode (R.env ω)) (R.grid ω) m (q.1.1, q.2.1)
      ≠ some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := by
    intro hcon
    refine hq ?_
    show O.owner ω (q.1.1.1, q.2.1.1) = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)
    rw [hO, hlab]
    exact hcon
  have hna : ¬ ActiveEdge (decode (R.env ω)) (R.grid ω) m
      (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) (q.1.1, q.2.1) := fun hcon =>
    hne (activeOwner_eq_some_of_activeEdge (decode (R.env ω))
      (decode_geometry (R.env ω)).1 (R.grid ω) m hcon)
  have hval : pairCoeff (R.env ω) (Ψ ω) (H ω) (q.1.1.1, q.2.1.1)
      = (decode (R.env ω)).graph.c q.1.1 q.2.1 *
        inner ℝ (Ψ ω q.2.1 - Ψ ω q.1.1) (H ω q.2.1 - H ω q.1.1) :=
    pairCoeff_vertex (R.env ω) (Ψ ω) (H ω) q.1.1 q.2.1
  show pairCoeff (R.env ω) (Ψ ω) (H ω) (q.1.1.1, q.2.1.1) = 0
  rw [hval]
  exact coeff_eq_zero_of_not_activeEdge (decode (R.env ω)) (R.grid ω) m (hH ω) hblock
    q.1.2 q.2.2 hna

/-- **`hsum` from the two block-local energies**, for any ownership datum with the canonical
owner. -/
theorem summable_indicator_ownedByOriginBlock_of_energies (O : PairingOwnership R m Ψ H)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), O.owner ω q = labelOwner R m ω q)
    (hH : ∀ (ω : Ω) (v : Vertex (R.env ω).val),
      v ∈ skeleton (decode (R.env ω)) (R.grid ω) m → H ω v = 0) (ω : Ω)
    (hsel : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k)
    (hΨE : vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => Ψ ω v.1) < ∞)
    (hHE : vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => H ω v.1) < ∞) :
    Summable fun p : ℕ × ℕ =>
      ((posField O).ownedByOriginBlock ω).indicator (pairCoeff (R.env ω) (Ψ ω) (H ω)) p := by
  refine summable_indicator_of_injective (injective_labelPair (R.env ω) _)
    (ownedByOriginBlock_subset_range_of_owner O hO ω)
    (fun q hq => pairCoeff_labelPair_eq_zero_of_notMem_of_owner O hO hH ω hsel q hq) ?_
  refine Summable.congr (summable_vectorGradProd _ hΨE hHE) fun q => ?_
  exact (pairCoeff_labelPair R Ψ H ω _ q).symm

/-- **`hzero` from a block orthogonality**: the signed pairing coefficient sums to zero on the
owner block of the origin as soon as `Ψ` and `H` are energy-orthogonal on the patch graph of
that block. -/
theorem tsum_indicator_ownedByOriginBlock_eq_zero_of_orthogonality
    (O : PairingOwnership R m Ψ H)
    (hO : ∀ (ω : Ω) (q : ℕ × ℕ), O.owner ω q = labelOwner R m ω q)
    (hH : ∀ (ω : Ω) (v : Vertex (R.env ω).val),
      v ∈ skeleton (decode (R.env ω)) (R.grid ω) m → H ω v = 0) (ω : Ω)
    (hsel : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k)
    (hΨE : vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => Ψ ω v.1) < ∞)
    (hHE : vectorEnergy (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => H ω v.1) < ∞)
    (horth : vectorPairing (restrictGraph (decode (R.env ω)).graph
        (patchVertices (decode (R.env ω))
          (square (R.grid ω) (blockSquareIndex (decode (R.env ω)) (R.grid ω) m))))
        (fun v => Ψ ω v.1) (fun v => H ω v.1) = 0) :
    (∑' p : ℕ × ℕ,
      ((posField O).ownedByOriginBlock ω).indicator (pairCoeff (R.env ω) (Ψ ω) (H ω)) p) = 0 := by
  rw [tsum_indicator_of_injective (injective_labelPair (R.env ω) _)
    (ownedByOriginBlock_subset_range_of_owner O hO ω)
    (fun q hq => pairCoeff_labelPair_eq_zero_of_notMem_of_owner O hO hH ω hsel q hq)]
  rw [tsum_congr fun q => pairCoeff_labelPair R Ψ H ω _ q,
    tsum_vectorGradProd_eq_two_mul_vectorPairing _ hΨE hHE, horth, mul_zero]

end Gated

end ReflectedGMS.StagePairingBlockOwnership
