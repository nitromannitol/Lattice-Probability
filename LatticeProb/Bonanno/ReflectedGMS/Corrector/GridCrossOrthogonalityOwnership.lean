/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GridCrossOrthogonalityOwnership at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GridCrossOrthogonalityTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.OwnedFieldLabelTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchLabelMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableSelectedAtIndex
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodMarkedSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# The signed pairing transport on the coupled two-grid space

`Corrector/GridCrossOrthogonalityTransport` supplies `s:eq:redistribute` on the coupled space
`Env × Grid × Grid` for the re-rooting `coupledReRooting` (block grid = first copy).  This module
supplies everything the signed pairing transport of the `s:prop:projection` lane
(`Corrector/OwnedFieldPairingTransport`, `Corrector/PairingOwnershipInstance`,
`Corrector/TransportAeGating`) needs on top of it, and welds them:

* `selectionCoversOn_of_mem_goodSet` — **the closed selected squares cover every covered point**
  on the good set, at every grid and every positive parameter.  Nothing in the tree produced
  `NestedProjectionProducers.SelectionCoversOn` before; it is the re-rooted origin-block existence
  of `GoodMarkedSpace.originChainRegularOn_goodMarked` pulled back through the square reindexing
  `SelectedSquareSimilarity.squareMap 1 z`.
* `measurableSet_labelOwner_eq_some` — **the owner label is measurable** on `Env × Grid`, and its
  coupled lift.  The active-edge owner is a `Classical.choose`, but its `some c` fibre is the
  `ActiveEdge` event, a Boolean combination of the selection event
  (`MeasurableSelectedAtIndex.measurableSet_selected`), the conductance slot, and the patch and
  boundary label events of `Corrector/PatchLabelMeasurability`.  This was an open input (`howner`)
  of `Corrector/PairingTransportWeld`.
* `measurable_pairCoeff_of_labels` — **the signed pairing coefficient is measurable** for any two
  label-indexed fields; the open input `hcoeff` of the same weld.
* `CoupledTransportedField`, `coupledCovariantField_posField`/`negField` — the coupled versions of
  `OwnedFieldLabelTransport.similarityCovariantField_posField`/`negField`.
* `gatedPairingOwnership` — the ownership datum with the cover hypothesis relaxed to
  *cover-or-vanish*: where the selected squares do not cover the plane the variation is required to
  vanish identically, which is how a variation gated by the good set enters.
* `tsum_indicator_ownedByOriginBlock_eq_zero_of_orthogonality` — the block sum of the signed
  coefficient vanishes from **any** block orthogonality `⟪Ψ, H⟫_{G_S} = 0`, not only from the
  centroid-trace minimality of `PairingOwnershipInstance`; this is what lets the *limiting*
  potential, whose block orthogonality is `FullRectangleOrthogonality`, play the role of `Ψ`.
* `integral_rootedPairingDensity_eq_zero_coupled` — **the weld**: the expected rooted pairing
  density on the coupled law vanishes, from `EnvironmentLaws.MassTransport ν` and almost-sure
  block data.

**This file proves no main theorem.**  Every statement below is either structural or an
implication with visible hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GridCrossOrthogonalityOwnership

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open EnvironmentLaws DyadicGridLaw DyadicGridTranslation UniformGridDilationInvariance
open ActualMarkedBlockTransport MarkedMassTransportProducer
open GridIndependenceCoupling CopyDifferenceDensitySimilarity
open ActiveBlockEdges NestedProjectionProducers PairingOwnershipInstance
open OwnedFieldPairingTransport OwnedFieldLabelTransport LabelBijectionProducer
open SelectedSquareSimilarity SpecificEnergyDensitySimilarity
open GridCrossOrthogonalityTransport GoodMarkedSpace GoodEnvironmentSet
open PatchLabelMeasurability MeasurableSelectedAtIndex HarmonicCoordinateAssembly

/-! ### The selected squares cover the covered points on the good set -/

/-- **`SelectionCoversOn` on the good set.**  For a good environment, every grid and every
positive parameter, every **covered** point of the plane lies in a closed selected square:
re-root at the point, take the selected origin block there
(`originChainRegularOn_goodMarked`), and pull it back through the unit-scale square
reindexing.

The re-rooted configuration lands in the invariant domain `coveredMarked` exactly because `z`
is covered: re-rooting at `z` moves `z` to the origin, so `(0 : Plane) ∉ uncoveredSet (decode
(translateEnv z e))` is `z ∉ uncoveredSet (decode e)`.  This is the manuscript's §3.1
statement, *"their closures cover every point belonging to a cell"*, and no claim is made at an
uncovered point. -/
theorem selectionCoversOn_of_mem_goodSet {e : Env} (he : e ∈ goodSet) (D : Grid) {m : ℝ}
    (hm : 0 < m) : SelectionCoversOn (decode e) D m := by
  intro z hz
  have he' : translateEnv z e ∈ goodSet := goodSet_translateEnv z e he
  have hcm : ((⟨translateEnv z e, he'⟩ : goodSet), translate z D) ∈ coveredMarked := by
    rw [mem_coveredMarked_iff]
    show (0 : Plane) ∈ Spatial.envCoveredSet (translateEnv z e)
    rw [zero_mem_envCoveredSet_translateEnv_iff]
    by_contra hcon
    exact hz (by rw [uncoveredSet_decode]; exact hcon)
  obtain ⟨k, hk⟩ := originChainRegularOn_goodMarked.exists_originSelected'
    (ω := ((⟨translateEnv z e, he'⟩ : goodSet), translate z D)) hcm hm
  have hk' : Selected (decode (similarityTargetEnv 1 z one_pos e))
      (dilate 1 one_pos (translate z D)) m (originIndex k) := by
    rw [dilate_one]
    exact hk
  have h := isSimilarityRelabel_similarityRelabel 1 z one_pos e
  obtain ⟨c, hc⟩ := exists_squareMap_eq 1 z D (originIndex k)
  have hsel : Selected (decode e) D m c := by
    have h1 := selected_squareMap_iff h D m c
    rw [hc] at h1
    exact h1.1 hk'
  refine ⟨c, hsel, ?_⟩
  have hpre := preimage_square_squareMap one_pos z D c
  rw [hc] at hpre
  rw [← hpre]
  show positiveSimilarity 1 z z
    ∈ (square (dilate 1 one_pos (translate z D)) (originIndex k)).carrier
  have h0 : positiveSimilarity 1 z z = 0 := by simp [positiveSimilarity]
  rw [h0, dilate_one]
  exact halfOpenSquare_subset _ _ (zero_mem_halfOpenSquare_originIndex _ _)

/-- Every good environment is in the sublinear event. -/
theorem mem_sublinearEvent_of_mem_goodSet {e : Env} (he : e ∈ goodSet) : e ∈ SublinearEvent :=
  he.2

/-! ### Measurability of the owner label -/

/-- **The `some c` fibre of the owner label is the active-edge event.** -/
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

/-- The coupled owner label is the one-grid owner label read at the block grid. -/
theorem labelOwner_coupledReRooting (m : ℝ) (p : CoupledSpace) (q : ℕ × ℕ) :
    labelOwner coupledReRooting m p q = labelOwner actualReRooting m (p.1, p.2.1) q := rfl

/-- The projection of the coupled space onto the environment and the block grid. -/
def blockMarked (p : CoupledSpace) : Env × Grid := (p.1, p.2.1)

theorem measurable_blockMarked : Measurable blockMarked :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

/-- **The coupled owner label is measurable.** -/
theorem measurableSet_labelOwner_coupled_eq_some (m : ℝ) (q : ℕ × ℕ) (c : SquareIndex) :
    MeasurableSet {p : CoupledSpace | labelOwner coupledReRooting m p q = some c} := by
  have hEq : {p : CoupledSpace | labelOwner coupledReRooting m p q = some c}
      = blockMarked ⁻¹' {ω : Env × Grid | labelOwner actualReRooting m ω q = some c} := rfl
  rw [hEq]
  exact measurable_blockMarked (measurableSet_labelOwner_eq_some m q c)

/-! ### Measurability of the signed pairing coefficient -/

/-- The signed pairing coefficient of two label-indexed fields, as an indicator. -/
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
open input `hcoeff` of `Corrector/PairingTransportWeld`, for fields given at every label. -/
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
      ((measurable_slot a).comp hE) Spatial.measurableSet_slotIsSome
    have h2 : MeasurableSet ((fun ω : Ω => (E ω).val.1 b) ⁻¹' {o | o.isSome}) :=
      ((measurable_slot b).comp hE) Spatial.measurableSet_slotIsSome
    exact h1.inter h2
  refine Measurable.indicator ?_ hset
  have hc : Measurable fun ω : Ω => (E ω).val.2 a b :=
    (RootedFiniteEnergyDensityMeasurable.measurable_conductance_env a b).comp hE
  have hΨab : Measurable fun ω : Ω => LΨ ω b - LΨ ω a := (hΨ b).sub (hΨ a)
  have hHab : Measurable fun ω : Ω => LH ω b - LH ω a := (hH b).sub (hH a)
  have hinner : Measurable fun ω : Ω => inner ℝ (LΨ ω b - LΨ ω a) (LH ω b - LH ω a) :=
    Measurable.inner hΨab hHab
  exact hc.mul hinner

/-! ### The transport datum on the coupled space -/

/-- A coupled vertex field whose increments transport along every joint similarity of the
environment and both grid copies. -/
def CoupledTransportedField (Ψ : ∀ p : CoupledSpace, Vertex p.1.val → Plane) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : CoupledSpace)
    (rel : Vertex p.1.val ≃ Vertex (coupledSimilarity s u hs p).1.val),
    IsSimilarityRelabel s u hs p.1 (coupledSimilarity s u hs p).1 rel →
      GradientTransported s rel (Ψ p) (Ψ (coupledSimilarity s u hs p))

/-- **The marked potential of the block grid transports on the coupled space.** -/
theorem coupledTransportedField_markedPotential_fst (ms : ℕ → ℕ) :
    CoupledTransportedField fun p : CoupledSpace => markedPotential ms (p.1, p.2.1) :=
  fun _ _ _ p _ h => gradientTransported_markedPotential (p := (p.1, p.2.1)) ms h

/-- **The marked potential of the passive grid transports on the coupled space.** -/
theorem coupledTransportedField_markedPotential_snd (ms : ℕ → ℕ) :
    CoupledTransportedField fun p : CoupledSpace => markedPotential ms (p.1, p.2.2) :=
  fun _ _ _ p _ h => gradientTransported_markedPotential (p := (p.1, p.2.2)) ms h

/-- **The gated stage field of the block grid transports on the coupled space.** -/
theorem coupledTransportedField_stageField_fst (m : ℕ) :
    CoupledTransportedField fun p : CoupledSpace =>
      MarkedStageFieldCovariance.stageField m (p.1, p.2.1) :=
  fun _ _ _ p _ h => MarkedStageFieldCovariance.gradientTransported_stageField (p := (p.1, p.2.1)) m h

/-! ### The coupled covariance of the two owned edge fields -/

section Covariance

variable {m : ℝ}

/-- **The owner-set clause on the coupled space**, for any owned edge field whose owner datum is
the canonical `labelOwner`. -/
theorem preimage_ownerSet_labelEquiv_coupled {s : ℝ} {u : Plane} {hs : 0 < s}
    (Q : OwnedEdgeField coupledReRooting m)
    (hQ : ∀ (p : CoupledSpace) (q : ℕ × ℕ), Q.owner p q = labelOwner coupledReRooting m p q)
    (p : CoupledSpace) (q : ℕ × ℕ) :
    positiveSimilarity s u ⁻¹' Q.ownerSet (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2)
      = Q.ownerSet p q := by
  have h := isSimilarityRelabel_similarityRelabel s u hs p.1
  have hgrid : (markedSimilarity s u hs (p.1, p.2.1)).2 = dilate s hs (translate u p.2.1) := rfl
  have hown := labelOwner_labelEquiv (hs := hs) m (p.1, p.2.1)
    (markedSimilarity s u hs (p.1, p.2.1)) h hgrid q
  have hown' : Q.owner (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2)
      = (Q.owner p q).map (squareMap s u p.2.1) := by
    rw [hQ, hQ, labelOwner_coupledReRooting, labelOwner_coupledReRooting]
    exact hown
  by_cases hnone : Q.owner p q = none
  · rw [hnone] at hown'
    have h1 : Q.owner (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2) = none := hown'
    rw [Q.ownerSet_of_eq_none h1, Q.ownerSet_of_eq_none hnone, Set.preimage_empty]
  · obtain ⟨c, hc⟩ := exists_eq_some_of_ne_none hnone
    rw [hc] at hown'
    have h1 : Q.owner (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2)
        = some (squareMap s u p.2.1 c) := hown'
    rw [Q.ownerSet_of_eq_some h1, Q.ownerSet_of_eq_some hc]
    show positiveSimilarity s u ⁻¹'
        halfOpenSquare (dilate s hs (translate u p.2.1)) (squareMap s u p.2.1 c)
      = halfOpenSquare p.2.1 c
    exact preimage_halfOpenSquare_squareMap hs u p.2.1 c

/-- **The owner-area clause on the coupled space.** -/
theorem ownerArea_labelEquiv_coupled {s : ℝ} {u : Plane} {hs : 0 < s}
    (Q : OwnedEdgeField coupledReRooting m)
    (hQ : ∀ (p : CoupledSpace) (q : ℕ × ℕ), Q.owner p q = labelOwner coupledReRooting m p q)
    (p : CoupledSpace) (q : ℕ × ℕ) :
    Q.ownerArea (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2)
      = ENNReal.ofReal (s ^ 2) * Q.ownerArea p q := by
  have h := isSimilarityRelabel_similarityRelabel s u hs p.1
  have hgrid : (markedSimilarity s u hs (p.1, p.2.1)).2 = dilate s hs (translate u p.2.1) := rfl
  have hown := labelOwner_labelEquiv (hs := hs) m (p.1, p.2.1)
    (markedSimilarity s u hs (p.1, p.2.1)) h hgrid q
  have hown' : Q.owner (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2)
      = (Q.owner p q).map (squareMap s u p.2.1) := by
    rw [hQ, hQ, labelOwner_coupledReRooting, labelOwner_coupledReRooting]
    exact hown
  by_cases hnone : Q.owner p q = none
  · rw [hnone] at hown'
    have h1 : Q.owner (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2) = none := hown'
    rw [Q.ownerArea_of_eq_none h1, Q.ownerArea_of_eq_none hnone, mul_zero]
  · obtain ⟨c, hc⟩ := exists_eq_some_of_ne_none hnone
    rw [hc] at hown'
    have h1 : Q.owner (coupledSimilarity s u hs p)
        (labelEquiv (similarityRelabel s u hs p.1) q.1,
          labelEquiv (similarityRelabel s u hs p.1) q.2)
        = some (squareMap s u p.2.1 c) := hown'
    rw [Q.ownerArea_of_eq_some h1, Q.ownerArea_of_eq_some hc]
    show ENNReal.ofReal (side (dilate s hs (translate u p.2.1)) (squareMap s u p.2.1 c).1 ^ 2)
      = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (side p.2.1 c.1 ^ 2)
    rw [side_squareMap hs u p.2.1 c, mul_pow, ENNReal.ofReal_mul (sq_nonneg s)]

variable {Ψ H : ∀ p : CoupledSpace, Vertex p.1.val → Plane}

/-- **`CoupledCovariantField` for the positive part of the signed pairing coefficient.** -/
theorem coupledCovariantField_posField (O : PairingOwnership coupledReRooting m Ψ H)
    (hO : ∀ (p : CoupledSpace) (q : ℕ × ℕ), O.owner p q = labelOwner coupledReRooting m p q)
    (hΨ : CoupledTransportedField Ψ) (hH : CoupledTransportedField H) :
    CoupledCovariantField (posField O) := by
  intro s u hs p
  have h := isSimilarityRelabel_similarityRelabel s u hs p.1
  refine ⟨labelEquiv (similarityRelabel s u hs p.1), preimage_labelCell_labelEquiv h,
    fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact ofReal_scaled (sq_nonneg s)
      (pairCoeff_labelEquiv h (hΨ s u hs p _ h) (hH s u hs p _ h) q)
  · exact preimage_ownerSet_labelEquiv_coupled (hs := hs) (posField O) hO p q
  · exact ownerArea_labelEquiv_coupled (hs := hs) (posField O) hO p q

/-- **`CoupledCovariantField` for the negative part.** -/
theorem coupledCovariantField_negField (O : PairingOwnership coupledReRooting m Ψ H)
    (hO : ∀ (p : CoupledSpace) (q : ℕ × ℕ), O.owner p q = labelOwner coupledReRooting m p q)
    (hΨ : CoupledTransportedField Ψ) (hH : CoupledTransportedField H) :
    CoupledCovariantField (negField O) := by
  intro s u hs p
  have h := isSimilarityRelabel_similarityRelabel s u hs p.1
  refine ⟨labelEquiv (similarityRelabel s u hs p.1), preimage_labelCell_labelEquiv h,
    fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact ofReal_neg_scaled (sq_nonneg s)
      (pairCoeff_labelEquiv h (hΨ s u hs p _ h) (hH s u hs p _ h) q)
  · exact preimage_ownerSet_labelEquiv_coupled (hs := hs) (negField O) hO p q
  · exact ownerArea_labelEquiv_coupled (hs := hs) (negField O) hO p q

end Covariance

/-! ### The ownership datum with a cover-or-vanish hypothesis -/

section Gated

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The ownership datum of the signed pairing coefficient, cover-or-vanish form.**  The owner of
an edge is the unique selected square of which it is an active edge; the variation vanishes on the
skeleton, and wherever the selected squares fail to cover the plane the variation vanishes
identically.  This is `PairingOwnershipInstance.activePairingOwnership` with the pathwise cover
hypothesis relaxed to a gate on the variation. -/
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

/-! ### The block sum of the signed coefficient, from any block orthogonality -/

variable {R : MarkedReRooting Ω} {m : ℝ} {Ψ H : ∀ ω : Ω, Vertex (R.env ω).val → Plane}

/-- The owner block of the origin is covered by the ordered pairs of its patch vertices, for any
ownership datum whose owner is the canonical `labelOwner`. -/
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
owner block of the origin as soon as `Ψ` and `H` are energy-orthogonal on the patch graph of that
block.  Compared with `PairingOwnershipInstance.tsum_indicator_ownedByOriginBlock_eq_zero`, the
centroid-trace minimality of `Ψ` is replaced by the bare orthogonality, which is what the
*limiting* potential satisfies (`FullRectangleOrthogonality`). -/
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

/-! ### The weld: the signed pairing transport on the coupled law -/

/-- **The expected rooted pairing density vanishes on the coupled law**, for any two coupled
transported fields with a canonical-owner ownership datum, from `EnvironmentLaws.MassTransport ν`
and almost-sure block data.  This is
`Corrector/TransportAeGating.integral_rootedPairingDensity_eq_zero_ae` on the coupled space with
the two single-kernel mass-transport identities discharged from `s:eq:MTP`. -/
theorem integral_rootedPairingDensity_eq_zero_coupled (m : ℝ)
    (Ψ H : ∀ p : CoupledSpace, Vertex p.1.val → Plane)
    (O : PairingOwnership coupledReRooting m Ψ H)
    (hO : ∀ (p : CoupledSpace) (q : ℕ × ℕ), O.owner p q = labelOwner coupledReRooting m p q)
    (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hΨt : CoupledTransportedField Ψ) (hHt : CoupledTransportedField H)
    (hcoeff : ∀ q : ℕ × ℕ, Measurable fun p : CoupledSpace => pairCoeff p.1 (Ψ p) (H p) q)
    (hsel : ∀ᵐ p ∂(ν.prod (gridMeasure.prod gridMeasure)),
      ∃ k : ℤ, OriginSelected (decode p.1) p.2.1 m k)
    (hpfin : (∫⁻ p, (posField O).rootEndpointDensity p
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞)
    (hmfin : (∫⁻ p, (negField O).rootEndpointDensity p
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞)
    (hsum : ∀ᵐ p ∂(ν.prod (gridMeasure.prod gridMeasure)), Summable fun q : ℕ × ℕ =>
      ((posField O).ownedByOriginBlock p).indicator (pairCoeff p.1 (Ψ p) (H p)) q)
    (hzero : ∀ᵐ p ∂(ν.prod (gridMeasure.prod gridMeasure)), (∑' q : ℕ × ℕ,
      ((posField O).ownedByOriginBlock p).indicator (pairCoeff p.1 (Ψ p) (H p)) q) = 0)
    (hbdry : ∀ᵐ p ∂(ν.prod (gridMeasure.prod gridMeasure)),
      (0 : Plane) ∉ RootDensities.boundaryMask (decode p.1)) :
    (∫ p, SpecificEnergyPolarization.rootedPairingDensity (decode p.1) (Ψ p) (H p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
  have hwp : ∀ q : ℕ × ℕ, Measurable fun p : CoupledSpace => (posField O).weight p q :=
    fun q => (hcoeff q).ennreal_ofReal
  have hwm : ∀ q : ℕ × ℕ, Measurable fun p : CoupledSpace => (negField O).weight p q :=
    fun q => (hcoeff q).neg.ennreal_ofReal
  have how : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {p : CoupledSpace | (posField O).owner p q = some c} := by
    intro q c
    have hEq : {p : CoupledSpace | (posField O).owner p q = some c}
        = {p : CoupledSpace | labelOwner coupledReRooting m p q = some c} := by
      ext p
      show O.owner p q = some c ↔ labelOwner coupledReRooting m p q = some c
      rw [hO]
    rw [hEq]
    exact measurableSet_labelOwner_coupled_eq_some m q c
  have how' : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {p : CoupledSpace | (negField O).owner p q = some c} := how
  exact TransportAeGating.integral_rootedPairingDensity_eq_zero_ae O
    (coupledMassTransport_endpointSpreadTransport (posField O) ν hν hwp how
      (coupledCovariantField_posField O hO hΨt hHt))
    (coupledMassTransport_endpointSpreadTransport (negField O) ν hν hwm how'
      (coupledCovariantField_negField O hO hΨt hHt))
    measurable_coupledEnv hcoeff hsel hpfin hmfin hsum hzero hbdry

end ReflectedGMS.GridCrossOrthogonalityOwnership
