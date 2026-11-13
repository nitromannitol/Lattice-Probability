/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MeasurableEndpointTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyRedistribution

/-!
# Joint measurability of the endpoint-spread to owner-block transport

`ReflectedGMS.Corrector.SpecificEnergyRedistribution` proves the manuscript
lemma "Redistribution over blocks" (`s:lem:redistribution`) for the actual
transport

`T(ω, w, z) = ∑_e (q_e/2)(1_{w ∈ H}/a_H + 1_{w ∈ H'}/a_{H'}) 1_{z ∈ S_e}/ℓ(S_e)²`

of an `OwnedEdgeField`, but leaves two hypotheses of its final identity
`lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity` undischarged: the
*joint* measurability `hmeas` of the kernel on `Ω × Plane × Plane`, and the
covariance `ReRootingCovariant`.  This module discharges the first one outright
and reduces the second to label-level data.

Nothing here assumes the transport, or any of its integrals, measurable.  The
inputs are the structural ones:

* `henv`/`hgrid`: the environment and dyadic-grid observables of the marked
  re-rooting are measurable — the same two hypotheses already used by
  `ReflectedGMS.Spatial.MarkedBlockAveraging`;
* `hweight`: each ordered-pair coefficient `ω ↦ q_e(ω)` is measurable;
* `howner`: each *selected ownership* event `{ω | S_e(ω) = s}` is measurable.

The route is:

* the label cell of a raw slot is the slot's compact cell (`slotCellSet`,
  `labelCell_eq_slotCellSet`), so the already checked joint measurability of
  cell interiors and cell volumes on the Hausdorff-Borel space of compact cells
  (`ReflectedGMS.Spatial.measurableSet_cellInterior`,
  `ReflectedGMS.Spatial.measurable_cellVolume`) transfers to the label cells and
  gives the joint measurability `measurable_spread_uncurry` of the endpoint
  factor `1_{w ∈ int H_n}/a_{H_n}`;
* the owner-block factor is handled by decomposing over the *countable* set of
  square indices: `measurableSet_ownerSetGraph` writes the graph of the owner
  block as a countable union over `s` of `{ω | S_e = s}` intersected with the
  half-open-square graph, and `ownerArea_eq_tsum` writes the owner area as a
  countable sum of indicators, each measurable because the grid coordinates are
  (`measurable_squareLower`, `measurable_squareUpper`, `measurable_gridSide`);
* `measurable_endpointSpreadTransport` then follows from
  `Measurable.ennreal_tsum` over the countable index `ℕ × ℕ`, preserving the
  `q_e/2` convention of the manuscript kernel verbatim.

Two further results are proved:

* `measurable_rootEndpointDensity` — the manuscript endpoint density
  `(2 a_{H_0})⁻¹ ∑_{e ∋ H_0} q_e` is measurable in `ω`.  This is one of the
  `AEMeasurable` inputs of the *signed* redistribution
  `SpecificEnergyRedistribution.integral_signedRootDensity_eq_integral_signedOwnerDensity`,
  and its proof (`rootEndpointDensity_eq_tsum`) uses that at most one cell
  interior contains the origin, so the boundary convention of the density is
  preserved exactly;
* `reRootingCovariant_of_ownerReRooting` — the kernel covariance
  `OwnedEdgeField.ReRootingCovariant`, which is stated in terms of the *sets*
  `ownerSet` and the areas `ownerArea`, follows from the label-level equivariance
  `OwnerReRooting`: a relabelling `σ` of the raw labels together with a
  reindexing `τ` of the selected squares under which the owner label, the
  coefficient, the cells and the half-open squares are equivariant.  This is the
  actual ownership half of the covariance; the equivariance of the environment
  and grid laws themselves remains the producer dependency and is *not* claimed
  here.

Combining, `lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_structural`
is the redistribution identity whose only remaining inputs are the mass-transport
identity for the single kernel `Q.endpointSpreadTransport`, the label-level
equivariance, and the origin-selection hypothesis.  It does **not** take the
whole-class predicate `SpecificEnergyRedistribution.MarkedMassTransport`, which
is strictly stronger than the manuscript's `s:eq:MTP`; see the audit note on that
definition and the unconditional producer
`MarkedMassTransportProducer.markedMassTransport_of_massTransport`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.MeasurableEndpointTransport

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution
open SpecificEnergyRedistribution.OwnedEdgeField

/-- The lattice indices of the dyadic squares form a countable type. -/
instance countable_squareIndex : Countable SquareIndex :=
  inferInstanceAs (Countable (ℤ × (Fin 2 → ℤ)))

/-! ### Coordinates of the plane and of the dyadic grid

These are the minimal measurability facts about `DyadicApproximation.Grid`
needed below.  `ReflectedGMS.Spatial.MeasurableSelectedBlocks` carries the same
facts, but that module is not currently compiled, and in any case only states
the half-open-square graph for the *origin* indices `originIndex k`, while the
owner block of an edge is an arbitrary selected index. -/

theorem measurable_ofLp : Measurable (WithLp.ofLp : Plane → (Fin 2 → ℝ)) :=
  (PiLp.volume_preserving_ofLp (Fin 2)).measurable

theorem measurable_planeCoord (i : Fin 2) : Measurable fun z : Plane => z i :=
  (measurable_pi_apply i).comp measurable_ofLp

theorem measurable_gridData : Measurable fun D : Grid => (D.phase, D.origin, D.digit) :=
  measurable_iff_comap_le.2 le_rfl

theorem measurable_gridPhase : Measurable fun D : Grid => D.phase :=
  measurable_fst.comp measurable_gridData

theorem measurable_gridOrigin (k : ℤ) (i : Fin 2) : Measurable fun D : Grid => D.origin k i :=
  (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
    (measurable_fst.comp (measurable_snd.comp measurable_gridData)))

theorem measurable_gridSide (k : ℤ) : Measurable fun D : Grid => side D k := by
  show Measurable fun D : Grid => (2 : ℝ) ^ (D.phase + (k : ℝ))
  exact ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).measurable).comp
    (measurable_gridPhase.add_const _)

theorem measurable_squareLower (s : SquareIndex) (i : Fin 2) :
    Measurable fun D : Grid => (square D s).lower i := by
  show Measurable fun D : Grid => D.origin s.1 i + side D s.1 * (s.2 i : ℝ)
  exact (measurable_gridOrigin s.1 i).add ((measurable_gridSide s.1).mul_const _)

theorem measurable_squareUpper (s : SquareIndex) (i : Fin 2) :
    Measurable fun D : Grid => (square D s).upper i := by
  show Measurable fun D : Grid =>
    D.origin s.1 i + side D s.1 * (s.2 i : ℝ) + side D s.1
  exact ((measurable_gridOrigin s.1 i).add
    ((measurable_gridSide s.1).mul_const _)).add (measurable_gridSide s.1)

/-- **The graph of a half-open dyadic square is jointly measurable**, for an
arbitrary lattice index and an arbitrary measurable grid observable. -/
theorem measurableSet_halfOpenSquareGraph {α : Type*} [MeasurableSpace α] {G : α → Grid}
    (hG : Measurable G) (s : SquareIndex) :
    MeasurableSet {x : α × Plane | x.2 ∈ halfOpenSquare (G x.1) s} := by
  have hEq : {x : α × Plane | x.2 ∈ halfOpenSquare (G x.1) s}
      = ⋂ i : Fin 2, ({x : α × Plane | (square (G x.1) s).lower i ≤ x.2 i} ∩
          {x : α × Plane | x.2 i < (square (G x.1) s).upper i}) := by
    ext x
    constructor
    · intro hx
      exact mem_iInter.2 fun i => ⟨(hx i).1, (hx i).2⟩
    · intro hx i
      exact ⟨(mem_iInter.1 hx i).1, (mem_iInter.1 hx i).2⟩
  rw [hEq]
  refine MeasurableSet.iInter fun i => ?_
  have hlow : Measurable fun x : α × Plane => (square (G x.1) s).lower i :=
    (measurable_squareLower s i).comp (hG.comp measurable_fst)
  have hupp : Measurable fun x : α × Plane => (square (G x.1) s).upper i :=
    (measurable_squareUpper s i).comp (hG.comp measurable_fst)
  have hz : Measurable fun x : α × Plane => x.2 i :=
    (measurable_planeCoord i).comp measurable_snd
  exact (measurableSet_le hlow hz).inter (measurableSet_lt hz hupp)

/-! ### The cell of a raw code slot

`SpecificEnergyRedistribution.labelCell` is the cell carried by a raw label.
Identifying it with the cell of the corresponding code *slot* transfers the
already checked joint measurability of compact-cell interiors and volumes. -/

/-- The plane set carried by a code slot: the slot's cell when present, and the
empty set otherwise. -/
noncomputable def slotCellSet (o : Option CompactCell) : Set Plane :=
  if o.isSome then ((o.getD Spatial.referenceCell : CompactCell) : Set Plane) else ∅

theorem slotCellSet_of_isSome {o : Option CompactCell} (h : o.isSome) :
    slotCellSet o = ((o.getD Spatial.referenceCell : CompactCell) : Set Plane) := if_pos h

theorem slotCellSet_of_not_isSome {o : Option CompactCell} (h : ¬ o.isSome) :
    slotCellSet o = ∅ := if_neg h

theorem option_get_eq_getD (o : Option CompactCell) (h : o.isSome) :
    o.get h = o.getD Spatial.referenceCell := by
  cases o with
  | none => simp at h
  | some K => rfl

/-- The cell of a raw label is the cell of its code slot. -/
theorem labelCell_eq_slotCellSet (e : Env) (n : ℕ) :
    labelCell e n = slotCellSet (e.val.1 n) := by
  by_cases h : (e.val.1 n).isSome
  · rw [labelCell_of_isSome e h]
    show (((e.val.1 n).get h : CompactCell) : Set Plane) = slotCellSet (e.val.1 n)
    rw [slotCellSet_of_isSome h, option_get_eq_getD (e.val.1 n) h]
  · rw [labelCell_of_not_isSome e h, slotCellSet_of_not_isSome h]

theorem measurableSet_slotCellInteriorGraph :
    MeasurableSet {q : Option CompactCell × Plane | q.2 ∈ interior (slotCellSet q.1)} := by
  have hEq : {q : Option CompactCell × Plane | q.2 ∈ interior (slotCellSet q.1)}
      = {q : Option CompactCell × Plane | q.1.isSome} ∩
        {q : Option CompactCell × Plane |
          q.2 ∈ interior ((q.1.getD Spatial.referenceCell : CompactCell) : Set Plane)} := by
    ext q
    constructor
    · intro hq
      replace hq : q.2 ∈ interior (slotCellSet q.1) := hq
      by_cases h : q.1.isSome
      · refine ⟨h, ?_⟩
        rwa [slotCellSet_of_isSome h] at hq
      · rw [slotCellSet_of_not_isSome h, interior_empty] at hq
        exact absurd hq (Set.notMem_empty _)
    · rintro ⟨h, hq⟩
      show q.2 ∈ interior (slotCellSet q.1)
      rw [slotCellSet_of_isSome h]
      exact hq
  rw [hEq]
  refine MeasurableSet.inter ?_ ?_
  · exact measurable_fst Spatial.measurableSet_slotIsSome
  · exact ((Spatial.measurable_slotCell.comp measurable_fst).prodMk measurable_snd)
      Spatial.measurableSet_cellInterior

theorem measurable_slotCellVolume :
    Measurable fun o : Option CompactCell => volume (slotCellSet o) := by
  have hEq : (fun o : Option CompactCell => volume (slotCellSet o))
      = Set.indicator {o : Option CompactCell | o.isSome}
          (fun o : Option CompactCell =>
            volume ((o.getD Spatial.referenceCell : CompactCell) : Set Plane)) := by
    funext o
    by_cases h : o.isSome
    · rw [slotCellSet_of_isSome h,
        Set.indicator_of_mem (show o ∈ {o : Option CompactCell | o.isSome} from h)]
    · rw [slotCellSet_of_not_isSome h, measure_empty,
        Set.indicator_of_notMem (show o ∉ {o : Option CompactCell | o.isSome} from h)]
  rw [hEq]
  exact (Spatial.measurable_cellVolume.comp Spatial.measurable_slotCell).indicator
    Spatial.measurableSet_slotIsSome

/-! ### The endpoint factor of a marked configuration -/

variable {Ω : Type*} [MeasurableSpace Ω] {R : MarkedReRooting Ω} {m : ℝ}

theorem measurable_envSlot (henv : Measurable R.env) (n : ℕ) :
    Measurable fun ω : Ω => (R.env ω).val.1 n :=
  ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)).comp henv

/-- **The label cells have a jointly measurable interior graph.** -/
theorem measurableSet_labelCellInteriorGraph (henv : Measurable R.env) (n : ℕ) :
    MeasurableSet {x : Ω × Plane | x.2 ∈ interior (labelCell (R.env x.1) n)} := by
  have hmap : Measurable fun x : Ω × Plane => ((R.env x.1).val.1 n, x.2) :=
    ((measurable_envSlot henv n).comp measurable_fst).prodMk measurable_snd
  have hEq : {x : Ω × Plane | x.2 ∈ interior (labelCell (R.env x.1) n)}
      = (fun x : Ω × Plane => ((R.env x.1).val.1 n, x.2)) ⁻¹'
        {q : Option CompactCell × Plane | q.2 ∈ interior (slotCellSet q.1)} := by
    ext x
    show x.2 ∈ interior (labelCell (R.env x.1) n)
      ↔ x.2 ∈ interior (slotCellSet ((R.env x.1).val.1 n))
    rw [labelCell_eq_slotCellSet]
  rw [hEq]
  exact hmap measurableSet_slotCellInteriorGraph

/-- **The cell areas `a_{H_n}` are measurable.** -/
theorem measurable_labelCellVolume (henv : Measurable R.env) (n : ℕ) :
    Measurable fun ω : Ω => volume (labelCell (R.env ω) n) := by
  have hEq : (fun ω : Ω => volume (labelCell (R.env ω) n))
      = fun ω : Ω => volume (slotCellSet ((R.env ω).val.1 n)) := by
    funext ω
    rw [labelCell_eq_slotCellSet]
  rw [hEq]
  exact measurable_slotCellVolume.comp (measurable_envSlot henv n)

/-- **Joint measurability of the endpoint spread `1_{w ∈ int H_n}/a_{H_n}`.** -/
theorem measurable_spread_uncurry (henv : Measurable R.env) (n : ℕ) :
    Measurable fun x : Ω × Plane => spread (R.env x.1) n x.2 := by
  have hEq : (fun x : Ω × Plane => spread (R.env x.1) n x.2)
      = Set.indicator {x : Ω × Plane | x.2 ∈ interior (labelCell (R.env x.1) n)}
          (fun x : Ω × Plane => (volume (labelCell (R.env x.1) n))⁻¹) := by
    funext x
    show Set.indicator (interior (labelCell (R.env x.1) n))
        (fun _ => (volume (labelCell (R.env x.1) n))⁻¹) x.2
      = Set.indicator {x : Ω × Plane | x.2 ∈ interior (labelCell (R.env x.1) n)}
          (fun x : Ω × Plane => (volume (labelCell (R.env x.1) n))⁻¹) x
    by_cases h : x.2 ∈ interior (labelCell (R.env x.1) n)
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem
          (show x ∈ {x : Ω × Plane | x.2 ∈ interior (labelCell (R.env x.1) n)} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem
          (show x ∉ {x : Ω × Plane | x.2 ∈ interior (labelCell (R.env x.1) n)} from h)]
  rw [hEq]
  exact ((measurable_labelCellVolume henv n).comp measurable_fst).inv.indicator
    (measurableSet_labelCellInteriorGraph henv n)

/-! ### The owner-block factor -/

/-- **The owner block of an edge has a jointly measurable graph**, from
measurable selected ownership and a measurable grid. -/
theorem measurableSet_ownerSetGraph (Q : OwnedEdgeField R m) (hgrid : Measurable R.grid)
    (howner : ∀ (p : ℕ × ℕ) (s : SquareIndex), MeasurableSet {ω : Ω | Q.owner ω p = some s})
    (p : ℕ × ℕ) :
    MeasurableSet {x : Ω × Plane | x.2 ∈ Q.ownerSet x.1 p} := by
  have hEq : {x : Ω × Plane | x.2 ∈ Q.ownerSet x.1 p}
      = ⋃ s : SquareIndex, ({x : Ω × Plane | Q.owner x.1 p = some s} ∩
          {x : Ω × Plane | x.2 ∈ halfOpenSquare (R.grid x.1) s}) := by
    ext x
    constructor
    · intro hx
      replace hx : x.2 ∈ Q.ownerSet x.1 p := hx
      by_cases hnone : Q.owner x.1 p = none
      · rw [Q.ownerSet_of_eq_none hnone] at hx
        exact absurd hx (Set.notMem_empty _)
      · obtain ⟨s, hs⟩ := exists_eq_some_of_ne_none hnone
        refine mem_iUnion.2 ⟨s, hs, ?_⟩
        rwa [Q.ownerSet_of_eq_some hs] at hx
    · intro hx
      obtain ⟨s, hs, hmem⟩ := mem_iUnion.1 hx
      show x.2 ∈ Q.ownerSet x.1 p
      rw [Q.ownerSet_of_eq_some hs]
      exact hmem
  rw [hEq]
  refine MeasurableSet.iUnion fun s => ?_
  exact (measurable_fst (howner p s)).inter (measurableSet_halfOpenSquareGraph hgrid s)

/-- The owner area `ℓ(S_e)²` as a countable sum over lattice indices: at most one
term is nonzero, because `S_e` has at most one value. -/
theorem ownerArea_eq_tsum (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) :
    Q.ownerArea ω p = ∑' s : SquareIndex,
      {ω : Ω | Q.owner ω p = some s}.indicator
        (fun ω : Ω => ENNReal.ofReal (side (R.grid ω) s.1 ^ 2)) ω := by
  by_cases hnone : Q.owner ω p = none
  · have hz : ∀ s : SquareIndex,
        {ω : Ω | Q.owner ω p = some s}.indicator
          (fun ω : Ω => ENNReal.ofReal (side (R.grid ω) s.1 ^ 2)) ω = 0 := by
      intro s
      refine Set.indicator_of_notMem (fun hmem => ?_) _
      rw [show Q.owner ω p = some s from hmem] at hnone
      exact absurd hnone (by simp)
    rw [Q.ownerArea_of_eq_none hnone]
    simp only [hz, tsum_zero]
  · obtain ⟨s0, hs0⟩ := exists_eq_some_of_ne_none hnone
    have hsingle : (∑' s : SquareIndex,
        {ω : Ω | Q.owner ω p = some s}.indicator
          (fun ω : Ω => ENNReal.ofReal (side (R.grid ω) s.1 ^ 2)) ω)
        = {ω : Ω | Q.owner ω p = some s0}.indicator
          (fun ω : Ω => ENNReal.ofReal (side (R.grid ω) s0.1 ^ 2)) ω := by
      refine tsum_eq_single s0 fun s hs => ?_
      refine Set.indicator_of_notMem (fun hmem => ?_) _
      have hss : (some s0 : Option SquareIndex) = some s := by
        rw [← hs0]
        exact hmem
      exact hs (Option.some.inj hss).symm
    rw [Q.ownerArea_of_eq_some hs0, hsingle,
      Set.indicator_of_mem (show ω ∈ {ω : Ω | Q.owner ω p = some s0} from hs0)]

/-- **The owner area is measurable.** -/
theorem measurable_ownerArea (Q : OwnedEdgeField R m) (hgrid : Measurable R.grid)
    (howner : ∀ (p : ℕ × ℕ) (s : SquareIndex), MeasurableSet {ω : Ω | Q.owner ω p = some s})
    (p : ℕ × ℕ) : Measurable fun ω : Ω => Q.ownerArea ω p := by
  have hEq : (fun ω : Ω => Q.ownerArea ω p)
      = fun ω : Ω => ∑' s : SquareIndex,
        {ω : Ω | Q.owner ω p = some s}.indicator
          (fun ω : Ω => ENNReal.ofReal (side (R.grid ω) s.1 ^ 2)) ω :=
    funext fun ω => ownerArea_eq_tsum Q ω p
  rw [hEq]
  refine Measurable.ennreal_tsum fun s => ?_
  exact (ENNReal.measurable_ofReal.comp
    (((measurable_gridSide s.1).comp hgrid).pow_const 2)).indicator (howner p s)

/-- **Joint measurability of the owner-block factor `1_{z ∈ S_e}/ℓ(S_e)²`.** -/
theorem measurable_ownerSpread_uncurry (Q : OwnedEdgeField R m) (hgrid : Measurable R.grid)
    (howner : ∀ (p : ℕ × ℕ) (s : SquareIndex), MeasurableSet {ω : Ω | Q.owner ω p = some s})
    (p : ℕ × ℕ) : Measurable fun x : Ω × Plane => Q.ownerSpread x.1 p x.2 := by
  have hEq : (fun x : Ω × Plane => Q.ownerSpread x.1 p x.2)
      = Set.indicator {x : Ω × Plane | x.2 ∈ Q.ownerSet x.1 p}
          (fun x : Ω × Plane => (Q.ownerArea x.1 p)⁻¹) := by
    funext x
    show Set.indicator (Q.ownerSet x.1 p) (fun _ => (Q.ownerArea x.1 p)⁻¹) x.2
      = Set.indicator {x : Ω × Plane | x.2 ∈ Q.ownerSet x.1 p}
          (fun x : Ω × Plane => (Q.ownerArea x.1 p)⁻¹) x
    by_cases h : x.2 ∈ Q.ownerSet x.1 p
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show x ∈ {x : Ω × Plane | x.2 ∈ Q.ownerSet x.1 p} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show x ∉ {x : Ω × Plane | x.2 ∈ Q.ownerSet x.1 p} from h)]
  rw [hEq]
  exact ((measurable_ownerArea Q hgrid howner p).comp measurable_fst).inv.indicator
    (measurableSet_ownerSetGraph Q hgrid howner p)

/-! ### The structural measurability theorem -/

/-- **Joint measurability of the manuscript endpoint-spread transport.**  The
kernel `T(ω, w, z)` of `SpecificEnergyRedistribution.OwnedEdgeField` is
measurable on `Ω × Plane × Plane` as soon as the environment and grid
observables, the edge coefficients and the selected-ownership events are
measurable.  The transport itself is never assumed measurable, and the `q_e/2`
convention is untouched.  This is exactly the hypothesis `hmeas` of
`OwnedEdgeField.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity`. -/
theorem measurable_endpointSpreadTransport (Q : OwnedEdgeField R m)
    (henv : Measurable R.env) (hgrid : Measurable R.grid)
    (hweight : ∀ p : ℕ × ℕ, Measurable fun ω : Ω => Q.weight ω p)
    (howner : ∀ (p : ℕ × ℕ) (s : SquareIndex), MeasurableSet {ω : Ω | Q.owner ω p = some s}) :
    Measurable fun x : Ω × Plane × Plane =>
      Q.endpointSpreadTransport x.1 x.2.1 x.2.2 := by
  show Measurable fun x : Ω × Plane × Plane => ∑' p : ℕ × ℕ,
    Q.weight x.1 p / 2 * spread (R.env x.1) p.1 x.2.1 * Q.ownerSpread x.1 p x.2.2
  refine Measurable.ennreal_tsum fun p => ?_
  have h1 : Measurable fun x : Ω × Plane × Plane => Q.weight x.1 p / 2 := by
    simp only [div_eq_mul_inv]
    exact ((hweight p).comp measurable_fst).mul_const _
  have h2 : Measurable fun x : Ω × Plane × Plane => spread (R.env x.1) p.1 x.2.1 :=
    (measurable_spread_uncurry henv p.1).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h3 : Measurable fun x : Ω × Plane × Plane => Q.ownerSpread x.1 p x.2.2 :=
    (measurable_ownerSpread_uncurry Q hgrid howner p).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (h1.mul h2).mul h3

/-! ### Measurability of the endpoint density -/

/-- The endpoint density as a countable sum: at most one cell interior contains
the origin, so the sum has at most one nonzero term and the boundary convention
(the density vanishes when no cell interior contains the origin) is preserved. -/
theorem rootEndpointDensity_eq_tsum (Q : OwnedEdgeField R m) (ω : Ω) :
    Q.rootEndpointDensity ω = ∑' n : ℕ,
      {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) n)}.indicator
        (fun ω : Ω =>
          (∑' k : ℕ, Q.weight ω (n, k)) / (2 * volume (labelCell (R.env ω) n))) ω := by
  obtain ⟨o, ho⟩ : ∃ o : Option ℕ, originLabel (R.env ω) = o := ⟨_, rfl⟩
  cases o with
  | none =>
    have hr : originLabel (R.env ω) = none := ho
    have hgoal : Q.rootEndpointDensity ω = 0 := by
      unfold OwnedEdgeField.rootEndpointDensity
      rw [hr]
      rfl
    have hz : ∀ n : ℕ,
        {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) n)}.indicator
          (fun ω : Ω =>
            (∑' k : ℕ, Q.weight ω (n, k)) / (2 * volume (labelCell (R.env ω) n))) ω = 0 := by
      intro n
      refine Set.indicator_of_notMem ?_ _
      exact not_mem_interior_labelCell_of_originLabel_eq_none (R.env ω) hr n
    rw [hgoal]
    simp only [hz, tsum_zero]
  | some r =>
    have hr : originLabel (R.env ω) = some r := ho
    have hmem : (0 : Plane) ∈ interior (labelCell (R.env ω) r) :=
      mem_interior_labelCell_originLabel (R.env ω) hr
    have hgoal : Q.rootEndpointDensity ω
        = (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r)) := by
      unfold OwnedEdgeField.rootEndpointDensity
      rw [hr]
      rfl
    have hsingle : (∑' n : ℕ,
        {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) n)}.indicator
          (fun ω : Ω =>
            (∑' k : ℕ, Q.weight ω (n, k)) / (2 * volume (labelCell (R.env ω) n))) ω)
        = {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) r)}.indicator
          (fun ω : Ω =>
            (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r))) ω := by
      refine tsum_eq_single r fun n hn => ?_
      refine Set.indicator_of_notMem ?_ _
      exact fun hc => hn (eq_of_mem_interior_labelCell (R.env ω) hc hmem)
    have hval : {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) r)}.indicator
        (fun ω : Ω =>
          (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r))) ω
        = (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r)) :=
      Set.indicator_of_mem
        (show ω ∈ {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) r)} from hmem) _
    rw [hgoal, hsingle, hval]

/-- **The manuscript endpoint density is measurable.**  This is the
`AEMeasurable` input of the signed redistribution
`SpecificEnergyRedistribution.integral_signedRootDensity_eq_integral_signedOwnerDensity`
for the root density; no integrability is assumed. -/
theorem measurable_rootEndpointDensity (Q : OwnedEdgeField R m) (henv : Measurable R.env)
    (hweight : ∀ p : ℕ × ℕ, Measurable fun ω : Ω => Q.weight ω p) :
    Measurable Q.rootEndpointDensity := by
  have hEq : Q.rootEndpointDensity = fun ω : Ω => ∑' n : ℕ,
      {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) n)}.indicator
        (fun ω : Ω =>
          (∑' k : ℕ, Q.weight ω (n, k)) / (2 * volume (labelCell (R.env ω) n))) ω :=
    funext fun ω => rootEndpointDensity_eq_tsum Q ω
  rw [hEq]
  refine Measurable.ennreal_tsum fun n => ?_
  have hset : MeasurableSet {ω : Ω | (0 : Plane) ∈ interior (labelCell (R.env ω) n)} :=
    (measurable_id.prodMk (measurable_const : Measurable fun _ : Ω => (0 : Plane)))
      (measurableSet_labelCellInteriorGraph henv n)
  have hnum : Measurable fun ω : Ω => ∑' k : ℕ, Q.weight ω (n, k) :=
    Measurable.ennreal_tsum fun k => hweight (n, k)
  have hden : Measurable fun ω : Ω => (2 * volume (labelCell (R.env ω) n))⁻¹ :=
    ((measurable_labelCellVolume henv n).const_mul 2).inv
  have hfun : Measurable fun ω : Ω =>
      (∑' k : ℕ, Q.weight ω (n, k)) / (2 * volume (labelCell (R.env ω) n)) := by
    simp only [div_eq_mul_inv]
    exact hnum.mul hden
  exact hfun.indicator hset

/-! ### The ownership half of the kernel covariance -/

/-! ### The redistribution identity from structural inputs -/

end ReflectedGMS.MeasurableEndpointTransport
