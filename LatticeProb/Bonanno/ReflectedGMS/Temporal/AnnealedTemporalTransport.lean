/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.AnnealedTemporalTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BaseSpecificEnergy

/-!
# The spatial transport built from a conditional temporal transport (`p:eq:spacefromtime`)

This file formalises the **annealed** half of the manuscript lemma
`p:lem:timeMTP` ("Temporal mass transport"), namely the step of its proof that
converts a temporal transport into a *spatial* one and then applies spatial mass
transport `p:eq:mtp`.  The manuscript defines, for unique source and target
cells,

```
  T(𝓗, w, z) = a_{H_z}⁻¹ E_H^{H_w} ∫_ℝ 1_{X_t = H_z} V(Ω, 0, t) dt
```

("set it to zero at ambiguous source or target roots"), observes that

> Under spatial dilation, `a_{H_z}` and `dt` each acquire a factor `C²`, whereas
> `V` acquires a factor `C^{-2}`.  Thus `T` has exactly degree `-2` and satisfies
> the covariance needed in `p:eq:mtp`,

and then computes the two spatial integrals:

> Integration in `z` cancels the denominator and sums the indicator over all
> target cells.  This gives the left side of `p:eq:timeMTP`.  For the incoming
> integral, fix the environment and put `o = H_0`.  Integration over source cells
> gives `∑_v (a_v / a_o) E_H^v ∫_ℝ 1_{X_t = o} V(Ω,0,t) dt`.

All of that is proved here, with the exact manuscript normalisation.

## What is the input and what is the conclusion

The *temporal* data is isolated in the structure `ConditionalPathIntegral`.  Its
`toFun e n m` is the manuscript's conditional path integral

```
  I(H, v, v') = E_H^{v} ∫_ℝ 1_{X_t = v'} V(Ω, 0, t) dt ,
```

indexed by the code slots of the environment, with three properties:

* joint measurability in the environment (`measurable_toFun`), which is the
  measurable trajectory coding of `p:sec:temporalmtp`;
* vanishing when a slot carries no cell (`absent_source`, `absent_target`) — no
  source or target vertex transports nothing;
* **similarity invariance** (`scaleInvariant`): `I` is unchanged by a physical
  similarity of the environment.  This is *exactly* the manuscript's scaling
  bookkeeping for the numerator alone: `dt` acquires `C²` and `V` acquires
  `C^{-2}`, so the product `∫ 1_{X_t = H_z} V(Ω,0,t) dt` has parabolic degree
  `0`.  It is a covariance statement about the temporal input, **not** about the
  mass-transport identity.

The *conclusion* proved from this input is the manuscript's spatial transport and
its consequences:

* `annealedSpatialTransport` is the transport `p:eq:spacefromtime`, written as
  the manuscript's boundary-masked sum over ordered pairs of cells, so that
  ambiguous source or target roots really transport zero;
* `annealedSpatialTransport_covariant` is the asserted **degree `-2`**
  covariance, with the single factor `(s²)⁻¹` coming from the target area
  `a_{H_z}` alone;
* `annealedSpatialTransportKernel` packages it as an honest
  `EnvironmentLaws.MassTransportKernel`, so the existing law
  `EnvironmentLaws.MassTransport` applies to it verbatim;
* `lintegral_annealedSpatialTransport_outgoing_eq_rooted` and
  `lintegral_annealedSpatialTransport_incoming_eq_rooted` are the two displayed
  integrals of the manuscript proof, off the null boundary mask;
* `lintegral_rootedOutgoing_eq_lintegral_rootedIncoming` is the annealed
  identity obtained by applying spatial mass transport, i.e. the manuscript
  equality between `E ∫_ℝ V(Ω,0,t) dt` and
  `E ∑_v (a_v/a_o) E_H^v ∫_ℝ 1_{X_t = o} V(Ω,0,t) dt`.

## Why this is the paper's route, and what remains

The already-proved `ReflectedGMS.Temporal.TemporalMassTransport` supplies the
*fixed-environment* half of `p:lem:timeMTP`: for a σ-finite time-shift invariant
path measure, outgoing and incoming temporal transports through the time origin
agree.  That file explicitly leaves open the annealed passage, which is what is
proved here.  Combining the two gives `p:eq:timeMTP`, and the remaining
mathematical producers for a fully unconditional statement are exactly:

1. the shift invariance of the σ-finite fixed-environment path measure
   `Q_H = ∑_v a_v P_H^v` of `p:eq:sigmapath`, reduced by
   `Temporal.SigmaFiniteTwoSidedShift` and `Temporal.AreaCylinderShiftIdentity`
   to the area-reversibility of the one-step transition function;
2. the identification of the manuscript's conditional path integral for a
   concrete `V` as a `ConditionalPathIntegral`, i.e. the measurable trajectory
   coding together with the parabolic degree `-2` hypothesis of `p:lem:timeMTP`
   transferred through the dilation `S_C Ω = (C𝓗, (C X_{t/C²}))`.

Nothing here assumes a measure-preserving real time shift of the *annealed*
rooted probability law, and nothing here assumes stationarity of that law: the
whole annealed input used is `EnvironmentLaws.MassTransport`, the manuscript's
spatial mass-transport assumption `s:eq:MTP`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ReflectedGMS.AnnealedTemporalTransport

open Code EnvironmentLaws Spatial BaseSpecificEnergy

/-! ### The temporal input -/

/-- The manuscript's conditional path integral

`I(H, v, v') = E_H^{v} ∫_ℝ 1_{X_t = v'} V(Ω, 0, t) dt`,

indexed by the code slots of the environment.  See the module docstring: the
three fields are the measurable trajectory coding, the convention that an absent
source or target vertex transports nothing, and the parabolic degree `0` of the
numerator (`dt` gains `C²`, `V` gains `C^{-2}`). -/
structure ConditionalPathIntegral where
  /-- `toFun e n m` is `E_H^{H_n} ∫_ℝ 1_{X_t = H_m} V(Ω,0,t) dt`. -/
  toFun : Env → ℕ → ℕ → ℝ≥0∞
  /-- Measurability in the environment, from the measurable trajectory coding. -/
  measurable_toFun : ∀ n m : ℕ, Measurable fun e : Env => toFun e n m
  /-- An absent source slot carries no starting vertex. -/
  absent_source : ∀ (e : Env) (n m : ℕ), e.val.1 n = none → toFun e n m = 0
  /-- An absent target slot carries no target cell. -/
  absent_target : ∀ (e : Env) (n m : ℕ), e.val.1 m = none → toFun e n m = 0
  /-- Parabolic degree `0`: the time measure gains `C²` and `V` gains `C^{-2}`,
  so the conditional path integral is similarity invariant. -/
  scaleInvariant : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
      (relabel : Vertex e.val ≃ Vertex e'.val),
      IsSimilarityRelabel s u hs e e' relabel →
      ∀ v v' : Vertex e.val,
        toFun e' (relabel v).val (relabel v').val = toFun e v.val v'.val

/-! ### The transport of one ordered pair of cells -/

/-- The contribution of one ordered pair of cells to the manuscript transport
`T(𝓗, w, z) = a_{H_z}⁻¹ E_H^{H_w} ∫_ℝ 1_{X_t = H_z} V(Ω,0,t) dt`.  Only the
**target** area appears in the denominator, exactly as in `p:eq:spacefromtime`,
and the two interior indicators implement "set it to zero at ambiguous source or
target roots". -/
noncomputable def cellPairTimeTransport (K L : CompactCell) (I : ℝ≥0∞) (w z : Plane) : ℝ≥0∞ :=
  interiorIndicator K w * interiorIndicator L z * I * (volume (L : Set Plane))⁻¹

theorem cellPairTimeTransport_of_zero (K L : CompactCell) (w z : Plane) :
    cellPairTimeTransport K L 0 w z = 0 := by
  rw [cellPairTimeTransport]
  ring

theorem measurable_cellPairTimeTransport_target (K L : CompactCell) (I : ℝ≥0∞) (w : Plane) :
    Measurable fun z : Plane => cellPairTimeTransport K L I w z := by
  have hEq : (fun z : Plane => cellPairTimeTransport K L I w z)
      = fun z : Plane =>
        (interiorIndicator K w * I * (volume (L : Set Plane))⁻¹) * interiorIndicator L z := by
    funext z
    simp only [cellPairTimeTransport]
    ring
  rw [hEq]
  refine measurable_const.mul ?_
  show Measurable (Set.indicator (interior (L : Set Plane)) (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator isOpen_interior.measurableSet

theorem measurable_cellPairTimeTransport_source (K L : CompactCell) (I : ℝ≥0∞) (z : Plane) :
    Measurable fun w : Plane => cellPairTimeTransport K L I w z := by
  have hEq : (fun w : Plane => cellPairTimeTransport K L I w z)
      = fun w : Plane =>
        (interiorIndicator L z * I * (volume (L : Set Plane))⁻¹) * interiorIndicator K w := by
    funext w
    simp only [cellPairTimeTransport]
    ring
  rw [hEq]
  refine measurable_const.mul ?_
  show Measurable (Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator isOpen_interior.measurableSet

/-- **Degree `-2` covariance of the pair transport.**  The two interior
indicators are exactly covariant, the conditional path integral `I` is
similarity invariant (parabolic degree `0`), and the *single* remaining factor is
the target area `a_{H_z}`, which scales by `s²`.  This is the manuscript's
"`a_{H_z}` and `dt` each acquire a factor `C²`, whereas `V` acquires a factor
`C^{-2}`; thus `T` has exactly degree `-2`". -/
theorem cellPairTimeTransport_transformCell (s : ℝ) (u : Plane) (hs : 0 < s)
    (K L : CompactCell) (I : ℝ≥0∞) (w z : Plane) :
    cellPairTimeTransport (transformCell s u hs K) (transformCell s u hs L) I
        (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * cellPairTimeTransport K L I w z := by
  have hspos : (0 : ℝ) < s ^ 2 := by positivity
  have ht0 : ENNReal.ofReal (s ^ 2) ≠ 0 := by simpa using hspos.ne'
  have httop : ENNReal.ofReal (s ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hindK : interiorIndicator (transformCell s u hs K) (positiveSimilarity s u w)
      = interiorIndicator K w :=
    indicator_one_congr_of_iff (mem_interior_transformCell_iff s u hs K w)
  have hindL : interiorIndicator (transformCell s u hs L) (positiveSimilarity s u z)
      = interiorIndicator L z :=
    indicator_one_congr_of_iff (mem_interior_transformCell_iff s u hs L z)
  have hvolL : (volume ((transformCell s u hs L : CompactCell) : Set Plane))⁻¹
      = (ENNReal.ofReal (s ^ 2))⁻¹ * (volume (L : Set Plane))⁻¹ := by
    rw [coe_transformCell, volume_image_positiveSimilarity s u (L : Set Plane),
      ENNReal.mul_inv (Or.inl ht0) (Or.inl httop)]
  rw [cellPairTimeTransport, cellPairTimeTransport, hindK, hindL, hvolL,
    ENNReal.ofReal_inv_of_pos hspos]
  ring

/-- **Integration in the target cancels the denominator.**  For a cell with null
frontier and positive finite area, `∫_z` of the pair transport is the source
indicator times the conditional path integral: this is the manuscript's
"integration in `z` cancels the denominator". -/
theorem lintegral_cellPairTimeTransport_target (K L : CompactCell) (I : ℝ≥0∞) (w : Plane)
    (hfrontL : volume (frontier (L : Set Plane)) = 0)
    (hposL : 0 < volume (L : Set Plane)) (hfinL : volume (L : Set Plane) < ∞) :
    (∫⁻ z : Plane, cellPairTimeTransport K L I w z ∂volume)
      = interiorIndicator K w * I := by
  have hI : MeasurableSet (interior (L : Set Plane)) := isOpen_interior.measurableSet
  have hz : ∀ z : Plane, cellPairTimeTransport K L I w z
      = Set.indicator (interior (L : Set Plane))
        (fun _ => interiorIndicator K w * I * (volume (L : Set Plane))⁻¹) z := by
    intro z
    by_cases hzI : z ∈ interior (L : Set Plane)
    · rw [Set.indicator_of_mem hzI, cellPairTimeTransport, interiorIndicator_of_mem hzI]
      ring
    · rw [Set.indicator_of_notMem hzI, cellPairTimeTransport,
        interiorIndicator_of_notMem hzI]
      ring
  simp_rw [hz]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfrontL, mul_assoc,
    ENNReal.inv_mul_cancel hposL.ne' hfinL.ne, mul_one]

/-- **Integration over source cells produces the area factor `a_v`.**  This is
the manuscript's "integration over source cells gives
`∑_v (a_v/a_o) E_H^v ∫ 1_{X_t=o} V(Ω,0,t) dt`". -/
theorem lintegral_cellPairTimeTransport_source (K L : CompactCell) (I : ℝ≥0∞) (z : Plane)
    (hfrontK : volume (frontier (K : Set Plane)) = 0) :
    (∫⁻ w : Plane, cellPairTimeTransport K L I w z ∂volume)
      = volume (K : Set Plane) * (interiorIndicator L z * I * (volume (L : Set Plane))⁻¹) := by
  have hI : MeasurableSet (interior (K : Set Plane)) := isOpen_interior.measurableSet
  have hw : ∀ w : Plane, cellPairTimeTransport K L I w z
      = Set.indicator (interior (K : Set Plane))
        (fun _ => interiorIndicator L z * I * (volume (L : Set Plane))⁻¹) w := by
    intro w
    by_cases hwI : w ∈ interior (K : Set Plane)
    · rw [Set.indicator_of_mem hwI, cellPairTimeTransport, interiorIndicator_of_mem hwI]
      ring
    · rw [Set.indicator_of_notMem hwI, cellPairTimeTransport,
        interiorIndicator_of_notMem hwI]
      ring
  simp_rw [hw]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfrontK]
  ring

/-! ### Slot and environment level transport -/

/-- The pair transport of two code slots, read through the measurable default
`referenceCell`.  An absent slot transports nothing, by
`slotPairTimeTransport_eq_zero_of_none`. -/
noncomputable def slotPairTimeTransport (J : ConditionalPathIntegral) (e : Env) (n m : ℕ)
    (w z : Plane) : ℝ≥0∞ :=
  cellPairTimeTransport ((e.val.1 n).getD referenceCell) ((e.val.1 m).getD referenceCell)
    (J.toFun e n m) w z

theorem slotPairTimeTransport_eq_zero_of_none (J : ConditionalPathIntegral) (e : Env) (n m : ℕ)
    (w z : Plane) (h : e.val.1 n = none ∨ e.val.1 m = none) :
    slotPairTimeTransport J e n m w z = 0 := by
  have hzero : J.toFun e n m = 0 := by
    rcases h with h | h
    · exact J.absent_source e n m h
    · exact J.absent_target e n m h
  rw [slotPairTimeTransport, hzero]
  exact cellPairTimeTransport_of_zero _ _ w z

theorem slotPairTimeTransport_vertex (J : ConditionalPathIntegral) (e : Env)
    (v v' : Vertex e.val) (w z : Plane) :
    slotPairTimeTransport J e v.val v'.val w z
      = cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
        (J.toFun e v.val v'.val) w z := by
  have hv : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
  have hv' : e.val.1 v'.val = some ((decode e).cell v') := (Option.some_get v'.property).symm
  rw [slotPairTimeTransport, hv, hv']
  simp only [Option.getD_some]

/-- **The manuscript spatial transport `p:eq:spacefromtime`** on the full trace
environment space:
`T(𝓗, w, z) = a_{H_z}⁻¹ E_H^{H_w} ∫_ℝ 1_{X_t = H_z} V(Ω,0,t) dt`, summed over
ordered pairs of code slots so that ambiguous source or target roots transport
zero. -/
noncomputable def annealedSpatialTransport (J : ConditionalPathIntegral)
    (p : Env × Plane × Plane) : ℝ≥0∞ :=
  ∑' q : ℕ × ℕ, slotPairTimeTransport J p.1 q.1 q.2 p.2.1 p.2.2

theorem measurable_annealedSpatialTransport (J : ConditionalPathIntegral) :
    Measurable (annealedSpatialTransport J) := by
  have hslot : ∀ q : ℕ × ℕ, Measurable fun p : Env × Plane × Plane =>
      slotPairTimeTransport J p.1 q.1 q.2 p.2.1 p.2.2 := by
    intro q
    have hcode : Measurable fun p : Env × Plane × Plane => p.1.val :=
      measurable_inclusion.comp measurable_fst
    have h1 : Measurable fun p : Env × Plane × Plane =>
        ((p.1.val.1 q.1).getD referenceCell : CompactCell) :=
      measurable_slotCell.comp ((measurable_pi_apply q.1).comp (measurable_fst.comp hcode))
    have h2 : Measurable fun p : Env × Plane × Plane =>
        ((p.1.val.1 q.2).getD referenceCell : CompactCell) :=
      measurable_slotCell.comp ((measurable_pi_apply q.2).comp (measurable_fst.comp hcode))
    have hw : Measurable fun p : Env × Plane × Plane => p.2.1 :=
      measurable_fst.comp measurable_snd
    have hz : Measurable fun p : Env × Plane × Plane => p.2.2 :=
      measurable_snd.comp measurable_snd
    have m1 : Measurable fun p : Env × Plane × Plane =>
        interiorIndicator ((p.1.val.1 q.1).getD referenceCell) p.2.1 :=
      measurable_interiorIndicator.comp (h1.prodMk hw)
    have m2 : Measurable fun p : Env × Plane × Plane =>
        interiorIndicator ((p.1.val.1 q.2).getD referenceCell) p.2.2 :=
      measurable_interiorIndicator.comp (h2.prodMk hz)
    have m3 : Measurable fun p : Env × Plane × Plane => J.toFun p.1 q.1 q.2 :=
      (J.measurable_toFun q.1 q.2).comp measurable_fst
    have m4 : Measurable fun p : Env × Plane × Plane =>
        (volume (((p.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
      (measurable_cellVolume.comp h2).inv
    have hEq : (fun p : Env × Plane × Plane =>
          slotPairTimeTransport J p.1 q.1 q.2 p.2.1 p.2.2)
        = fun p : Env × Plane × Plane =>
          interiorIndicator ((p.1.val.1 q.1).getD referenceCell) p.2.1 *
              interiorIndicator ((p.1.val.1 q.2).getD referenceCell) p.2.2 *
              J.toFun p.1 q.1 q.2 *
            (volume (((p.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane))⁻¹ := by
      funext p
      rw [slotPairTimeTransport, cellPairTimeTransport]
    rw [hEq]
    exact ((m1.mul m2).mul m3).mul m4
  exact Measurable.ennreal_tsum hslot

theorem annealedSpatialTransport_eq_tsum_vertex (J : ConditionalPathIntegral) (e : Env)
    (w z : Plane) :
    annealedSpatialTransport J (e, w, z)
      = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z := by
  have hinner : ∀ n : ℕ,
      (∑' m : ℕ, slotPairTimeTransport J e n m w z)
        = ∑' v' : Vertex e.val, slotPairTimeTransport J e n v'.val w z := by
    intro n
    have hsupp : Function.support (fun m : ℕ => slotPairTimeTransport J e n m w z)
        ⊆ {m : ℕ | (e.val.1 m).isSome} := by
      intro m hm
      cases hcase : e.val.1 m with
      | none =>
          refine absurd (show slotPairTimeTransport J e n m w z = 0 from ?_) hm
          exact slotPairTimeTransport_eq_zero_of_none J e n m w z (Or.inr hcase)
      | some L => simp [hcase]
    exact (tsum_subtype_eq_of_support_subset hsupp).symm
  have houter : Function.support
      (fun n : ℕ => ∑' v' : Vertex e.val, slotPairTimeTransport J e n v'.val w z)
      ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    cases hcase : e.val.1 n with
    | none =>
        refine absurd (show (∑' v' : Vertex e.val,
          slotPairTimeTransport J e n v'.val w z) = 0 from ?_) hn
        refine ENNReal.tsum_eq_zero.mpr fun v' => ?_
        exact slotPairTimeTransport_eq_zero_of_none J e n v'.val w z (Or.inl hcase)
    | some K => simp [hcase]
  calc annealedSpatialTransport J (e, w, z)
      = ∑' q : ℕ × ℕ, slotPairTimeTransport J e q.1 q.2 w z := rfl
    _ = ∑' n : ℕ, ∑' m : ℕ, slotPairTimeTransport J e n m w z := ENNReal.tsum_prod'
    _ = ∑' n : ℕ, ∑' v' : Vertex e.val, slotPairTimeTransport J e n v'.val w z :=
        tsum_congr hinner
    _ = ∑' n : {n : ℕ | (e.val.1 n).isSome}, ∑' v' : Vertex e.val,
          slotPairTimeTransport J e n.val v'.val w z :=
        (tsum_subtype_eq_of_support_subset houter).symm
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z :=
        tsum_congr fun v => tsum_congr fun v' => slotPairTimeTransport_vertex J e v v' w z

/-- **The manuscript's degree `-2` covariance of `p:eq:spacefromtime`.**  The
only scaling factor is the target area `a_{H_z}`, because the conditional path
integral itself has parabolic degree `0`. -/
theorem annealedSpatialTransport_covariant (J : ConditionalPathIntegral) (s : ℝ) (u : Plane)
    (hs : 0 < s) (e e' : Env) (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    annealedSpatialTransport J (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * annealedSpatialTransport J (e, w, z) := by
  obtain ⟨relabel, hrelabel⟩ := hsim
  obtain ⟨hcell, hc⟩ := hrelabel
  rw [annealedSpatialTransport_eq_tsum_vertex, annealedSpatialTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq relabel (fun a : Vertex e'.val => ∑' b : Vertex e'.val,
      cellPairTimeTransport ((decode e').cell a) ((decode e').cell b)
        (J.toFun e' a.val b.val) (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [← Equiv.tsum_eq relabel (fun b : Vertex e'.val =>
      cellPairTimeTransport ((decode e').cell (relabel v)) ((decode e').cell b)
        (J.toFun e' (relabel v).val b.val) (positiveSimilarity s u w)
        (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v' => ?_
  rw [J.scaleInvariant s u hs e e' relabel ⟨hcell, hc⟩ v v', hcell v, hcell v',
    cellPairTimeTransport_transformCell]

/-- **The manuscript transport `p:eq:spacefromtime` as an actual
`EnvironmentLaws.MassTransportKernel`.**  This is the statement "`T` has exactly
degree `-2` and satisfies the covariance needed in `p:eq:mtp`". -/
noncomputable def annealedSpatialTransportKernel (J : ConditionalPathIntegral) :
    MassTransportKernel where
  toFun := annealedSpatialTransport J
  measurable_toFun := measurable_annealedSpatialTransport J
  covariant := fun s u hs e e' hsim w z =>
    annealedSpatialTransport_covariant J s u hs e e' hsim w z

/-! ### The two spatial integrals of the manuscript proof -/

theorem lintegral_annealedSpatialTransport_outgoing (J : ConditionalPathIntegral) (e : Env)
    (w : Plane) :
    (∫⁻ z : Plane, annealedSpatialTransport J (e, w, z) ∂volume)
      = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          interiorIndicator ((decode e).cell v) w * J.toFun e v.val v'.val := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v v' : Vertex e.val, Measurable fun z : Plane =>
      cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
        (J.toFun e v.val v'.val) w z := fun v v' =>
    measurable_cellPairTimeTransport_target _ _ _ _
  calc (∫⁻ z : Plane, annealedSpatialTransport J (e, w, z) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z ∂volume :=
        lintegral_congr fun z => annealedSpatialTransport_eq_tsum_vertex J e w z
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane, ∑' v' : Vertex e.val,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z ∂volume :=
        lintegral_tsum fun v => (Measurable.ennreal_tsum fun v' => hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val, ∫⁻ z : Plane,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z ∂volume :=
        tsum_congr fun v => lintegral_tsum fun v' => (hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          interiorIndicator ((decode e).cell v) w * J.toFun e v.val v'.val :=
        tsum_congr fun v => tsum_congr fun v' =>
          lintegral_cellPairTimeTransport_target _ _ _ _ (hgeom.2.2.1 v')
            (cellVolume_pos_lt_top (decode e) hgeom v').1
            (cellVolume_pos_lt_top (decode e) hgeom v').2

theorem lintegral_annealedSpatialTransport_incoming (J : ConditionalPathIntegral) (e : Env)
    (z : Plane) :
    (∫⁻ w : Plane, annealedSpatialTransport J (e, w, z) ∂volume)
      = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          volume ((decode e).cell v : Set Plane) *
            (interiorIndicator ((decode e).cell v') z * J.toFun e v.val v'.val *
              (volume ((decode e).cell v' : Set Plane))⁻¹) := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v v' : Vertex e.val, Measurable fun w : Plane =>
      cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
        (J.toFun e v.val v'.val) w z := fun v v' =>
    measurable_cellPairTimeTransport_source _ _ _ _
  calc (∫⁻ w : Plane, annealedSpatialTransport J (e, w, z) ∂volume)
      = ∫⁻ w : Plane, ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z ∂volume :=
        lintegral_congr fun w => annealedSpatialTransport_eq_tsum_vertex J e w z
    _ = ∑' v : Vertex e.val, ∫⁻ w : Plane, ∑' v' : Vertex e.val,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z ∂volume :=
        lintegral_tsum fun v => (Measurable.ennreal_tsum fun v' => hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val, ∫⁻ w : Plane,
          cellPairTimeTransport ((decode e).cell v) ((decode e).cell v')
            (J.toFun e v.val v'.val) w z ∂volume :=
        tsum_congr fun v => lintegral_tsum fun v' => (hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          volume ((decode e).cell v : Set Plane) *
            (interiorIndicator ((decode e).cell v') z * J.toFun e v.val v'.val *
              (volume ((decode e).cell v' : Set Plane))⁻¹) :=
        tsum_congr fun v => tsum_congr fun v' =>
          lintegral_cellPairTimeTransport_source _ _ _ _ (hgeom.2.2.1 v)

/-! ### The rooted densities of `p:eq:timeMTP` -/

/-- The boundary-masked **outgoing** temporal density at the origin,
`∑_{H'} E_H^{H_0} ∫_ℝ 1_{X_t = H'} V(Ω,0,t) dt`.  Summing the target indicator
over all cells is the manuscript's "sums the indicator over all target cells",
so this is the left side of `p:eq:timeMTP`, `E_H^{H_0} ∫_ℝ V(Ω,0,t) dt`, for a
`V` supported on vertex target times. -/
noncomputable def rootedOutgoingTemporalDensity (J : ConditionalPathIntegral) (e : Env) : ℝ≥0∞ :=
  (RootDensities.rootAt (decode e) 0).elim 0 fun v₀ =>
    ∑' v' : Vertex e.val, J.toFun e v₀.val v'.val

/-- The boundary-masked **incoming** temporal density at the origin,
`∑_v (a_v / a_o) E_H^v ∫_ℝ 1_{X_t = o} V(Ω,0,t) dt` with `o = H_0`.  This is the
displayed intermediate expression of the manuscript proof. -/
noncomputable def rootedIncomingTemporalDensity (J : ConditionalPathIntegral) (e : Env) : ℝ≥0∞ :=
  (RootDensities.rootAt (decode e) 0).elim 0 fun v₀ =>
    ∑' v : Vertex e.val, volume ((decode e).cell v : Set Plane) *
      (J.toFun e v.val v₀.val * (volume ((decode e).cell v₀ : Set Plane))⁻¹)

/-- Off the null boundary mask the outgoing spatial integral of
`p:eq:spacefromtime` is exactly the outgoing temporal density. -/
theorem lintegral_annealedSpatialTransport_outgoing_eq_rooted (J : ConditionalPathIntegral)
    (e : Env) (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    (∫⁻ z : Plane, annealedSpatialTransport J (e, 0, z) ∂volume)
      = rootedOutgoingTemporalDensity J e := by
  have hgeom := decode_geometry e
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom he
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom he
  have hone : interiorIndicator ((decode e).cell v₀) 0 = 1 := interiorIndicator_of_mem hint
  rw [lintegral_annealedSpatialTransport_outgoing J e 0]
  rw [tsum_eq_single v₀ ?_]
  · simp only [rootedOutgoingTemporalDensity, hv₀, Option.elim]
    exact tsum_congr fun v' => by rw [hone, one_mul]
  · intro v hv
    have hnot : (0 : Plane) ∉ interior ((decode e).cell v : Set Plane) := by
      intro hmem
      exact hv (huniq.unique hmem hint)
    refine ENNReal.tsum_eq_zero.mpr fun v' => ?_
    rw [interiorIndicator_of_notMem hnot, zero_mul]

/-- Off the null boundary mask the incoming spatial integral of
`p:eq:spacefromtime` is exactly the incoming temporal density. -/
theorem lintegral_annealedSpatialTransport_incoming_eq_rooted (J : ConditionalPathIntegral)
    (e : Env) (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    (∫⁻ w : Plane, annealedSpatialTransport J (e, w, 0) ∂volume)
      = rootedIncomingTemporalDensity J e := by
  have hgeom := decode_geometry e
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom he
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom he
  have hone : interiorIndicator ((decode e).cell v₀) 0 = 1 := interiorIndicator_of_mem hint
  have hinner : ∀ v : Vertex e.val,
      (∑' v' : Vertex e.val, volume ((decode e).cell v : Set Plane) *
          (interiorIndicator ((decode e).cell v') 0 * J.toFun e v.val v'.val *
            (volume ((decode e).cell v' : Set Plane))⁻¹))
        = volume ((decode e).cell v : Set Plane) *
            (J.toFun e v.val v₀.val * (volume ((decode e).cell v₀ : Set Plane))⁻¹) := by
    intro v
    rw [tsum_eq_single v₀ ?_]
    · rw [hone, one_mul]
    · intro v' hv'
      have hnot : (0 : Plane) ∉ interior ((decode e).cell v' : Set Plane) := by
        intro hmem
        exact hv' (huniq.unique hmem hint)
      rw [interiorIndicator_of_notMem hnot, zero_mul, zero_mul, mul_zero]
  rw [lintegral_annealedSpatialTransport_incoming J e 0, tsum_congr hinner]
  simp only [rootedIncomingTemporalDensity, hv₀, Option.elim]

/-! ### The annealed identity from spatial mass transport -/

/-- **Annealed temporal transport from spatial mass transport.**  Applying the
manuscript spatial mass-transport assumption `p:eq:mtp` to the transport
`p:eq:spacefromtime` gives

```
  E ∑_{H'} E_H^{H_0} ∫_ℝ 1_{X_t = H'} V(Ω,0,t) dt
    = E ∑_v (a_v/a_o) E_H^v ∫_ℝ 1_{X_t = o} V(Ω,0,t) dt ,   o = H_0 ,
```

which is precisely the step "apply spatial mass transport to finish" of the
proof of `p:lem:timeMTP`.  The only annealed input is
`EnvironmentLaws.MassTransport`; no time shift of the rooted probability law and
no annealed stationarity is used.  The remaining producer for `p:eq:timeMTP`
itself is the σ-finite fixed-environment time-shift step, which is
`ReflectedGMS.Temporal.TemporalMassTransport`. -/
theorem lintegral_rootedOutgoing_eq_lintegral_rootedIncoming (J : ConditionalPathIntegral)
    (ν : Measure Env) (hν : MassTransport ν) :
    (∫⁻ e : Env, rootedOutgoingTemporalDensity J e ∂ν)
      = ∫⁻ e : Env, rootedIncomingTemporalDensity J e ∂ν := by
  have hmt : (∫⁻ e : Env, ∫⁻ z : Plane, annealedSpatialTransport J (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ z : Plane, annealedSpatialTransport J (e, z, 0) ∂volume ∂ν :=
    hν (annealedSpatialTransportKernel J)
  have hout : (∫⁻ e : Env, ∫⁻ z : Plane, annealedSpatialTransport J (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, rootedOutgoingTemporalDensity J e ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_notMem_boundaryMask_of_massTransport ν hν] with e he
    exact lintegral_annealedSpatialTransport_outgoing_eq_rooted J e he
  have hin : (∫⁻ e : Env, ∫⁻ z : Plane, annealedSpatialTransport J (e, z, 0) ∂volume ∂ν)
      = ∫⁻ e : Env, rootedIncomingTemporalDensity J e ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_notMem_boundaryMask_of_massTransport ν hν] with e he
    exact lintegral_annealedSpatialTransport_incoming_eq_rooted J e he
  exact hout.symm.trans (hmt.trans hin)

end ReflectedGMS.AnnealedTemporalTransport

/-! ## Remaining mathematical gap

Proved here: the manuscript spatial transport `p:eq:spacefromtime` is an honest
degree `-2` `EnvironmentLaws.MassTransportKernel`, its outgoing spatial integral
is the outgoing temporal density, its incoming spatial integral is the
manuscript's `∑_v (a_v/a_o) E_H^v ∫ 1_{X_t=o} V dt`, and spatial mass transport
equates the two annealed expectations.

Not claimed here:

* the identification of a concrete `V` of parabolic scaling degree `-2` as a
  `ConditionalPathIntegral`, i.e. the measurable trajectory coding of
  `p:sec:temporalmtp` together with the transfer of the degree `-2` rule through
  the dilation `S_C Ω = (C𝓗, (C X_{t/C²}))`;
* the σ-finite fixed-environment time-shift step, which is already proved in
  `ReflectedGMS.Temporal.TemporalMassTransport` from the shift invariance of
  `Q_H = ∑_v a_v P_H^v`, whose own remaining producer is the area-weighted
  finite-cylinder shift identity of `Temporal.AreaCylinderShiftIdentity`.

In particular no measure-preserving real shift of the annealed rooted
probability law is assumed anywhere in this file.
-/
