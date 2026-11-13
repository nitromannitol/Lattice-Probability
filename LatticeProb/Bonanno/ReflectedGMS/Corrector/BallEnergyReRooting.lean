/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BallEnergyReRooting at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GraphBallReach
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BaseSpecificEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedMassTransportProducer

/-!
# Re-rooting a scale-invariant vertex observable from the root cell to a graph ball

`HarmonicCoordinateAssembly.MarkedSpecificEnergyConvergence` controls the manuscript
specific-energy density of the gradient error **at the root cell only**:
`ρ_m(H_0) → 0` in expectation.  The discrete Poincaré inequality of
`Corrector/DiscreteBallPoincare` needs that density **throughout the graph ball**
`B(H_0, radius+1)`.  Passing from one to the other is a re-rooting statement, and the
manuscript's own tool for re-rooting is mass transport.

This module carries out that step for an arbitrary scale-invariant slot observable.

## The transport

With `T` the kernel

`T(𝓗, 𝔻, w, z) = ∑_{u,v} 1_{w ∈ H_u°} 1_{z ∈ H_v°} 1_{d_G(u,v) ≤ k} f(v) / a_v`,

the two one-sided integrals at the origin are

* outgoing, `∫ T(𝓗, 𝔻, 0, z) dz = ∑_{v} 1_{d_G(H_0,v) ≤ k} f(v)` — the **ball sum**, because
  `∫ 1_{z ∈ H_v°} dz = a_v` cancels the `1/a_v`;
* incoming, `∫ T(𝓗, 𝔻, w, 0) dw = f(H_0) · W_k`, `W_k = (∑_{u} 1_{d_G(u,H_0) ≤ k} a_u)/a_{H_0}`
  — the **root value** times the ball-to-root area ratio.

`T` has scaling degree exactly `−2` (`s:eq:Tcov`): the two interior indicators and the
combinatorial reachability weight are similarity invariant, `f` is invariant by hypothesis,
and the single factor `1/a_v` contributes `(s²)⁻¹`.  So `EnvironmentLaws.MassTransport`
applies — through `Corrector/MarkedMassTransportProducer.markedMassTransport_of_massTransport`,
which is what allows the observable to depend on the independent grid marks as well as on the
environment — and gives

`E[∑_{v ∈ B(H_0,k)} f(v)] = E[f(H_0) · W_k]`.

## What is assumed and what is not

The observable is packaged as a `SlotObservable`: it vanishes on absent code slots, it is
measurable slot by slot, and it is **invariant** under the joint similarity action
`MarkedMassTransportProducer.markedSimilarity` together with the relabelling of the physical
similarity.  Invariance is the manuscript's degree-zero property of `ρ`: conductances are
similarity invariant while `|θ|²` and `a` both scale by `s²`.

No stationarity, no ergodicity and no translation-invariance of `ν` is used — only
`EnvironmentLaws.MassTransport ν`, i.e. `s:eq:MTP` itself.  In particular this module does
**not** route through the translation-only marked transport predicate, which is not derivable
from `s:eq:MTP`.

The combinatorial ball indicator is `GraphBallReach.reach`, a slot-level recursion; the
project's `Corrector/MarkedDensityMeasurabilityProducer.LazyReach` is the same notion as a
`Prop`, but the kernel needs an `ℝ≥0∞`-valued factor and, above all, needs the similarity
invariance `GraphBallReach.reach_relabel`, which the `Prop` form does not carry.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.BallEnergyReRooting

open Code EnvironmentLaws Spatial BaseSpecificEnergy GraphBallReach
open MarkedMassTransportProducer DyadicGridLaw DyadicApproximation

/-! ### The one-pair kernel -/

/-- The contribution of one ordered pair of cells to the re-rooting transport: the source
indicator at `w`, the target indicator at `z`, the combinatorial weight `t`, the observable
value `d` at the target, and the single area denominator that carries the whole scaling
degree. -/
noncomputable def cellPairBallTransport (K L : CompactCell) (t d : ℝ≥0∞) (w z : Plane) :
    ℝ≥0∞ :=
  interiorIndicator K w * interiorIndicator L z * t * d * (volume (L : Set Plane))⁻¹

theorem cellPairBallTransport_of_weight_zero (K L : CompactCell) (d : ℝ≥0∞) (w z : Plane) :
    cellPairBallTransport K L 0 d w z = 0 := by
  rw [cellPairBallTransport]; ring

theorem cellPairBallTransport_of_value_zero (K L : CompactCell) (t : ℝ≥0∞) (w z : Plane) :
    cellPairBallTransport K L t 0 w z = 0 := by
  rw [cellPairBallTransport]; ring

/-- **Degree `-2` covariance of the one-pair kernel.**  The two interior indicators are
invariant, the combinatorial weight and the observable value are carried unchanged, and the
one area denominator supplies the factor `(s²)⁻¹`. -/
theorem cellPairBallTransport_transformCell (s : ℝ) (u : Plane) (hs : 0 < s)
    (K L : CompactCell) (t d : ℝ≥0∞) (w z : Plane) :
    cellPairBallTransport (transformCell s u hs K) (transformCell s u hs L) t d
        (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * cellPairBallTransport K L t d w z := by
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
  rw [cellPairBallTransport, cellPairBallTransport, hindK, hindL, hvolL,
    ENNReal.ofReal_inv_of_pos hspos]
  ring

/-! ### Slot observables -/

/-- The data a nonnegative vertex observable must carry in order to be re-rooted by the
manuscript mass transport: it is supported on the active code slots, it is measurable slot by
slot, and it is a **degree-zero** physical quantity, i.e. invariant under the joint similarity
action on the environment and the grid marks. -/
structure SlotObservable where
  /-- The observable, read at a code slot of a marked configuration. -/
  toFun : Env × Grid → ℕ → ℝ≥0∞
  /-- Absent slots are not vertices and carry nothing. -/
  absent : ∀ (p : Env × Grid) (n : ℕ), p.1.val.1 n = none → toFun p n = 0
  /-- Measurability in the marked configuration, one slot at a time. -/
  measurable_toFun : ∀ n : ℕ, Measurable fun p : Env × Grid => toFun p n
  /-- Scale invariance along the joint similarity action. -/
  invariant : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : Env × Grid)
    (rel : Vertex p.1.val ≃ Vertex (markedSimilarity s u hs p).1.val),
    IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel →
    ∀ v : Vertex p.1.val, toFun (markedSimilarity s u hs p) (rel v).val = toFun p v.val

/-! ### The transport -/

/-- The manuscript re-rooting transport of a slot observable, summed over ordered pairs of
code slots. -/
noncomputable def ballTransport (k : ℕ) (Q : SlotObservable) (p : Env × Grid) (w z : Plane) :
    ℝ≥0∞ :=
  ∑' q : ℕ × ℕ,
    cellPairBallTransport ((p.1.val.1 q.1).getD referenceCell)
      ((p.1.val.1 q.2).getD referenceCell) (reach p.1.val.2 k q.1 q.2) (Q.toFun p q.2) w z

/-- The transport as a sum over actual vertices: absent target slots carry no observable and
absent source slots reach nothing else. -/
theorem ballTransport_eq_tsum_vertex (k : ℕ) (Q : SlotObservable) (p : Env × Grid)
    (w z : Plane) :
    ballTransport k Q p w z
      = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z := by
  have hinner : ∀ n : ℕ,
      (∑' m : ℕ, cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
          ((p.1.val.1 m).getD referenceCell) (reach p.1.val.2 k n m) (Q.toFun p m) w z)
        = ∑' v' : Vertex p.1.val, cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
            ((p.1.val.1 v'.val).getD referenceCell) (reach p.1.val.2 k n v'.val)
            (Q.toFun p v'.val) w z := by
    intro n
    have hsupp : Function.support
        (fun m : ℕ => cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
          ((p.1.val.1 m).getD referenceCell) (reach p.1.val.2 k n m) (Q.toFun p m) w z)
        ⊆ {m : ℕ | (p.1.val.1 m).isSome} := by
      intro m hm
      cases hcase : p.1.val.1 m with
      | none =>
          refine absurd (show cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
            ((p.1.val.1 m).getD referenceCell) (reach p.1.val.2 k n m) (Q.toFun p m) w z
            = 0 from ?_) hm
          rw [Q.absent p m hcase]
          exact cellPairBallTransport_of_value_zero _ _ _ w z
      | some L => simp [hcase]
    exact (tsum_subtype_eq_of_support_subset hsupp).symm
  have houter : Function.support
      (fun n : ℕ => ∑' v' : Vertex p.1.val,
        cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
          ((p.1.val.1 v'.val).getD referenceCell) (reach p.1.val.2 k n v'.val)
          (Q.toFun p v'.val) w z)
      ⊆ {n : ℕ | (p.1.val.1 n).isSome} := by
    intro n hn
    cases hcase : p.1.val.1 n with
    | none =>
        refine absurd (show (∑' v' : Vertex p.1.val,
          cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
            ((p.1.val.1 v'.val).getD referenceCell) (reach p.1.val.2 k n v'.val)
            (Q.toFun p v'.val) w z) = 0 from ?_) hn
        refine ENNReal.tsum_eq_zero.mpr fun v' => ?_
        have hne : n ≠ v'.val := by
          intro h
          have hv := v'.property
          rw [← h, hcase] at hv
          simp at hv
        rw [reach_eq_zero_of_absent p.1 hcase k hne]
        exact cellPairBallTransport_of_weight_zero _ _ _ w z
    | some K => simp [hcase]
  have houterterm : ∀ v : Vertex p.1.val,
      (∑' v' : Vertex p.1.val, cellPairBallTransport ((p.1.val.1 v.val).getD referenceCell)
          ((p.1.val.1 v'.val).getD referenceCell) (reach p.1.val.2 k v.val v'.val)
          (Q.toFun p v'.val) w z)
        = ∑' v' : Vertex p.1.val, cellPairBallTransport ((decode p.1).cell v)
            ((decode p.1).cell v') (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z := by
    intro v
    refine tsum_congr fun v' => ?_
    rw [← CanonicalSimilarity.decode_cell_eq_getD p.1 v, ← CanonicalSimilarity.decode_cell_eq_getD p.1 v']
  calc ballTransport k Q p w z
      = ∑' q : ℕ × ℕ, cellPairBallTransport ((p.1.val.1 q.1).getD referenceCell)
          ((p.1.val.1 q.2).getD referenceCell) (reach p.1.val.2 k q.1 q.2)
          (Q.toFun p q.2) w z := rfl
    _ = ∑' n : ℕ, ∑' m : ℕ, cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
          ((p.1.val.1 m).getD referenceCell) (reach p.1.val.2 k n m) (Q.toFun p m) w z :=
        ENNReal.tsum_prod'
    _ = ∑' n : ℕ, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((p.1.val.1 n).getD referenceCell)
            ((p.1.val.1 v'.val).getD referenceCell) (reach p.1.val.2 k n v'.val)
            (Q.toFun p v'.val) w z := tsum_congr hinner
    _ = ∑' n : {n : ℕ | (p.1.val.1 n).isSome}, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((p.1.val.1 n.val).getD referenceCell)
            ((p.1.val.1 v'.val).getD referenceCell) (reach p.1.val.2 k n.val v'.val)
            (Q.toFun p v'.val) w z := (tsum_subtype_eq_of_support_subset houter).symm
    _ = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z := tsum_congr houterterm

theorem measurable_ballTransport (k : ℕ) (Q : SlotObservable) :
    Measurable fun x : (Env × Grid) × Plane × Plane => ballTransport k Q x.1 x.2.1 x.2.2 := by
  have henv : Measurable fun x : (Env × Grid) × Plane × Plane => x.1.1 :=
    measurable_fst.comp measurable_fst
  have hcode : Measurable fun x : (Env × Grid) × Plane × Plane => x.1.1.val :=
    measurable_inclusion.comp henv
  have hw : Measurable fun x : (Env × Grid) × Plane × Plane => x.2.1 :=
    measurable_fst.comp measurable_snd
  have hz : Measurable fun x : (Env × Grid) × Plane × Plane => x.2.2 :=
    measurable_snd.comp measurable_snd
  refine Measurable.ennreal_tsum fun q : ℕ × ℕ => ?_
  have h1 : Measurable fun x : (Env × Grid) × Plane × Plane =>
      ((x.1.1.val.1 q.1).getD referenceCell : CompactCell) :=
    measurable_slotCell.comp ((measurable_pi_apply q.1).comp (measurable_fst.comp hcode))
  have h2 : Measurable fun x : (Env × Grid) × Plane × Plane =>
      ((x.1.1.val.1 q.2).getD referenceCell : CompactCell) :=
    measurable_slotCell.comp ((measurable_pi_apply q.2).comp (measurable_fst.comp hcode))
  have m1 : Measurable fun x : (Env × Grid) × Plane × Plane =>
      interiorIndicator ((x.1.1.val.1 q.1).getD referenceCell) x.2.1 :=
    measurable_interiorIndicator.comp (h1.prodMk hw)
  have m2 : Measurable fun x : (Env × Grid) × Plane × Plane =>
      interiorIndicator ((x.1.1.val.1 q.2).getD referenceCell) x.2.2 :=
    measurable_interiorIndicator.comp (h2.prodMk hz)
  have m3 : Measurable fun x : (Env × Grid) × Plane × Plane =>
      reach x.1.1.val.2 k q.1 q.2 := (measurable_reach k q.1 q.2).comp henv
  have m4 : Measurable fun x : (Env × Grid) × Plane × Plane => Q.toFun x.1 q.2 :=
    (Q.measurable_toFun q.2).comp measurable_fst
  have m5 : Measurable fun x : (Env × Grid) × Plane × Plane =>
      (volume (((x.1.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
    (measurable_cellVolume.comp h2).inv
  have hEq : (fun x : (Env × Grid) × Plane × Plane =>
        cellPairBallTransport ((x.1.1.val.1 q.1).getD referenceCell)
          ((x.1.1.val.1 q.2).getD referenceCell) (reach x.1.1.val.2 k q.1 q.2)
          (Q.toFun x.1 q.2) x.2.1 x.2.2)
      = fun x : (Env × Grid) × Plane × Plane =>
        interiorIndicator ((x.1.1.val.1 q.1).getD referenceCell) x.2.1 *
            interiorIndicator ((x.1.1.val.1 q.2).getD referenceCell) x.2.2 *
            reach x.1.1.val.2 k q.1 q.2 * Q.toFun x.1 q.2 *
          (volume (((x.1.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane))⁻¹ := by
    funext x
    rw [cellPairBallTransport]
  rw [hEq]
  exact ((((m1.mul m2).mul m3).mul m4).mul m5)

/-- **`s:eq:Tcov` for the re-rooting transport.**  Degree `-2` under every translation and
every positive dilation, with the grid marks transported along. -/
theorem ballTransport_markedSimilarityCovariant (k : ℕ) (Q : SlotObservable) :
    MarkedSimilarityCovariant (ballTransport k Q) := by
  intro s u hs p w z
  -- Ascribe the target as `(markedSimilarity s u hs p).1` (defeq to `similarityTargetEnv s u hs p.1`)
  -- so that `rel`'s codomain matches the goal syntactically and the `tsum` rewrites below fire.
  obtain ⟨rel, hcell, hc⟩ : IsSimilarity s u hs p.1 (markedSimilarity s u hs p).1 :=
    isSimilarity_similarityTargetEnv s u hs p.1
  have hrel : IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel := ⟨hcell, hc⟩
  rw [ballTransport_eq_tsum_vertex, ballTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq rel (fun a : Vertex (markedSimilarity s u hs p).1.val =>
      ∑' b : Vertex (markedSimilarity s u hs p).1.val,
        cellPairBallTransport ((decode (markedSimilarity s u hs p).1).cell a)
          ((decode (markedSimilarity s u hs p).1).cell b)
          (reach (markedSimilarity s u hs p).1.val.2 k a.val b.val)
          (Q.toFun (markedSimilarity s u hs p) b.val)
          (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [← Equiv.tsum_eq rel (fun b : Vertex (markedSimilarity s u hs p).1.val =>
      cellPairBallTransport ((decode (markedSimilarity s u hs p).1).cell (rel v))
        ((decode (markedSimilarity s u hs p).1).cell b)
        (reach (markedSimilarity s u hs p).1.val.2 k (rel v).val b.val)
        (Q.toFun (markedSimilarity s u hs p) b.val)
        (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v' => ?_
  rw [hcell v, hcell v', reach_relabel hrel k v v', Q.invariant s u hs p rel hrel v',
    cellPairBallTransport_transformCell]

/-- The re-rooting transport as a marked transport of degree `-2`. -/
theorem markedMassTransport_ballTransport (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (k : ℕ) (Q : SlotObservable) :
    (∫⁻ p : Env × Grid, ∫⁻ z : Plane, ballTransport k Q p 0 z ∂volume ∂(ν.prod gridMeasure))
      = ∫⁻ p : Env × Grid, ∫⁻ z : Plane, ballTransport k Q p z 0 ∂volume
          ∂(ν.prod gridMeasure) :=
  markedMassTransport_of_massTransport ν hν (ballTransport k Q) (measurable_ballTransport k Q)
    (ballTransport_markedSimilarityCovariant k Q)

/-! ### The two one-sided integrals -/

theorem lintegral_cellPairBallTransport_target (K L : CompactCell) (t d : ℝ≥0∞) (w : Plane)
    (hfrontL : volume (frontier (L : Set Plane)) = 0)
    (hposL : 0 < volume (L : Set Plane)) (hfinL : volume (L : Set Plane) < ∞) :
    (∫⁻ z : Plane, cellPairBallTransport K L t d w z ∂volume)
      = interiorIndicator K w * t * d := by
  have hI : MeasurableSet (interior (L : Set Plane)) := isOpen_interior.measurableSet
  have hz : ∀ z : Plane, cellPairBallTransport K L t d w z
      = Set.indicator (interior (L : Set Plane))
        (fun _ => interiorIndicator K w * t * d * (volume (L : Set Plane))⁻¹) z := by
    intro z
    by_cases hzI : z ∈ interior (L : Set Plane)
    · rw [Set.indicator_of_mem hzI, cellPairBallTransport, interiorIndicator_of_mem hzI]
      ring
    · rw [Set.indicator_of_notMem hzI, cellPairBallTransport, interiorIndicator_of_notMem hzI]
      ring
  simp_rw [hz]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfrontL, mul_assoc,
    ENNReal.inv_mul_cancel hposL.ne' hfinL.ne, mul_one]

theorem lintegral_cellPairBallTransport_source (K L : CompactCell) (t d : ℝ≥0∞) (z : Plane)
    (hfrontK : volume (frontier (K : Set Plane)) = 0) :
    (∫⁻ w : Plane, cellPairBallTransport K L t d w z ∂volume)
      = interiorIndicator L z * t * d * (volume (L : Set Plane))⁻¹ *
        volume (K : Set Plane) := by
  have hI : MeasurableSet (interior (K : Set Plane)) := isOpen_interior.measurableSet
  have hw : ∀ w : Plane, cellPairBallTransport K L t d w z
      = Set.indicator (interior (K : Set Plane))
        (fun _ => interiorIndicator L z * t * d * (volume (L : Set Plane))⁻¹) w := by
    intro w
    by_cases hwI : w ∈ interior (K : Set Plane)
    · rw [Set.indicator_of_mem hwI, cellPairBallTransport, interiorIndicator_of_mem hwI]
      ring
    · rw [Set.indicator_of_notMem hwI, cellPairBallTransport, interiorIndicator_of_notMem hwI]
      ring
  simp_rw [hw]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfrontK]

theorem lintegral_ballTransport_outgoing (k : ℕ) (Q : SlotObservable) (p : Env × Grid)
    (w : Plane) :
    (∫⁻ z : Plane, ballTransport k Q p w z ∂volume)
      = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          interiorIndicator ((decode p.1).cell v) w * reach p.1.val.2 k v.val v'.val *
            Q.toFun p v'.val := by
  have hgeom := decode_geometry p.1
  have hmeas : ∀ v v' : Vertex p.1.val, Measurable fun z : Plane =>
      cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
        (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z := by
    intro v v'
    have hEq : (fun z : Plane => cellPairBallTransport ((decode p.1).cell v)
          ((decode p.1).cell v') (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z)
        = fun z : Plane =>
          (interiorIndicator ((decode p.1).cell v) w * reach p.1.val.2 k v.val v'.val *
              Q.toFun p v'.val *
              (volume ((decode p.1).cell v' : Set Plane))⁻¹) *
            interiorIndicator ((decode p.1).cell v') z := by
      funext z
      simp only [cellPairBallTransport]
      ring
    rw [hEq]
    refine measurable_const.mul ?_
    show Measurable (Set.indicator (interior ((decode p.1).cell v' : Set Plane))
      (fun _ => (1 : ℝ≥0∞)))
    exact measurable_const.indicator isOpen_interior.measurableSet
  calc (∫⁻ z : Plane, ballTransport k Q p w z ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z ∂volume :=
        lintegral_congr fun z => ballTransport_eq_tsum_vertex k Q p w z
    _ = ∑' v : Vertex p.1.val, ∫⁻ z : Plane, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z ∂volume :=
        lintegral_tsum fun v => (Measurable.ennreal_tsum fun v' => hmeas v v').aemeasurable
    _ = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val, ∫⁻ z : Plane,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z ∂volume :=
        tsum_congr fun v => lintegral_tsum fun v' => (hmeas v v').aemeasurable
    _ = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          interiorIndicator ((decode p.1).cell v) w * reach p.1.val.2 k v.val v'.val *
            Q.toFun p v'.val :=
        tsum_congr fun v => tsum_congr fun v' =>
          lintegral_cellPairBallTransport_target _ _ _ _ _ (hgeom.2.2.1 v')
            (cellVolume_pos_lt_top (decode p.1) hgeom v').1
            (cellVolume_pos_lt_top (decode p.1) hgeom v').2

theorem lintegral_ballTransport_incoming (k : ℕ) (Q : SlotObservable) (p : Env × Grid)
    (z : Plane) :
    (∫⁻ w : Plane, ballTransport k Q p w z ∂volume)
      = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          interiorIndicator ((decode p.1).cell v') z * reach p.1.val.2 k v.val v'.val *
            Q.toFun p v'.val * (volume ((decode p.1).cell v' : Set Plane))⁻¹ *
            volume ((decode p.1).cell v : Set Plane) := by
  have hgeom := decode_geometry p.1
  have hmeas : ∀ v v' : Vertex p.1.val, Measurable fun w : Plane =>
      cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
        (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z := by
    intro v v'
    have hEq : (fun w : Plane => cellPairBallTransport ((decode p.1).cell v)
          ((decode p.1).cell v') (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z)
        = fun w : Plane =>
          (interiorIndicator ((decode p.1).cell v') z * reach p.1.val.2 k v.val v'.val *
              Q.toFun p v'.val *
              (volume ((decode p.1).cell v' : Set Plane))⁻¹) *
            interiorIndicator ((decode p.1).cell v) w := by
      funext w
      simp only [cellPairBallTransport]
      ring
    rw [hEq]
    refine measurable_const.mul ?_
    show Measurable (Set.indicator (interior ((decode p.1).cell v : Set Plane))
      (fun _ => (1 : ℝ≥0∞)))
    exact measurable_const.indicator isOpen_interior.measurableSet
  calc (∫⁻ w : Plane, ballTransport k Q p w z ∂volume)
      = ∫⁻ w : Plane, ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z ∂volume :=
        lintegral_congr fun w => ballTransport_eq_tsum_vertex k Q p w z
    _ = ∑' v : Vertex p.1.val, ∫⁻ w : Plane, ∑' v' : Vertex p.1.val,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z ∂volume :=
        lintegral_tsum fun v => (Measurable.ennreal_tsum fun v' => hmeas v v').aemeasurable
    _ = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val, ∫⁻ w : Plane,
          cellPairBallTransport ((decode p.1).cell v) ((decode p.1).cell v')
            (reach p.1.val.2 k v.val v'.val) (Q.toFun p v'.val) w z ∂volume :=
        tsum_congr fun v => lintegral_tsum fun v' => (hmeas v v').aemeasurable
    _ = ∑' v : Vertex p.1.val, ∑' v' : Vertex p.1.val,
          interiorIndicator ((decode p.1).cell v') z * reach p.1.val.2 k v.val v'.val *
            Q.toFun p v'.val * (volume ((decode p.1).cell v' : Set Plane))⁻¹ *
            volume ((decode p.1).cell v : Set Plane) :=
        tsum_congr fun v => tsum_congr fun v' =>
          lintegral_cellPairBallTransport_source _ _ _ _ _ (hgeom.2.2.1 v)

/-! ### The two rooted observables -/

/-- The **ball sum** at the origin root: `∑_{v : d_G(H_0,v) ≤ k} f(v)`. -/
noncomputable def rootedBallSum (k : ℕ) (Q : SlotObservable) (p : Env × Grid) : ℝ≥0∞ :=
  (RootDensities.rootAt (decode p.1) 0).elim 0 fun r =>
    ∑' v : Vertex p.1.val, reach p.1.val.2 k r.val v.val * Q.toFun p v.val

/-- The **root value** `f(H_0)`. -/
noncomputable def rootedValue (Q : SlotObservable) (p : Env × Grid) : ℝ≥0∞ :=
  (RootDensities.rootAt (decode p.1) 0).elim 0 fun r => Q.toFun p r.val

/-- The **ball-to-root area ratio** `W_k = (∑_{u : d_G(u,H_0) ≤ k} a_u) / a_{H_0}`.  It is a
purely geometric observable of the environment: no field and no grid mark enter. -/
noncomputable def rootedBallAreaRatio (k : ℕ) (e : Env) : ℝ≥0∞ :=
  (RootDensities.rootAt (decode e) 0).elim 0 fun r =>
    (∑' v : Vertex e.val,
      reach e.val.2 k v.val r.val * volume ((decode e).cell v : Set Plane)) /
        volume ((decode e).cell r : Set Plane)

theorem lintegral_ballTransport_outgoing_eq_rooted (k : ℕ) (Q : SlotObservable)
    (p : Env × Grid) (hp : (0 : Plane) ∉ RootDensities.boundaryMask (decode p.1)) :
    (∫⁻ z : Plane, ballTransport k Q p 0 z ∂volume) = rootedBallSum k Q p := by
  have hgeom := decode_geometry p.1
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode p.1) hgeom hp
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode p.1) hgeom hp
  have hone : interiorIndicator ((decode p.1).cell v₀) 0 = 1 := interiorIndicator_of_mem hint
  rw [lintegral_ballTransport_outgoing k Q p 0]
  rw [tsum_eq_single v₀ ?_]
  · simp only [rootedBallSum, hv₀, Option.elim]
    exact tsum_congr fun v' => by rw [hone, one_mul]
  · intro v hv
    have hnot : (0 : Plane) ∉ interior ((decode p.1).cell v : Set Plane) := by
      intro hmem
      exact hv (huniq.unique hmem hint)
    refine ENNReal.tsum_eq_zero.mpr fun v' => ?_
    rw [interiorIndicator_of_notMem hnot]
    simp

theorem lintegral_ballTransport_incoming_eq_rooted (k : ℕ) (Q : SlotObservable)
    (p : Env × Grid) (hp : (0 : Plane) ∉ RootDensities.boundaryMask (decode p.1)) :
    (∫⁻ w : Plane, ballTransport k Q p w 0 ∂volume)
      = rootedValue Q p * rootedBallAreaRatio k p.1 := by
  have hgeom := decode_geometry p.1
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode p.1) hgeom hp
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode p.1) hgeom hp
  have hone : interiorIndicator ((decode p.1).cell v₀) 0 = 1 := interiorIndicator_of_mem hint
  have hinner : ∀ v : Vertex p.1.val,
      (∑' v' : Vertex p.1.val, interiorIndicator ((decode p.1).cell v') 0 *
          reach p.1.val.2 k v.val v'.val * Q.toFun p v'.val *
          (volume ((decode p.1).cell v' : Set Plane))⁻¹ *
          volume ((decode p.1).cell v : Set Plane))
        = (reach p.1.val.2 k v.val v₀.val * volume ((decode p.1).cell v : Set Plane)) *
          (Q.toFun p v₀.val * (volume ((decode p.1).cell v₀ : Set Plane))⁻¹) := by
    intro v
    rw [tsum_eq_single v₀ ?_]
    · rw [hone, one_mul]; ring
    · intro v' hv'
      have hnot : (0 : Plane) ∉ interior ((decode p.1).cell v' : Set Plane) := by
        intro hmem
        exact hv' (huniq.unique hmem hint)
      rw [interiorIndicator_of_notMem hnot]
      simp
  rw [lintegral_ballTransport_incoming k Q p 0, tsum_congr hinner, ENNReal.tsum_mul_right]
  simp only [rootedValue, rootedBallAreaRatio, hv₀, Option.elim, div_eq_mul_inv]
  ring

/-! ### The re-rooting identity -/

/-- **The re-rooting identity.**  For every scale-invariant slot observable and every
combinatorial radius `k`, the expected ball sum at the origin root equals the expectation of
the root value against the ball-to-root area ratio:

`E[∑_{v ∈ B(H_0,k)} f(v)] = E[f(H_0) · W_k]`.

The only probabilistic input is the manuscript's own mass-transport hypothesis
`EnvironmentLaws.MassTransport ν` (`s:eq:MTP`); the grid marks are handled by averaging, as
the manuscript prescribes at tex:286. -/
theorem lintegral_rootedBallSum_eq (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (k : ℕ) (Q : SlotObservable) :
    (∫⁻ p : Env × Grid, rootedBallSum k Q p ∂(ν.prod gridMeasure))
      = ∫⁻ p : Env × Grid, rootedValue Q p * rootedBallAreaRatio k p.1
          ∂(ν.prod gridMeasure) := by
  have hgrid : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmask : ∀ᵐ p : Env × Grid ∂(ν.prod gridMeasure),
      (0 : Plane) ∉ RootDensities.boundaryMask (decode p.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := gridMeasure)).tendsto_ae.eventually
      (ae_notMem_boundaryMask_of_massTransport ν hν)
  have hout : (∫⁻ p : Env × Grid, ∫⁻ z : Plane, ballTransport k Q p 0 z ∂volume
        ∂(ν.prod gridMeasure))
      = ∫⁻ p : Env × Grid, rootedBallSum k Q p ∂(ν.prod gridMeasure) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hmask] with p hp
    exact lintegral_ballTransport_outgoing_eq_rooted k Q p hp
  have hin : (∫⁻ p : Env × Grid, ∫⁻ z : Plane, ballTransport k Q p z 0 ∂volume
        ∂(ν.prod gridMeasure))
      = ∫⁻ p : Env × Grid, rootedValue Q p * rootedBallAreaRatio k p.1
          ∂(ν.prod gridMeasure) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hmask] with p hp
    exact lintegral_ballTransport_incoming_eq_rooted k Q p hp
  exact hout.symm.trans ((markedMassTransport_ballTransport ν hν k Q).trans hin)

/-! ### The ball comparison -/

/-- The ball sum dominates the sum over the graph ball `B(r, k+1)` of the manuscript's
neighbourhood error: `reach` is at least `1` there. -/
theorem le_rootedBallSum_of_mem_ball (k : ℕ) (Q : SlotObservable) (p : Env × Grid)
    {r : Vertex p.1.val} (hr : RootDensities.rootAt (decode p.1) 0 = some r)
    {v : Vertex p.1.val}
    (hv : v ∈ (decode p.1).graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞)) :
    Q.toFun p v.val ≤ rootedBallSum k Q p := by
  have hone : 1 ≤ reach p.1.val.2 k r.val v.val := one_le_reach_of_mem_ball p.1 r k hv
  have hterm : Q.toFun p v.val ≤ reach p.1.val.2 k r.val v.val * Q.toFun p v.val := by
    calc Q.toFun p v.val = 1 * Q.toFun p v.val := (one_mul _).symm
      _ ≤ reach p.1.val.2 k r.val v.val * Q.toFun p v.val := mul_le_mul' hone le_rfl
  refine hterm.trans ?_
  simp only [rootedBallSum, hr, Option.elim]
  exact ENNReal.le_tsum (f := fun x : Vertex p.1.val =>
    reach p.1.val.2 k r.val x.val * Q.toFun p x.val) v

end ReflectedGMS.BallEnergyReRooting
