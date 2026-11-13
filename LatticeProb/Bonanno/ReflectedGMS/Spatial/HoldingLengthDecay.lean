/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.HoldingLengthDecay at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClocks

/-!
# Exact holding lengths are subquadratic: `a_H / π_H ≤ C + δ dist(0, H)²`

The exact area-clock walk holds at a cell `H` for exactly `h_H = a_H / π_H`
(`AreaClocks.areaHoldingLength`).  The exact holding mesh (P3) needs, for almost every
environment, that no cell within distance `R` of the origin has `h_H` of order `R²`.  This file
proves the environment half:

```
  ∀ δ > 0, ∃ C, ∀ H,   a_H / π_H ≤ C + δ · dist(0, H)²          (exists_areaHoldingLength_bound)
```

for almost every environment, from `MassTransport ν` and the manuscript's (FE) moment alone.

## Why the holding length is controlled by (FE)

(FE) is `𝔼[(d²/a)(π + π*)(H_0)] < ∞`, and the reciprocal conductance `π* = ∑ c⁻¹` is part of it.
Every vertex has a neighbour (the cell graph is connected and has at least two cells), so
`π_H ≥ c(H, H')` and `π*_H ≥ c(H, H')⁻¹`, whence `1/π_H ≤ π*_H`.  With `a_H ≤ |B_1| d_H²`,

```
  h_H = a_H / π_H ≤ |B_1| d_H² π*_H ≤ |B_1| (d_H m_H)²,     m_H := √(1 + π*_H)      (areaHoldingLength_le)
```

## The mass transport

`LargeCellDiameterDecay` counts the cells whose `k d_H`-neighbourhood contains the origin.  Here
the neighbourhood radius is `k d_H m_H`, which is again exactly similarity covariant (diameters
scale, conductances do not), so

`T(𝓗, w, z) = ∑_H 1_{w ∈ int H} 1_{dist(z, H) ≤ k d_H m_H} / a_H`

is an honest `MassTransportKernel` (`resistanceNeighborhoodTransportKernel`), read through the
code slots for measurability (`RootedFiniteEnergyDensityMeasurable.slotResistanceMass`).  Its
outgoing mass at the origin is `|N(H_0)| / a_{H_0} ≤ |B_1| (k m + 1)² d²/a ≤ 4 (k² + 1) |B_1| ρ_FE(0)`
(AM–GM `π + π* ≥ 2`, `LargeCellDiameterDecay.two_le_pi_add_piStar`), and its incoming mass is the
number of such cells.  So the count has finite expectation and is almost surely finite at every
integer `k` (`ae_finite_resistanceNear`).  A cell with `h_H > δ dist(0,H)²` lies in the family
with `k ≥ (|B_1|/δ)`, which gives the bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ReflectedGMS.HoldingLengthDecay

open Code EnvironmentLaws Spatial RootedFiniteEnergyDensityMeasurable

variable {V : Type*}

/-! ### The resistance multiplier -/

/-- `m_H = √(1 + π*_H)`, a similarity invariant of the cell. -/
noncomputable def resistanceMultiplier (F : IndexedCells V) (v : V) : ℝ :=
  Real.sqrt (1 + RootDensities.piStar F v)

theorem resistanceMultiplier_nonneg (F : IndexedCells V) (v : V) :
    0 ≤ resistanceMultiplier F v :=
  Real.sqrt_nonneg _

theorem resistanceMultiplier_sq (F : IndexedCells V) (v : V) :
    resistanceMultiplier F v ^ 2 = 1 + RootDensities.piStar F v :=
  Real.sq_sqrt (by linarith [Spatial.piStar_nonneg F v])

/-! ### Joint measurability with a variable scale -/

/-- The cell transport of `LargeCellDiameterDecay` is jointly measurable in the scale, the cell
and both points. -/
theorem measurable_cellScaledNeighborhoodTransport_comp {α : Type*} [MeasurableSpace α]
    {kf : α → ℝ} {Kf : α → CompactCell} {wf zf : α → Plane}
    (hk : Measurable kf) (hK : Measurable Kf) (hw : Measurable wf) (hz : Measurable zf) :
    Measurable fun a => cellScaledNeighborhoodTransport (kf a) (Kf a) (wf a) (zf a) := by
  have hS1 : MeasurableSet {a | wf a ∈ interior (Kf a : Set Plane)} :=
    (hK.prodMk hw) measurableSet_cellInterior
  have hinf : Measurable fun a => Metric.infDist (zf a) (Kf a : Set Plane) := by
    have hc : Continuous fun p : Plane × CompactCell => Metric.infDist p.1 (p.2 : Set Plane) :=
      (NonemptyCompacts.lipschitz_infDist (α := Plane)).continuous
    have hm : Measurable fun p : Plane × CompactCell => Metric.infDist p.1 (p.2 : Set Plane) :=
      hc.measurable
    have h2 : Measurable ((fun p : Plane × CompactCell => Metric.infDist p.1 (p.2 : Set Plane)) ∘
        fun a => (zf a, Kf a)) := hm.comp (hz.prodMk hK)
    rw [Function.comp_def] at h2
    exact h2
  have hS2 : MeasurableSet {a | Metric.infDist (zf a) (Kf a : Set Plane)
      ≤ kf a * Metric.diam (Kf a : Set Plane)} :=
    measurableSet_le hinf (hk.mul (measurable_cellDiam.comp hK))
  have hEq : (fun a => cellScaledNeighborhoodTransport (kf a) (Kf a) (wf a) (zf a))
      = ({a | wf a ∈ interior (Kf a : Set Plane)} ∩ {a | Metric.infDist (zf a) (Kf a : Set Plane)
          ≤ kf a * Metric.diam (Kf a : Set Plane)}).indicator
          (fun a => (volume (Kf a : Set Plane))⁻¹) := by
    funext a
    by_cases hwa : wf a ∈ interior (Kf a : Set Plane)
    · by_cases hza : zf a ∈ cellScaledNeighborhood (kf a) (Kf a)
      · have hmem : a ∈ {a | wf a ∈ interior (Kf a : Set Plane)} ∩
            {a | Metric.infDist (zf a) (Kf a : Set Plane)
              ≤ kf a * Metric.diam (Kf a : Set Plane)} := ⟨hwa, hza⟩
        rw [cellScaledNeighborhoodTransport_of_mem _ _ hwa hza, Set.indicator_of_mem hmem]
      · have hmem : a ∉ {a | wf a ∈ interior (Kf a : Set Plane)} ∩
            {a | Metric.infDist (zf a) (Kf a : Set Plane)
              ≤ kf a * Metric.diam (Kf a : Set Plane)} := fun h => hza h.2
        rw [cellScaledNeighborhoodTransport_of_notMem_neighborhood _ _ _ hza,
          Set.indicator_of_notMem hmem]
    · have hmem : a ∉ {a | wf a ∈ interior (Kf a : Set Plane)} ∩
          {a | Metric.infDist (zf a) (Kf a : Set Plane)
            ≤ kf a * Metric.diam (Kf a : Set Plane)} := fun h => hwa h.1
      rw [cellScaledNeighborhoodTransport_of_notMem_interior _ _ _ hwa,
        Set.indicator_of_notMem hmem]
  rw [hEq]
  exact (measurable_cellVolume.comp hK).inv.indicator (hS1.inter hS2)

/-! ### Slot level -/

/-- The slot form of `m_H`. -/
noncomputable def slotMultiplier (e : Env) (n : ℕ) : ℝ :=
  Real.sqrt (1 + (slotResistanceMass e n).toReal)

theorem measurable_slotMultiplier (n : ℕ) : Measurable fun e : Env => slotMultiplier e n :=
  Real.continuous_sqrt.measurable.comp
    (measurable_const.add (measurable_slotResistanceMass n).ennreal_toReal)

theorem slotMultiplier_eq (e : Env) (v : Vertex e.val) :
    slotMultiplier e v.val = resistanceMultiplier (decode e) v := by
  rw [slotMultiplier, resistanceMultiplier, ← ofReal_piStar_eq_slotResistanceMass,
    ENNReal.toReal_ofReal (Spatial.piStar_nonneg _ _)]

/-- The transport of one code slot; absent slots transport nothing. -/
noncomputable def slotResistanceTerm (k : ℝ) (n : ℕ) : Env × Plane × Plane → ℝ≥0∞ :=
  Set.indicator {p : Env × Plane × Plane | (p.1.val.1 n).isSome}
    (fun p => cellScaledNeighborhoodTransport (k * slotMultiplier p.1 n) (slotCell p.1 n)
      p.2.1 p.2.2)

theorem measurable_slotResistanceTerm (k : ℝ) (n : ℕ) :
    Measurable (slotResistanceTerm k n) := by
  have hslot : Measurable fun p : Env × Plane × Plane => p.1.val.1 n :=
    ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)).comp
      measurable_fst
  exact (measurable_cellScaledNeighborhoodTransport_comp
    (measurable_const.mul ((measurable_slotMultiplier n).comp measurable_fst))
    ((measurable_slotCell_env n).comp measurable_fst)
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)).indicator
    (hslot measurableSet_slotIsSome)

/-- The resistance-scaled neighbourhood transport on the trace environment space. -/
noncomputable def resistanceNeighborhoodTransport (k : ℝ) (p : Env × Plane × Plane) : ℝ≥0∞ :=
  ∑' n : ℕ, slotResistanceTerm k n p

theorem measurable_resistanceNeighborhoodTransport (k : ℝ) :
    Measurable (resistanceNeighborhoodTransport k) :=
  Measurable.ennreal_tsum fun n => measurable_slotResistanceTerm k n

theorem resistanceNeighborhoodTransport_eq_tsum_vertex (k : ℝ) (e : Env) (w z : Plane) :
    resistanceNeighborhoodTransport k (e, w, z)
      = ∑' v : Vertex e.val, cellScaledNeighborhoodTransport
          (k * resistanceMultiplier (decode e) v) ((decode e).cell v) w z := by
  have hsupp : Function.support (fun n : ℕ => slotResistanceTerm k n (e, w, z))
      ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    by_contra hnone
    have h0 : slotResistanceTerm k n (e, w, z) = 0 := by
      unfold slotResistanceTerm
      exact Set.indicator_of_notMem
        (show (e, w, z) ∉ {p : Env × Plane × Plane | (p.1.val.1 n).isSome} from hnone) _
    exact hn h0
  have hterm : ∀ v : Vertex e.val, slotResistanceTerm k v.val (e, w, z)
      = cellScaledNeighborhoodTransport (k * resistanceMultiplier (decode e) v)
          ((decode e).cell v) w z := by
    intro v
    unfold slotResistanceTerm
    rw [Set.indicator_of_mem
      (show (e, w, z) ∈ {p : Env × Plane × Plane | (p.1.val.1 v.val).isSome} from v.property)]
    simp only [slotMultiplier_eq e v, slotCell_eq_cell e v]
  calc resistanceNeighborhoodTransport k (e, w, z)
      = ∑' n : ℕ, slotResistanceTerm k n (e, w, z) := rfl
    _ = ∑' n : {n : ℕ | (e.val.1 n).isSome}, slotResistanceTerm k n.val (e, w, z) :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' v : Vertex e.val, cellScaledNeighborhoodTransport
          (k * resistanceMultiplier (decode e) v) ((decode e).cell v) w z := tsum_congr hterm

/-! ### Covariance and the kernel -/

/-- The reciprocal conductance mass is unchanged by a physical similarity. -/
theorem piStar_similarityRelabel {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' relabel)
    (v : Vertex e.val) :
    RootDensities.piStar (decode e') (relabel v) = RootDensities.piStar (decode e) v := by
  show (∑' w : Vertex e'.val, ((decode e').graph.c (relabel v) w)⁻¹)
      = ∑' w : Vertex e.val, ((decode e).graph.c v w)⁻¹
  rw [← Equiv.tsum_eq relabel fun w : Vertex e'.val => ((decode e').graph.c (relabel v) w)⁻¹]
  exact tsum_congr fun w => by rw [h.2 v w]

theorem resistanceNeighborhoodTransport_covariant (k s : ℝ) (u : Plane) (hs : 0 < s)
    (e e' : Env) (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    resistanceNeighborhoodTransport k (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * resistanceNeighborhoodTransport k (e, w, z) := by
  obtain ⟨relabel, hrel⟩ := hsim
  rw [resistanceNeighborhoodTransport_eq_tsum_vertex,
    resistanceNeighborhoodTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq relabel (fun v' : Vertex e'.val =>
      cellScaledNeighborhoodTransport (k * resistanceMultiplier (decode e') v')
        ((decode e').cell v') (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  have hm : resistanceMultiplier (decode e') (relabel v) = resistanceMultiplier (decode e) v := by
    rw [resistanceMultiplier, resistanceMultiplier, piStar_similarityRelabel hrel v]
  rw [hrel.1 v, hm, cellScaledNeighborhoodTransport_transformCell]

/-- The resistance-scaled neighbourhood transport as a `MassTransportKernel`. -/
noncomputable def resistanceNeighborhoodTransportKernel (k : ℝ) : MassTransportKernel where
  toFun := resistanceNeighborhoodTransport k
  measurable_toFun := measurable_resistanceNeighborhoodTransport k
  covariant := fun s u hs e e' hsim w z =>
    resistanceNeighborhoodTransport_covariant k s u hs e e' hsim w z

/-! ### Outgoing and incoming integrals -/

theorem lintegral_resistanceNeighborhoodTransport_outgoing (k : ℝ) (e : Env) (w : Plane) :
    (∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, w, z) ∂volume)
      = ∑' v : Vertex e.val,
          Set.indicator (interior ((decode e).cell v : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w *
            (volume (cellScaledNeighborhood (k * resistanceMultiplier (decode e) v)
                ((decode e).cell v)) /
              volume ((decode e).cell v : Set Plane)) := by
  calc (∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, w, z) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val, cellScaledNeighborhoodTransport
          (k * resistanceMultiplier (decode e) v) ((decode e).cell v) w z ∂volume :=
        lintegral_congr fun z => resistanceNeighborhoodTransport_eq_tsum_vertex k e w z
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane, cellScaledNeighborhoodTransport
          (k * resistanceMultiplier (decode e) v) ((decode e).cell v) w z ∂volume :=
        lintegral_tsum fun v =>
          (measurable_cellScaledNeighborhoodTransport_target _ _ w).aemeasurable
    _ = _ := tsum_congr fun v => lintegral_cellScaledNeighborhoodTransport_target _ _ _

theorem lintegral_resistanceNeighborhoodTransport_incoming (k : ℝ) (e : Env) (z : Plane) :
    (∫⁻ w : Plane, resistanceNeighborhoodTransport k (e, w, z) ∂volume)
      = ∑' v : Vertex e.val,
          Set.indicator (cellScaledNeighborhood (k * resistanceMultiplier (decode e) v)
            ((decode e).cell v)) (fun _ => (1 : ℝ≥0∞)) z := by
  have hgeom := decode_geometry e
  calc (∫⁻ w : Plane, resistanceNeighborhoodTransport k (e, w, z) ∂volume)
      = ∫⁻ w : Plane, ∑' v : Vertex e.val, cellScaledNeighborhoodTransport
          (k * resistanceMultiplier (decode e) v) ((decode e).cell v) w z ∂volume :=
        lintegral_congr fun w => resistanceNeighborhoodTransport_eq_tsum_vertex k e w z
    _ = ∑' v : Vertex e.val, ∫⁻ w : Plane, cellScaledNeighborhoodTransport
          (k * resistanceMultiplier (decode e) v) ((decode e).cell v) w z ∂volume :=
        lintegral_tsum fun v =>
          (measurable_cellScaledNeighborhoodTransport_source _ _ z).aemeasurable
    _ = _ := tsum_congr fun v => lintegral_cellScaledNeighborhoodTransport_source _ _ _
          (hgeom.2.2.1 v) (cellVolume_pos_lt_top (decode e) hgeom v).1
          (cellVolume_pos_lt_top (decode e) hgeom v).2

/-! ### The near-cell count and the rooted ratio -/

/-- The number of cells whose `k d_H m_H`-neighbourhood contains the point `z`. -/
noncomputable def resistanceNearCellCount (k : ℝ) (F : IndexedCells V) (z : Plane) : ℝ≥0∞ :=
  ∑' v : V, Set.indicator (cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v))
    (fun _ => (1 : ℝ≥0∞)) z

/-- The boundary-masked neighbourhood-to-area ratio of the rooted cell. -/
noncomputable def rootedResistanceAreaRatio (k : ℝ) (F : IndexedCells V) (z : Plane) :
    ℝ≥0∞ :=
  (RootDensities.rootAt F z).elim 0 fun v =>
    volume (cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v)) /
      volume (F.cell v : Set Plane)

theorem lintegral_resistanceNeighborhoodTransport_outgoing_eq_rooted (k : ℝ) (e : Env)
    (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    (∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, 0, z) ∂volume)
      = rootedResistanceAreaRatio k (decode e) 0 := by
  have hgeom := decode_geometry e
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom he
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom he
  rw [lintegral_resistanceNeighborhoodTransport_outgoing k e 0]
  rw [tsum_eq_single v₀ ?_]
  · rw [Set.indicator_of_mem hint, one_mul]
    simp [rootedResistanceAreaRatio, hv₀]
  · intro v hv
    have hnot : (0 : Plane) ∉ interior ((decode e).cell v : Set Plane) := by
      intro hmem
      exact hv (huniq.unique hmem hint)
    rw [Set.indicator_of_notMem hnot, zero_mul]

/-- Mass transport: the expected count is the expected rooted ratio. -/
theorem lintegral_resistanceNearCellCount_eq_rootedRatio (k : ℝ) (ν : Measure Env)
    (hν : MassTransport ν) :
    (∫⁻ e : Env, resistanceNearCellCount k (decode e) 0 ∂ν)
      = ∫⁻ e : Env, rootedResistanceAreaRatio k (decode e) 0 ∂ν := by
  have hmt : (∫⁻ e : Env, ∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, z, 0) ∂volume ∂ν :=
    hν (resistanceNeighborhoodTransportKernel k)
  have hout : (∫⁻ e : Env, ∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, rootedResistanceAreaRatio k (decode e) 0 ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_notMem_boundaryMask_of_massTransport ν hν] with e he
    exact lintegral_resistanceNeighborhoodTransport_outgoing_eq_rooted k e he
  have hin : (∫⁻ e : Env, ∫⁻ z : Plane, resistanceNeighborhoodTransport k (e, z, 0) ∂volume ∂ν)
      = ∫⁻ e : Env, resistanceNearCellCount k (decode e) 0 ∂ν :=
    lintegral_congr fun e => lintegral_resistanceNeighborhoodTransport_incoming k e 0
  exact hin.symm.trans (hmt.symm.trans hout)

/-- The rooted ratio is dominated by the rooted (FE) density. -/
theorem rootedResistanceAreaRatio_le {k : ℝ} (hk : 0 ≤ k) [Countable V] [Nontrivial V]
    (F : IndexedCells V) (hF : Geometry F) (z : Plane) :
    rootedResistanceAreaRatio k F z
      ≤ ENNReal.ofReal (4 * (k ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1) *
          RootDensities.rootedFiniteEnergyDensity F z := by
  cases hroot : RootDensities.rootAt F z with
  | none => simp [rootedResistanceAreaRatio, hroot]
  | some v =>
      simp only [rootedResistanceAreaRatio, RootDensities.rootedFiniteEnergyDensity,
        RootDensities.finiteEnergyDensity, hroot, Option.elim]
      have hm0 : 0 ≤ resistanceMultiplier F v := resistanceMultiplier_nonneg F v
      have hm2 : resistanceMultiplier F v ^ 2 = 1 + RootDensities.piStar F v :=
        resistanceMultiplier_sq F v
      have hpi : 0 ≤ RootDensities.pi F v := F.graph.pi_nonneg v
      have hpis : 0 ≤ RootDensities.piStar F v := Spatial.piStar_nonneg F v
      have h2 := two_le_pi_add_piStar F hF v
      have hreal : (k * resistanceMultiplier F v + 1) ^ 2 * Metric.diam (F.cell v : Set Plane) ^ 2
          ≤ 4 * (k ^ 2 + 1) * (Metric.diam (F.cell v : Set Plane) ^ 2 *
            (RootDensities.pi F v + RootDensities.piStar F v)) := by
        have hd2 : 0 ≤ Metric.diam (F.cell v : Set Plane) ^ 2 := sq_nonneg _
        have h1 : (k * resistanceMultiplier F v + 1) ^ 2
            ≤ 2 * (k ^ 2 * resistanceMultiplier F v ^ 2) + 2 := by
          nlinarith [sq_nonneg (k * resistanceMultiplier F v - 1)]
        have h3 : 2 * (k ^ 2 * resistanceMultiplier F v ^ 2) + 2
            ≤ 4 * (k ^ 2 + 1) * (RootDensities.pi F v + RootDensities.piStar F v) := by
          rw [hm2]
          nlinarith [sq_nonneg k]
        have h4 : (k * resistanceMultiplier F v + 1) ^ 2
            ≤ 4 * (k ^ 2 + 1) * (RootDensities.pi F v + RootDensities.piStar F v) :=
          h1.trans h3
        nlinarith
      have hvol := cellVolume_pos_lt_top F hF v
      have harea : ENNReal.ofReal (StatementIngredients.cellArea F v)
          = volume (F.cell v : Set Plane) := by
        rw [StatementIngredients.cellArea, ENNReal.ofReal_toReal hvol.2.ne]
      rw [harea]
      have hX : ENNReal.ofReal ((k * resistanceMultiplier F v + 1) ^ 2 *
            Metric.diam (F.cell v : Set Plane) ^ 2)
          ≤ ENNReal.ofReal (4 * (k ^ 2 + 1)) *
            (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              (ENNReal.ofReal (RootDensities.pi F v) +
                ENNReal.ofReal (RootDensities.piStar F v))) := by
        rw [← ENNReal.ofReal_add hpi hpis, ← ENNReal.ofReal_mul (sq_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hreal
      have hk' : (0 : ℝ) ≤ k * resistanceMultiplier F v := mul_nonneg hk hm0
      have hN := volume_cellScaledNeighborhood_le hk' (F.cell v)
      calc volume (cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v)) /
            volume (F.cell v : Set Plane)
          ≤ (ENNReal.ofReal ((k * resistanceMultiplier F v + 1) ^ 2 *
                Metric.diam (F.cell v : Set Plane) ^ 2) *
              volume (Metric.ball (0 : Plane) 1)) / volume (F.cell v : Set Plane) :=
            ENNReal.div_le_div_right hN _
        _ ≤ (ENNReal.ofReal (4 * (k ^ 2 + 1)) *
              (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
                (ENNReal.ofReal (RootDensities.pi F v) +
                  ENNReal.ofReal (RootDensities.piStar F v))) *
              volume (Metric.ball (0 : Plane) 1)) / volume (F.cell v : Set Plane) :=
            ENNReal.div_le_div_right (mul_le_mul' hX le_rfl) _
        _ = ENNReal.ofReal (4 * (k ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1) *
              (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
                  volume (F.cell v : Set Plane) *
                (ENNReal.ofReal (RootDensities.pi F v) +
                  ENNReal.ofReal (RootDensities.piStar F v))) := by
            simp only [div_eq_mul_inv]
            ring

/-- Under mass transport, the expected near-cell count is bounded by the (FE) moment. -/
theorem lintegral_resistanceNearCellCount_le {k : ℝ} (hk : 0 ≤ k) (ν : Measure Env)
    (hν : MassTransport ν) :
    (∫⁻ e : Env, resistanceNearCellCount k (decode e) 0 ∂ν)
      ≤ ENNReal.ofReal (4 * (k ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1) *
          ∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν := by
  have hconst : ENNReal.ofReal (4 * (k ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  rw [lintegral_resistanceNearCellCount_eq_rootedRatio k ν hν]
  calc (∫⁻ e : Env, rootedResistanceAreaRatio k (decode e) 0 ∂ν)
      ≤ ∫⁻ e : Env, ENNReal.ofReal (4 * (k ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1) *
          RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν := by
        refine lintegral_mono fun e => ?_
        have : Nontrivial (Vertex e.val) :=
          nontrivial_of_geometry (decode e) (decode_geometry e)
        exact rootedResistanceAreaRatio_le hk (decode e) (decode_geometry e) 0
    _ = ENNReal.ofReal (4 * (k ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1) *
          ∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν :=
        lintegral_const_mul' _ _ hconst

/-- A finite count is a finite family of cells. -/
theorem finite_of_resistanceNearCellCount_ne_top (k : ℝ) (F : IndexedCells V) (z : Plane)
    (h : resistanceNearCellCount k F z ≠ ∞) :
    {v : V | z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v)}.Finite := by
  by_contra hcon
  have hinf : {v : V | z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v)
      (F.cell v)}.Infinite := hcon
  have : Infinite {v : V | z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v)
      (F.cell v)} := hinf.to_subtype
  have hsupp : Function.support
      (fun v : V => Set.indicator (cellScaledNeighborhood (k * resistanceMultiplier F v)
        (F.cell v)) (fun _ => (1 : ℝ≥0∞)) z)
      ⊆ {v : V | z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v)} := by
    intro v hv
    by_contra hz
    have hz' : z ∉ cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v) := hz
    exact hv (Set.indicator_of_notMem hz' _)
  refine h ?_
  calc resistanceNearCellCount k F z
      = ∑' v : {v : V | z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v)},
          Set.indicator (cellScaledNeighborhood (k * resistanceMultiplier F v.1) (F.cell v.1))
            (fun _ => (1 : ℝ≥0∞)) z :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' _ : {v : V | z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v) (F.cell v)},
          (1 : ℝ≥0∞) := by
        refine tsum_congr fun v => ?_
        have hmem : z ∈ cellScaledNeighborhood (k * resistanceMultiplier F v.1) (F.cell v.1) :=
          v.2
        exact Set.indicator_of_mem hmem _
    _ = ∞ := ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- **Almost surely, at every integer scale `n`, only finitely many cells have their
`n d_H m_H`-neighbourhood containing the origin.**  From `MassTransport ν` and (FE) alone. -/
theorem ae_finite_resistanceNear (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, ∀ n : ℕ,
      {v : Vertex e.val | (0 : Plane) ∈ cellScaledNeighborhood
        ((n : ℝ) * resistanceMultiplier (decode e) v) ((decode e).cell v)}.Finite := by
  rw [ae_all_iff]
  intro n
  have hk : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmeas : Measurable fun e : Env => resistanceNearCellCount (n : ℝ) (decode e) 0 := by
    have hinc : Measurable fun e : Env =>
        ∫⁻ z : Plane, resistanceNeighborhoodTransport (n : ℝ) (e, z, 0) ∂volume :=
      (resistanceNeighborhoodTransportKernel (n : ℝ)).measurable_incoming.lintegral_prod_right'
    have hEq : (fun e : Env => ∫⁻ z : Plane,
          resistanceNeighborhoodTransport (n : ℝ) (e, z, 0) ∂volume)
        = fun e : Env => resistanceNearCellCount (n : ℝ) (decode e) 0 :=
      funext fun e => lintegral_resistanceNeighborhoodTransport_incoming (n : ℝ) e 0
    rwa [hEq] at hinc
  have hbound := lintegral_resistanceNearCellCount_le hk ν hν
  have hconst : ENNReal.ofReal (4 * ((n : ℝ) ^ 2 + 1)) * volume (Metric.ball (0 : Plane) 1)
      ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hfin : (∫⁻ e : Env, resistanceNearCellCount (n : ℝ) (decode e) 0 ∂ν) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hconst hFE) hbound
  filter_upwards [ae_lt_top hmeas hfin] with e he
  exact finite_of_resistanceNearCellCount_ne_top (n : ℝ) (decode e) 0 he.ne

/-! ### The deterministic holding bound -/

/-- **`h_H ≤ |B_1| (d_H m_H)²`**: the exact holding length is controlled by the cell diameter
and the reciprocal conductance. -/
theorem areaHoldingLength_le [Countable V] [Nontrivial V] (F : IndexedCells V)
    (hF : Geometry F) (v : V) :
    AreaClocks.areaHoldingLength F v
      ≤ (volume (Metric.ball (0 : Plane) 1)).toReal *
          (Metric.diam (F.cell v : Set Plane) * resistanceMultiplier F v) ^ 2 := by
  obtain ⟨w, hw⟩ := F.graph.exists_adj_of_connected (hF.2.2.2.2.2.1) v
  have hcpos : 0 < F.graph.c v w := hw
  have h1 : F.graph.c v w ≤ F.graph.pi v := F.graph.c_le_pi v w
  have h2 : (F.graph.c v w)⁻¹ ≤ RootDensities.piStar F v :=
    (summable_inv_conductance F hF v).le_tsum w
      fun b _ => inv_nonneg.mpr (F.graph.c_nonneg v b)
  have hpipos : 0 < F.graph.pi v := hcpos.trans_le h1
  have hinvpi : (F.graph.pi v)⁻¹ ≤ RootDensities.piStar F v :=
    (inv_anti₀ hcpos h1).trans h2
  obtain ⟨x, hx⟩ := (F.cell v).nonempty
  have hd0 : 0 ≤ Metric.diam (F.cell v : Set Plane) := Metric.diam_nonneg
  have hsub : (F.cell v : Set Plane) ⊆
      Metric.closedBall x (Metric.diam (F.cell v : Set Plane)) := fun y hy =>
    Metric.mem_closedBall.2 (Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hy hx)
  have hball := Measure.addHaar_closedBall (volume : Measure Plane) x hd0
  rw [finrank_euclideanSpace_fin] at hball
  have hvolle : volume (F.cell v : Set Plane)
      ≤ ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
          volume (Metric.ball (0 : Plane) 1) := by
    rw [← hball]
    exact measure_mono hsub
  have harea : StatementIngredients.cellArea F v
      ≤ Metric.diam (F.cell v : Set Plane) ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) hvolle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at h
  have hm2 := resistanceMultiplier_sq F v
  have hpis := Spatial.piStar_nonneg F v
  have ha0 : 0 ≤ StatementIngredients.cellArea F v := ENNReal.toReal_nonneg
  have hβ : 0 ≤ (volume (Metric.ball (0 : Plane) 1)).toReal := ENNReal.toReal_nonneg
  have hmul : StatementIngredients.cellArea F v * (F.graph.pi v)⁻¹
      ≤ (Metric.diam (F.cell v : Set Plane) ^ 2 * (volume (Metric.ball (0 : Plane) 1)).toReal) *
          RootDensities.piStar F v :=
    mul_le_mul harea hinvpi (inv_nonneg.2 hpipos.le) (by positivity)
  unfold AreaClocks.areaHoldingLength
  rw [div_eq_mul_inv, mul_pow, hm2]
  have hd2 : 0 ≤ Metric.diam (F.cell v : Set Plane) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hd2 hβ]

/-- **The deterministic holding bound from the finite near-cell families**: for every `δ > 0`
some finite `C` bounds `h_H − δ dist(0, H)²` over all cells. -/
theorem exists_areaHoldingLength_bound [Countable V] [Nontrivial V] (F : IndexedCells V)
    (hF : Geometry F)
    (hfin : ∀ n : ℕ, {v : V | (0 : Plane) ∈ cellScaledNeighborhood
      ((n : ℝ) * resistanceMultiplier F v) (F.cell v)}.Finite)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ v : V, AreaClocks.areaHoldingLength F v
      ≤ C + δ * Metric.infDist (0 : Plane) (F.cell v : Set Plane) ^ 2 := by
  set β := (volume (Metric.ball (0 : Plane) 1)).toReal with hβdef
  have hβ : 0 ≤ β := ENNReal.toReal_nonneg
  obtain ⟨n, hn⟩ : ∃ n : ℕ, β / δ ≤ n := ⟨⌈β / δ⌉₊, Nat.le_ceil _⟩
  have hnn : ((n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith
  have hβn : β ≤ δ * (n : ℝ) ^ 2 := by
    have h' : β ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).1 hn
    nlinarith
  have hS := hfin n
  have hh0 : ∀ u, 0 ≤ AreaClocks.areaHoldingLength F u := fun u =>
    div_nonneg ENNReal.toReal_nonneg (F.graph.pi_nonneg u)
  refine ⟨∑ u ∈ hS.toFinset, AreaClocks.areaHoldingLength F u, fun v => ?_⟩
  have hinf0 : 0 ≤ δ * Metric.infDist (0 : Plane) (F.cell v : Set Plane) ^ 2 := by positivity
  by_cases hv : (0 : Plane) ∈ cellScaledNeighborhood ((n : ℝ) * resistanceMultiplier F v)
      (F.cell v)
  · have hmem : v ∈ hS.toFinset := hS.mem_toFinset.2 hv
    have hle : AreaClocks.areaHoldingLength F v
        ≤ ∑ u ∈ hS.toFinset, AreaClocks.areaHoldingLength F u :=
      Finset.single_le_sum (fun u _ => hh0 u) hmem
    linarith
  · have hv' : ¬ (Metric.infDist (0 : Plane) (F.cell v : Set Plane)
        ≤ (n : ℝ) * resistanceMultiplier F v * Metric.diam (F.cell v : Set Plane)) := hv
    have hlt := not_le.1 hv'
    have hb := areaHoldingLength_le F hF v
    have hm0 := resistanceMultiplier_nonneg F v
    have hd0 : 0 ≤ Metric.diam (F.cell v : Set Plane) := Metric.diam_nonneg
    have hX0 : 0 ≤ (n : ℝ) * resistanceMultiplier F v * Metric.diam (F.cell v : Set Plane) := by
      positivity
    have hsq : ((n : ℝ) * resistanceMultiplier F v * Metric.diam (F.cell v : Set Plane)) ^ 2
        ≤ Metric.infDist (0 : Plane) (F.cell v : Set Plane) ^ 2 := by
      nlinarith
    have hDM : 0 ≤ (Metric.diam (F.cell v : Set Plane) * resistanceMultiplier F v) ^ 2 :=
      sq_nonneg _
    have hchain : β * (Metric.diam (F.cell v : Set Plane) * resistanceMultiplier F v) ^ 2
        ≤ δ * Metric.infDist (0 : Plane) (F.cell v : Set Plane) ^ 2 := by
      calc β * (Metric.diam (F.cell v : Set Plane) * resistanceMultiplier F v) ^ 2
          ≤ δ * (n : ℝ) ^ 2 * (Metric.diam (F.cell v : Set Plane) * resistanceMultiplier F v) ^ 2 :=
            mul_le_mul_of_nonneg_right hβn hDM
        _ = δ * ((n : ℝ) * resistanceMultiplier F v * Metric.diam (F.cell v : Set Plane)) ^ 2 := by
            ring
        _ ≤ δ * Metric.infDist (0 : Plane) (F.cell v : Set Plane) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hδ.le
    have hsum0 : 0 ≤ ∑ u ∈ hS.toFinset, AreaClocks.areaHoldingLength F u :=
      Finset.sum_nonneg fun u _ => hh0 u
    linarith

/-- **Almost surely, the exact holding lengths are subquadratic in the distance to the
origin**: for every `δ > 0` a finite `C` with `h_H ≤ C + δ dist(0, H)²` for every cell. -/
theorem ae_exists_areaHoldingLength_bound (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ v : Vertex e.val,
      AreaClocks.areaHoldingLength (decode e) v
        ≤ C + δ * Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) ^ 2 := by
  filter_upwards [ae_finite_resistanceNear ν hν hFE] with e he
  intro δ hδ
  have : Nontrivial (Vertex e.val) := nontrivial_of_geometry (decode e) (decode_geometry e)
  exact exists_areaHoldingLength_bound (decode e) (decode_geometry e) he hδ

end ReflectedGMS.HoldingLengthDecay
