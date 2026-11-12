/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes57Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Meas

/-!
# GM Lemma 5.7: `F_r(z)` is a.s. determined by `(h − h_{4r}(z))|_{B_{3r}(z)}` (task P2-M2L2)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.7
(`lem-geo-event-local`, l. 2997–3018), by the D51 route of `gm_L3_7meas`
(`Papers/GM/S3/GoodAnnulusMeas4.lean`): `LocalEvent.aeEventIn_of_saturated` applied to

* `Y = h`, `W` = {`D_g`, `D̃_g` boundedly compact length metrics, `c_* D_g ≤ D̃_g ≤ C_* D_g` on the
  pairs of a dense sequence} (Borel; a.s. by GM.S1.1 (`DFGPSLem3_8`) and `RatiosAre`);
* `R(g)` = the internal metrics of `B_{3r}(z)` at the pairs of a dense sequence of `B_{3r}(z)`,
  computed from `h|_{B_{3r}(z)}` by Axiom II (locality);
* `B = F_r(z)`: on `W` it is determined by `R` (`tubeEvent_saturated`, GM l. 3006–3017) and equals
  the projection `tubeEventB` of a Borel set (uniqueness of the geodesic through `MidUnique`, D48;
  condition (3) on a dense sequence), hence is universally measurable.

Condition (2) of `F_r(z)` is a deterministic condition on the point `u`; in its robust reading
`SepNear`/`SepDiscNear` (decisions D69, D77) it defines an open, hence Borel, set of `u`
(`isOpen_setOf_sepDiscNear`).
GM do not discuss measurability.

Then `gm_L5_7loc` gives `L5_7loc` and, with `gm_L5_7_of_loc` (Axiom III), `L5_7`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- condition (3) on the dense sequence `qd` -/
theorem cond3_iff {d : ContMetric} (hd : d ∈ lenSet) {V : Set ℂ} (hV : IsOpen V) {u : ℂ}
    (hu : u ∈ V) (δ : ℝ) (c : ℝ≥0∞) :
    (∀ w ∈ nearComp V δ u, d.internal V u w ≤ c) ↔
      ∀ n, qd n ∈ nearComp V δ u → d.chainInf V u (qd n) ≤ c := by
  have hl := isLength_of_mem_lenSet hd
  constructor
  · intro h n hn
    rw [← d.internal_eq_chainInf hl hV]; exact h _ hn
  · intro h w hw
    by_contra hlt
    rw [not_le] at hlt
    have hO : IsOpen (nearComp V δ u) := (hV.inter isOpen_ball).connectedComponentIn
    have hOV : nearComp V δ u ⊆ V := fun x hx => (connectedComponentIn_subset _ _ hx).1
    have hf : ContinuousOn (fun x => d.internal V u x) V :=
      (d.continuousOn_internal hl hV).comp (continuousOn_const.prodMk continuousOn_id)
        fun x hx => ⟨hu, hx⟩
    have hfa := hf.continuousAt (hV.mem_nhds (hOV hw))
    have hN : {x | c < d.internal V u x} ∩ nearComp V δ u ∈ 𝓝 w :=
      Filter.inter_mem (hfa.preimage_mem_nhds (Ioi_mem_nhds hlt)) (hO.mem_nhds hw)
    obtain ⟨t, hts, ht, hwt⟩ := _root_.mem_nhds_iff.1 hN
    obtain ⟨n, hn⟩ := denseRange_qd.exists_mem_open ht ⟨w, hwt⟩
    have h1 := h n (hts hn).2
    rw [← d.internal_eq_chainInf hl hV] at h1
    exact absurd (hts hn).1 (not_lt.2 h1)

/-- Borel form of `F_r(z)` (a projection of a Borel set) -/
def tubeEventB (D D' : DistC → ContMetric) (cs Cs c₁ η b ε r : ℝ) (z : ℂ) (V : Set ℂ) :
    Set DistC :=
  {g | ∃ u v : ℂ, ∃ γ : C(unitInterval, ℂ),
    u ∈ V ∩ closedBall z r ∧ v ∈ V ∩ closedBall z r ∧
    b * r ≤ ‖u - v‖ ∧ (D' g).1 (u, v) ≤ c₁ * (D g).1 (u, v) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {u} (sphere z (2 * r)) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {v} (sphere z (2 * r)) ∧
    MidUnique (D' g) u v ∧ (D' g).IsGeod01 u v γ ∧ (∀ t, γ t ∈ V) ∧
    (∀ t, γ t ∈ closedBall z r) ∧
    SepDiscNear V (20 * ε * r) u (z - 2 * r) (z + 2 * r) (ε * r) ∧
    SepDiscNear V (20 * ε * r) v (z + 2 * r) (z - 2 * r) (ε * r) ∧
    (∀ n, qd n ∈ nearComp V (20 * ε * r) u →
      (D' g).chainInf V u (qd n) ≤ ENNReal.ofReal (η * (D' g).1 (u, v))) ∧
    (∀ n, qd n ∈ nearComp V (20 * ε * r) v →
      (D' g).chainInf V v (qd n) ≤ ENNReal.ofReal (η * (D' g).1 (u, v)))}

/-- `F_r(z)` equals its Borel form when `D̃_g` is a boundedly compact length metric -/
theorem mem_tubeEvent_iff_B {D D' : DistC → ContMetric} {cs Cs c₁ η b ε r : ℝ} {z : ℂ}
    {V : Set ℂ} (hV : IsOpen V) {g : DistC} (hd : D' g ∈ lenSet) :
    g ∈ tubeEvent D D' cs Cs c₁ η b ε r z V ↔ g ∈ tubeEventB D D' cs Cs c₁ η b ε r z V := by
  have hex := hex_of_mem hd
  constructor
  · rintro ⟨u, hu, v, hv, hb, hrat, hset, hsetv, ⟨⟨γ, hγ, huniq⟩, hin⟩, hs1, hs2, hi1, hi2⟩
    have hU : (D' g).GeodUnique u v := fun a b ha hb => (huniq a ha).trans (huniq b hb).symm
    exact ⟨u, v, γ, hu, hv, hb, hrat, hset, hsetv, midUnique_of_geodUnique hex hU, hγ,
      fun t => (hin γ hγ ⟨t, rfl⟩).1, fun t => (hin γ hγ ⟨t, rfl⟩).2, hs1, hs2,
      (cond3_iff hd hV hu.1 _ _).1 hi1, (cond3_iff hd hV hv.1 _ _).1 hi2⟩
  · rintro ⟨u, v, γ, hu, hv, hb, hrat, hset, hsetv, hm, hγ, hV1, hV2, hs1, hs2, hi1, hi2⟩
    have hU := geodUnique_of_midUnique hm
    refine ⟨u, hu, v, hv, hb, hrat, hset, hsetv, ⟨⟨γ, hγ, fun γ' hγ' => hU γ' γ hγ' hγ⟩,
      fun γ' hγ' => ?_⟩, hs1, hs2, (cond3_iff hd hV hu.1 _ _).2 hi1,
      (cond3_iff hd hV hv.1 _ _).2 hi2⟩
    rintro _ ⟨t, rfl⟩
    rw [hU γ' γ hγ' hγ]
    exact ⟨hV1 t, hV2 t⟩

/-- **the Borel form is universally measurable** -/
theorem uMeasurableSet_tubeEventB {D D' : DistC → ContMetric}
    (hD : Measurable D) (hD' : Measurable D') (cs Cs c₁ η b ε r : ℝ) (z : ℂ) {V : Set ℂ}
    (hV : IsOpen V) : UMeasurableSet (tubeEventB D D' cs Cs c₁ η b ε r z V) := by
  let T := DistC × (ℂ × ℂ) × C(unitInterval, ℂ)
  have mu : Measurable fun p : T => p.2.1.1 := measurable_snd.fst.fst
  have mv : Measurable fun p : T => p.2.1.2 := measurable_snd.fst.snd
  have m1 : Measurable fun p : T => (p.2.1.1, p.2.1.2) := measurable_snd.fst
  have mD' : Measurable fun p : T => D' p.1 := hD'.comp measurable_fst
  have fD : ∀ E : DistC → ContMetric, Measurable E →
      Measurable fun p : T => (E p.1).1 (p.2.1.1, p.2.1.2) := fun E hE =>
    continuous_contMetric_apply.measurable.comp ((hE.comp measurable_fst).prodMk m1)
  have hVB : MeasurableSet (V ∩ closedBall z r) :=
    hV.measurableSet.inter isClosed_closedBall.measurableSet
  have A1 : MeasurableSet {p : T | p.2.1.1 ∈ V ∩ closedBall z r} := hVB.preimage mu
  have A2 : MeasurableSet {p : T | p.2.1.2 ∈ V ∩ closedBall z r} := hVB.preimage mv
  have A3 : MeasurableSet {p : T | b * r ≤ ‖p.2.1.1 - p.2.1.2‖} :=
    measurableSet_le measurable_const (mu.sub mv).norm
  have A4 : MeasurableSet {p : T | (D' p.1).1 (p.2.1.1, p.2.1.2) ≤
      c₁ * (D p.1).1 (p.2.1.1, p.2.1.2)} :=
    measurableSet_le (fD D' hD') ((fD D hD).const_mul c₁)
  have A5 : MeasurableSet {p : T | ENNReal.ofReal ((D' p.1).1 (p.2.1.1, p.2.1.2)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' p.1) {p.2.1.1} (sphere z (2 * r))} :=
    have mS : Measurable fun p : T => setDist (D' p.1) {p.2.1.1} (sphere z (2 * r)) :=
      Measurable.comp (g := fun q : ContMetric × ℂ => setDist q.1 {q.2} (sphere z (2 * r)))
        (f := fun p : T => (D' p.1, p.2.1.1)) (measurable_setDist_singleton _) (mD'.prodMk mu)
    measurableSet_le (ENNReal.measurable_ofReal.comp (fD D' hD')) (mS.const_mul _)
  have A5' : MeasurableSet {p : T | ENNReal.ofReal ((D' p.1).1 (p.2.1.1, p.2.1.2)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' p.1) {p.2.1.2} (sphere z (2 * r))} :=
    have mS : Measurable fun p : T => setDist (D' p.1) {p.2.1.2} (sphere z (2 * r)) :=
      Measurable.comp (g := fun q : ContMetric × ℂ => setDist q.1 {q.2} (sphere z (2 * r)))
        (f := fun p : T => (D' p.1, p.2.1.2)) (measurable_setDist_singleton _) (mD'.prodMk mv)
    measurableSet_le (ENNReal.measurable_ofReal.comp (fD D' hD')) (mS.const_mul _)
  have A6 : MeasurableSet {p : T | MidUnique (D' p.1) p.2.1.1 p.2.1.2} :=
    measurableSet_midUnique.preimage (mD'.prodMk m1)
  have A7 : MeasurableSet {p : T | (D' p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2} :=
    isClosed_geodRel3.measurableSet.preimage (mD'.prodMk measurable_snd)
  have A8 : MeasurableSet {p : T | ∀ t, p.2.2 t ∈ V} := by
    have ho : IsOpen {γ : C(unitInterval, ℂ) | MapsTo γ univ V} :=
      ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hV
    have e : {γ : C(unitInterval, ℂ) | ∀ t, γ t ∈ V} =
        {γ : C(unitInterval, ℂ) | MapsTo (⇑γ) univ V} := by
      ext γ; simp only [mem_ofPred_eq, MapsTo, mem_univ, true_imp_iff]
    rw [← e] at ho
    exact ho.measurableSet.preimage measurable_snd.snd
  have A9 : MeasurableSet {p : T | ∀ t, p.2.2 t ∈ closedBall z r} := by
    have hc : IsClosed {γ : C(unitInterval, ℂ) | ∀ t, γ t ∈ closedBall z r} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t => isClosed_closedBall.preimage (continuous_eval_const t)
    exact hc.measurableSet.preimage measurable_snd.snd
  have A10 : MeasurableSet
      {p : T | SepDiscNear V (20 * ε * r) p.2.1.1 (z - 2 * r) (z + 2 * r) (ε * r)} :=
    (isOpen_setOf_sepDiscNear V _ _ _ _).measurableSet.preimage mu
  have A11 : MeasurableSet
      {p : T | SepDiscNear V (20 * ε * r) p.2.1.2 (z + 2 * r) (z - 2 * r) (ε * r)} :=
    (isOpen_setOf_sepDiscNear V _ _ _ _).measurableSet.preimage mv
  have A12 : ∀ (f : T → ℂ), Measurable f → MeasurableSet {p : T | ∀ n,
      qd n ∈ nearComp V (20 * ε * r) (f p) →
      (D' p.1).chainInf V (f p) (qd n) ≤ ENNReal.ofReal (η * (D' p.1).1 (p.2.1.1, p.2.1.2))} := by
    intro f hf
    simp only [ofPred_forall]
    refine MeasurableSet.iInter fun n => ?_
    have e : {p : T | qd n ∈ nearComp V (20 * ε * r) (f p) →
        (D' p.1).chainInf V (f p) (qd n) ≤ ENNReal.ofReal (η * (D' p.1).1 (p.2.1.1, p.2.1.2))} =
        {p : T | qd n ∈ nearComp V (20 * ε * r) (f p)}ᶜ ∪
          {p : T | (D' p.1).chainInf V (f p) (qd n) ≤
            ENNReal.ofReal (η * (D' p.1).1 (p.2.1.1, p.2.1.2))} := by
      ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    refine (((isOpen_setOf_mem_nearComp hV _ _).measurableSet.preimage hf).compl).union
      (measurableSet_le ?_ (ENNReal.measurable_ofReal.comp ((fD D' hD').const_mul η)))
    exact measurable_chainInf_comp mD' hf measurable_const V
  have hS := A1.inter <| A2.inter <| A3.inter <| A4.inter <| A5.inter <| A5'.inter <| A6.inter <| A7.inter <|
    A8.inter <| A9.inter <| A10.inter <| A11.inter <| (A12 _ mu).inter (A12 _ mv)
  convert UMeasurableSet.setOf_exists hS using 1
  ext g
  constructor
  · rintro ⟨u, v, γ, h⟩; exact ⟨((u, v), γ), h⟩
  · rintro ⟨⟨⟨u, v⟩, γ⟩, h⟩; exact ⟨u, v, γ, h⟩

end LQGMetric.GM
