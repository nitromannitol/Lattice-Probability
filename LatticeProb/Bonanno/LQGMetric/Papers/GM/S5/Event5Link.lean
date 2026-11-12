/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event5Link at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event5Dense

/-!
# GM Lemma 5.9: conditions (1)–(3) for one tube and one pair of end points (task P2-M2M8)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.9
(`lem-geo-event-msrble`, l. 3293–3302), conditions (1)–(3) of `E_r` (the event of Lemma 5.8,
l. 3044–3062, `linkEvent`). For a fixed open tube `W` and fixed points `x, y`, `linkXY` is the
condition at `(x, y)` with `U x y = W`. As for `F_r(z)` (`tubeEventB`, `Tubes57Main.lean`), it
agrees on `D̃⁻¹' lenSet` with the projection `linkXYB` of a Borel set (uniqueness of the geodesic
through `MidUnique`, D48; condition (3) on a dense sequence, `cond3_iff`; condition (2) is open in
the point, D69/D77), which is universally measurable (Lusin). The only new ingredient is
`measurable_setDist_sphere`: `(d, u) ↦ d(u, ∂B_s(u))` is Borel. Own elementary argument (GM: "by
inspection").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- conditions (1)–(3) of `E_r` at the end points `x, y` for the tube `W` -/
def linkXY (D D' : DistC → ContMetric) (cs Cs c₁ η ρ b ε r : ℝ) (W : Set ℂ) (x y : ℂ) :
    Set DistC :=
  {g | ∃ u ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W,
    ∃ v ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W,
    b * r ≤ ‖u - v‖ ∧ (D' g).1 (u, v) ≤ c₁ * (D g).1 (u, v) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {u} (Metric.sphere u (4 * ρ * r)) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {v} (Metric.sphere v (4 * ρ * r)) ∧
    UniqueGeodIn (D' g) u v W ∧
    SepDiscNear W (20 * ε * r) u x y (ε * r) ∧
    SepDiscNear W (20 * ε * r) v y x (ε * r) ∧
    (∀ w ∈ nearComp W (20 * ε * r) u,
      (D' g).internal W u w ≤ ENNReal.ofReal (η * (D' g).1 (u, v))) ∧
    (∀ w ∈ nearComp W (20 * ε * r) v,
      (D' g).internal W v w ≤ ENNReal.ofReal (η * (D' g).1 (u, v)))}

/-- `linkEvent` is the intersection of the `linkXY` over the admissible pairs -/
lemma mem_linkEvent_iff_e5 {D D' : DistC → ContMetric} {cs Cs c₁ η δ ρ b ε r : ℝ}
    {U : ℂ → ℂ → Set ℂ} {g : DistC} :
    g ∈ linkEvent D D' cs Cs c₁ η δ ρ b ε r U ↔ ∀ x ∈ sphere (0 : ℂ) (2 * r),
      ∀ y ∈ sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
        g ∈ linkXY D D' cs Cs c₁ η ρ b ε r (U x y) x y :=
  Iff.rfl

/-- `(d, u) ↦ d(u, ∂B_s(u))` is Borel -/
theorem measurable_setDist_sphere (s : ℝ) :
    Measurable fun p : ContMetric × ℂ => setDist p.1 {p.2} (sphere p.2 s) := by
  have hs : ∀ u : ℂ, sphere u s = (fun w => u + w) '' sphere 0 s := fun u => by
    ext y
    simp only [mem_sphere, dist_eq_norm, mem_image, sub_zero]
    constructor
    · intro hy; exact ⟨y - u, hy, by ring⟩
    · rintro ⟨w, hw, rfl⟩; rwa [add_sub_cancel_left]
  have e : (fun p : ContMetric × ℂ => setDist p.1 {p.2} (sphere p.2 s)) =
      fun p => ⨅ w ∈ sphere (0 : ℂ) s, ENNReal.ofReal (p.1.1 (p.2, p.2 + w)) := by
    funext p
    rw [setDist_eq_iInf, hs]
    simp only [mem_singleton_iff, iInf_iInf_eq_left]
    exact iInf_image
  rw [e]
  refine measurable_biInf_of_continuous (f := fun (p : ContMetric × ℂ) (w : ℂ) =>
    ENNReal.ofReal (p.1.1 (p.2, p.2 + w))) (fun p => ?_) (fun w => ?_) _
  · exact ENNReal.continuous_ofReal.comp (p.1.1.continuous.comp
      (continuous_const.prodMk (continuous_const.add continuous_id)))
  · exact (ENNReal.continuous_ofReal.comp (continuous_contMetric_apply.comp
      (continuous_fst.prodMk (continuous_snd.prodMk (continuous_snd.add continuous_const))))).measurable

/-- Borel form of `linkXY` (a projection of a Borel set) -/
def linkXYB (D D' : DistC → ContMetric) (cs Cs c₁ η ρ b ε r : ℝ) (W : Set ℂ) (x y : ℂ) :
    Set DistC :=
  {g | ∃ u v : ℂ, ∃ γ : C(unitInterval, ℂ),
    u ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W ∧
    v ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W ∧
    b * r ≤ ‖u - v‖ ∧ (D' g).1 (u, v) ≤ c₁ * (D g).1 (u, v) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {u} (sphere u (4 * ρ * r)) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {v} (sphere v (4 * ρ * r)) ∧
    MidUnique (D' g) u v ∧ (D' g).IsGeod01 u v γ ∧ (∀ t, γ t ∈ W) ∧
    SepDiscNear W (20 * ε * r) u x y (ε * r) ∧
    SepDiscNear W (20 * ε * r) v y x (ε * r) ∧
    (∀ n, qd n ∈ nearComp W (20 * ε * r) u →
      (D' g).chainInf W u (qd n) ≤ ENNReal.ofReal (η * (D' g).1 (u, v))) ∧
    (∀ n, qd n ∈ nearComp W (20 * ε * r) v →
      (D' g).chainInf W v (qd n) ≤ ENNReal.ofReal (η * (D' g).1 (u, v)))}

/-- `linkXY` equals its Borel form when `D̃_g` is a boundedly compact length metric -/
theorem mem_linkXY_iff_B {D D' : DistC → ContMetric} {cs Cs c₁ η ρ b ε r : ℝ}
    {W : Set ℂ} (hW : IsOpen W) {x y : ℂ} {g : DistC} (hd : D' g ∈ lenSet) :
    g ∈ linkXY D D' cs Cs c₁ η ρ b ε r W x y ↔ g ∈ linkXYB D D' cs Cs c₁ η ρ b ε r W x y := by
  have hex := hex_of_mem hd
  constructor
  · rintro ⟨u, hu, v, hv, hb, hrat, hset, hsetv, ⟨⟨γ, hγ, huniq⟩, hin⟩, hs1, hs2, hi1, hi2⟩
    have hU : (D' g).GeodUnique u v := fun a b ha hb => (huniq a ha).trans (huniq b hb).symm
    exact ⟨u, v, γ, hu, hv, hb, hrat, hset, hsetv, midUnique_of_geodUnique hex hU, hγ,
      fun t => hin γ hγ ⟨t, rfl⟩, hs1, hs2,
      (cond3_iff hd hW hu.2 _ _).1 hi1, (cond3_iff hd hW hv.2 _ _).1 hi2⟩
  · rintro ⟨u, v, γ, hu, hv, hb, hrat, hset, hsetv, hm, hγ, hV1, hs1, hs2, hi1, hi2⟩
    have hU := geodUnique_of_midUnique hm
    refine ⟨u, hu, v, hv, hb, hrat, hset, hsetv, ⟨⟨γ, hγ, fun γ' hγ' => hU γ' γ hγ' hγ⟩,
      fun γ' hγ' => ?_⟩, hs1, hs2, (cond3_iff hd hW hu.2 _ _).2 hi1,
      (cond3_iff hd hW hv.2 _ _).2 hi2⟩
    rintro _ ⟨t, rfl⟩
    rw [hU γ' γ hγ' hγ]
    exact hV1 t

set_option maxHeartbeats 1000000 in
/-- **the Borel form is universally measurable** -/
theorem uMeasurableSet_linkXYB {D D' : DistC → ContMetric}
    (hD : Measurable D) (hD' : Measurable D') (cs Cs c₁ η ρ b ε r : ℝ) {W : Set ℂ}
    (hW : IsOpen W) (x y : ℂ) : UMeasurableSet (linkXYB D D' cs Cs c₁ η ρ b ε r W x y) := by
  let T := DistC × (ℂ × ℂ) × C(unitInterval, ℂ)
  have mu : Measurable fun p : T => p.2.1.1 := measurable_snd.fst.fst
  have mv : Measurable fun p : T => p.2.1.2 := measurable_snd.fst.snd
  have m1 : Measurable fun p : T => (p.2.1.1, p.2.1.2) := measurable_snd.fst
  have mD' : Measurable fun p : T => D' p.1 := hD'.comp measurable_fst
  have fD : ∀ E : DistC → ContMetric, Measurable E →
      Measurable fun p : T => (E p.1).1 (p.2.1.1, p.2.1.2) := fun E hE =>
    continuous_contMetric_apply.measurable.comp ((hE.comp measurable_fst).prodMk m1)
  have hVB : MeasurableSet ((annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W) :=
    (annulus 0 _ _).isOpen.measurableSet.inter hW.measurableSet
  have A1 : MeasurableSet {p : T | p.2.1.1 ∈
      (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W} := hVB.preimage mu
  have A2 : MeasurableSet {p : T | p.2.1.2 ∈
      (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ W} := hVB.preimage mv
  have A3 : MeasurableSet {p : T | b * r ≤ ‖p.2.1.1 - p.2.1.2‖} :=
    measurableSet_le measurable_const (mu.sub mv).norm
  have A4 : MeasurableSet {p : T | (D' p.1).1 (p.2.1.1, p.2.1.2) ≤
      c₁ * (D p.1).1 (p.2.1.1, p.2.1.2)} :=
    measurableSet_le (fD D' hD') ((fD D hD).const_mul c₁)
  have A5 : ∀ f : T → ℂ, Measurable f → MeasurableSet {p : T |
      ENNReal.ofReal ((D' p.1).1 (p.2.1.1, p.2.1.2)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' p.1) {f p} (sphere (f p) (4 * ρ * r))} :=
    fun f hf =>
    have mS : Measurable fun p : T => setDist (D' p.1) {f p} (sphere (f p) (4 * ρ * r)) :=
      Measurable.comp (g := fun q : ContMetric × ℂ => setDist q.1 {q.2} (sphere q.2 (4 * ρ * r)))
        (f := fun p : T => (D' p.1, f p)) (measurable_setDist_sphere _) (mD'.prodMk hf)
    measurableSet_le (ENNReal.measurable_ofReal.comp (fD D' hD')) (mS.const_mul _)
  have A6 : MeasurableSet {p : T | MidUnique (D' p.1) p.2.1.1 p.2.1.2} :=
    measurableSet_midUnique.preimage (mD'.prodMk m1)
  have A7 : MeasurableSet {p : T | (D' p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2} :=
    isClosed_geodRel3.measurableSet.preimage (mD'.prodMk measurable_snd)
  have A8 : MeasurableSet {p : T | ∀ t, p.2.2 t ∈ W} := by
    have ho : IsOpen {γ : C(unitInterval, ℂ) | MapsTo γ univ W} :=
      ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hW
    have e : {γ : C(unitInterval, ℂ) | ∀ t, γ t ∈ W} =
        {γ : C(unitInterval, ℂ) | MapsTo (⇑γ) univ W} := by
      ext γ; simp only [mem_ofPred_eq, MapsTo, mem_univ, true_imp_iff]
    rw [← e] at ho
    exact ho.measurableSet.preimage measurable_snd.snd
  have A10 : MeasurableSet {p : T | SepDiscNear W (20 * ε * r) p.2.1.1 x y (ε * r)} :=
    (isOpen_setOf_sepDiscNear W _ _ _ _).measurableSet.preimage mu
  have A11 : MeasurableSet {p : T | SepDiscNear W (20 * ε * r) p.2.1.2 y x (ε * r)} :=
    (isOpen_setOf_sepDiscNear W _ _ _ _).measurableSet.preimage mv
  have A12 : ∀ (f : T → ℂ), Measurable f → MeasurableSet {p : T | ∀ n,
      qd n ∈ nearComp W (20 * ε * r) (f p) →
      (D' p.1).chainInf W (f p) (qd n) ≤ ENNReal.ofReal (η * (D' p.1).1 (p.2.1.1, p.2.1.2))} := by
    intro f hf
    simp only [ofPred_forall]
    refine MeasurableSet.iInter fun n => ?_
    have e : {p : T | qd n ∈ nearComp W (20 * ε * r) (f p) →
        (D' p.1).chainInf W (f p) (qd n) ≤ ENNReal.ofReal (η * (D' p.1).1 (p.2.1.1, p.2.1.2))} =
        {p : T | qd n ∈ nearComp W (20 * ε * r) (f p)}ᶜ ∪
          {p : T | (D' p.1).chainInf W (f p) (qd n) ≤
            ENNReal.ofReal (η * (D' p.1).1 (p.2.1.1, p.2.1.2))} := by
      ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    refine (((isOpen_setOf_mem_nearComp hW _ _).measurableSet.preimage hf).compl).union
      (measurableSet_le ?_ (ENNReal.measurable_ofReal.comp ((fD D' hD').const_mul η)))
    exact measurable_chainInf_comp mD' hf measurable_const W
  have hS := A1.inter <| A2.inter <| A3.inter <| A4.inter <| (A5 _ mu).inter <| (A5 _ mv).inter <|
    A6.inter <| A7.inter <| A8.inter <| A10.inter <| A11.inter <| (A12 _ mu).inter (A12 _ mv)
  convert UMeasurableSet.setOf_exists hS using 1
  ext g
  constructor
  · rintro ⟨u, v, γ, h⟩; exact ⟨((u, v), γ), h⟩
  · rintro ⟨⟨⟨u, v⟩, γ⟩, h⟩; exact ⟨u, v, γ, h⟩

end LQGMetric.GM
