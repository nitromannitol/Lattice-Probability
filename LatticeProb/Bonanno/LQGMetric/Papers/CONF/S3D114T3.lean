/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114T3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114T2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114W

/-!
# CONF Lemma 3.6: the Step 3 node for `fatG`, wiring, and the a.s. measurability of `G̃ⁿ`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (C:1308–1448); decisions D114 §4,
D120 §3.

* `conf36StepNodeAE_fatG`: **`Conf36StepNodeAE γ D c p (fatG p)`** for `0 < δ < 1/8` (from
  `conf36Eq325_fatG`, S3D114T2, and `conf36StepNodeAE_of_eq325`, S3D114S2).
* `conf36_lem3_6AtAE0_of_meas`: `CONFLem3_6AtAE0 γ D c p` from `L33Gen γ D c p (fatG p)` and the
  Step 1 node `Conf36MeasNodeAE γ D c p (fatG p)` alone.
* `conf36_Gt_aeEventIn`: part (ii) of the Step 1 node (CONF C:1362–1368): every `G̃ⁿ` is an a.s.
  event (null-measurable): on each piece `{ε𝕣 = 𝔢, z = 𝔷}` the radii `ρ̃ⁿ` are built from the
  null-measurable events `E^{Ũ}_r(𝔷)`, `fatG` and `conf36Conn` (`conf36_measurableSet_rho` with
  the σ-algebra of null-measurable sets).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **Step 3 node for `fatG`** (CONF (3.24)–(3.25), C:1425–1447) -/
theorem conf36StepNodeAE_fatG {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) : Conf36StepNodeAE γ D c p (fatG p) :=
  conf36StepNodeAE_of_eq325 (conf36Eq325_fatG hδ hδ8)

section Null
variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- the σ-algebra of `P`-null-measurable sets -/
def conf36NullMS (P : Measure Ω) : MeasurableSpace Ω where
  MeasurableSet' s := NullMeasurableSet s P
  measurableSet_empty := nullMeasurableSet_empty
  measurableSet_compl _ h := h.compl
  measurableSet_iUnion _ h := NullMeasurableSet.iUnion h

theorem conf36_aeEventIn_of_null {P : Measure Ω} {E : Set Ω} (hE : NullMeasurableSet E P) :
    AEEventIn P mΩ E :=
  ⟨toMeasurable P E, measurableSet_toMeasurable _ _, hE.toMeasurable_ae_eq.symm⟩

theorem conf36_null_of_aeEventIn {P : Measure Ω} {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {E : Set Ω} (hE : @AEEventIn Ω mΩ P m E) : @NullMeasurableSet Ω mΩ E P := by
  obtain ⟨F, hF, hEF⟩ := hE
  letI : MeasurableSpace Ω := mΩ
  exact (hm _ hF).nullMeasurableSet.congr hEF.symm

end Null

section Piece
variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams} {Ω : Type}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
  {Bf : Ω → Set ℂ} {e : Ω → ℝ} {zf : Ω → ℂ}

/-- `E^{Ũ}_{2^j𝔢}(𝔷)` with `Ũ` built from `𝓑` is null-measurable -/
theorem conf36_EUj_null (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P)
    (hBc : ∀ ω, IsClosed (Bf ω))
    (hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y → NullMeasurableSet Y P)
    {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) (𝔷 : ℂ) (j : ℤ) :
    NullMeasurableSet (conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 j) P := by
  have hr' : 0 < (2 : ℝ) ^ j * 𝔢 := mul_pos (zpow_pos (by norm_num) j) h𝔢0
  unfold conf36EUj
  rw [conf36_setOf_mem_eq_iUnion
    (fun T' => confEU (xiGamma γ) c D P h p ((2 : ℝ) ^ j * 𝔢) 𝔷 T')
    (fun ω => conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω))]
  exact NullMeasurableSet.iUnion fun T' => (hset (conf36_setSigma_T hBc _ _ _ T')).inter
    (conf36_confEU_nullMeas hD hh p hr' 𝔷 T')

/-- the `fatG` event at `2^j𝔢` with `Ũ` built from `𝓑` is null-measurable -/
theorem conf36_FatJ_null (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    (hh : IsWholePlaneGFF h P) (hBc : ∀ ω, IsClosed (Bf ω))
    (hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y → NullMeasurableSet Y P)
    {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) (𝔷 : ℂ) (j : ℤ) :
    NullMeasurableSet (conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 j) P := by
  have hr' : 0 < (2 : ℝ) ^ j * 𝔢 := mul_pos (zpow_pos (by norm_num) j) h𝔢0
  have hfs : fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ((2 : ℝ) ^ j * 𝔢) 𝔷))
      ⟨ball 𝔷 (5 * ((2 : ℝ) ^ j * 𝔢)), isOpen_ball⟩ ≤ mΩ := by
    have hm : Measurable fun ω => -circleAvg (h ω) ((2 : ℝ) ^ j * 𝔢) 𝔷 :=
      ((measurable_circleAvg_left _ 𝔷).comp hh.measurable).neg
    exact ((measurable_restrictTo _).comp (hh.addConst hm).measurable).comap_le
  unfold conf36FatJ
  have eq := conf36_setOf_mem_eq_iUnion (fun T' => {ω | fatG p (D (h ω))
    (scaleFac (xiGamma γ) c (h ω) ((2 : ℝ) ^ j * 𝔢) 𝔷) ((2 : ℝ) ^ j * 𝔢) 𝔷 T'})
    (fun ω => conf36T p.δ ((2 : ℝ) ^ j * 𝔢) 𝔷 (Bf ω))
  simp only [mem_ofPred_eq] at eq
  rw [eq]
  exact NullMeasurableSet.iUnion fun T' => (hset (conf36_setSigma_T hBc _ _ _ T')).inter
    (conf36_null_of_aeEventIn hfs (conf36_fatG_ball hD hh p hδ hδ8 c hr' 𝔷 T'))

set_option maxHeartbeats 1000000 in
/-- `G̃ⁿ` on a piece `{e = 𝔢, zf = 𝔷}` through the events at the radii `2^k𝔢` -/
theorem conf36_Gt_piece_eq {𝔢 : ℝ} {𝔷 : ℂ} (n : ℕ) :
    {ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ conf36Gt (fatG p) (xiGamma γ) c D P h p e zf Bf n =
      ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤}) ∪
      ⋃ k : ℤ, ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩ {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
          ENNReal.ofReal ((2 : ℝ) ^ k * 𝔢)}) ∩
        conf36EUj (xiGamma γ) c D P h p Bf 𝔢 𝔷 k ∩
        conf36FatJ (fatG p) (xiGamma γ) c D h p Bf 𝔢 𝔷 k ∩
        {ω | conf36Conn (Bf ω) ((2 : ℝ) ^ k * 𝔢) 𝔷} := by
  ext ω
  constructor
  · rintro ⟨h0, h1 | ⟨k, h2, h3, h4, h5⟩⟩
    · exact Or.inl ⟨h0, h1⟩
    · rw [h0.1] at h2
      rw [h0.1, h0.2] at h3 h4 h5
      exact Or.inr (mem_iUnion.2 ⟨k, ⟨⟨⟨h0, h2⟩, h3⟩, h4⟩, h5⟩)
  · rintro (⟨h0, h1⟩ | hU)
    · exact ⟨h0, Or.inl h1⟩
    · obtain ⟨k, ⟨⟨⟨h0, h2⟩, h3⟩, h4⟩, h5⟩ := mem_iUnion.1 hU
      refine ⟨h0, Or.inr ⟨k, ?_⟩⟩
      have e1 : e ω = 𝔢 := h0.1
      have e2 : zf ω = 𝔷 := h0.2
      rw [e1, e2]
      exact ⟨h2, h3, h4, h5⟩

/-- **`G̃ⁿ` on a piece is null-measurable** -/
theorem conf36_Gt_piece_null (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    (hh : IsWholePlaneGFF h P) (hBc : ∀ ω, IsClosed (Bf ω))
    (hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma Bf] Y → NullMeasurableSet Y P)
    {𝔢 : ℝ} (h𝔢0 : 0 < 𝔢) (𝔷 : ℂ) (hE₀ : NullMeasurableSet {ω | e ω = 𝔢 ∧ zf ω = 𝔷} P)
    (n : ℕ) : NullMeasurableSet ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
      conf36Gt (fatG p) (xiGamma γ) c D P h p e zf Bf n) P := by
  have hEU := conf36_EUj_null (p := p) hD hh hBc hset h𝔢0 𝔷
  have hρ : ∀ m : ℕ, ∀ ℓ : ℤ, MeasurableSet[conf36NullMS P] ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
      {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf m ω = ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢)}) :=
    fun m ℓ => conf36_measurableSet_rho (conf36NullMS P) (k := ℓ + 1) h𝔢0 (fun _ hω => hω) hE₀
      (fun j _ => NullMeasurableSet.inter hE₀ (hEU j)) m ℓ (by omega)
  have htop : NullMeasurableSet ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
      {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤}) P := by
    have eq : {ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
        {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤} =
        {ω | e ω = 𝔢 ∧ zf ω = 𝔷} \ ⋃ ℓ : ℤ, ({ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
          {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
            ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢)}) := by
      ext ω
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨h0, fun hU => ?_⟩
        obtain ⟨ℓ, -, h2⟩ := mem_iUnion.1 hU
        have h1' : conf36Rho (xiGamma γ) c D P h p e zf Bf n ω = ⊤ := h1
        have h2' : conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
          ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢) := h2
        exact ENNReal.ofReal_ne_top (h2'.symm.trans h1')
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        have e1 : e ω = 𝔢 := h0.1
        have hpos : 0 < e ω := e1 ▸ h𝔢0
        rcases conf36Rho_cases (ξ := xiGamma γ) (cc := c) (D := D) (P := P) (h := h) (p := p)
          (zf := zf) (Bf := Bf) hpos n with ht | ⟨ℓ, hℓ⟩
        · exact ht
        · rw [e1] at hℓ
          exact absurd (mem_iUnion.2 ⟨ℓ, (⟨h0, hℓ⟩ : ω ∈ {ω | e ω = 𝔢 ∧ zf ω = 𝔷} ∩
            {ω | conf36Rho (xiGamma γ) c D P h p e zf Bf n ω =
              ENNReal.ofReal ((2 : ℝ) ^ ℓ * 𝔢)})⟩) h1
    rw [eq]
    exact hE₀.diff (NullMeasurableSet.iUnion fun ℓ => hρ n ℓ)
  rw [conf36_Gt_piece_eq n]
  refine htop.union (NullMeasurableSet.iUnion fun k => ?_)
  exact (((hρ n k).inter (hEU k)).inter
    (conf36_FatJ_null hδ hδ8 hD hh hBc hset h𝔢0 𝔷 k)).inter
    (hset (conf36_setSigma_conn Bf _ 𝔷))

end Piece

/-- **Step 1, part (ii)** (CONF C:1362–1368): each `G̃ⁿ` (for `fatG`) is null-measurable -/
theorem conf36_Gt_null {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) {R : ℝ} (hR : 0 < R) (τ : Ω → ℝ)
    (hle : localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ mΩ) (x : Ω → ℂ) (ε : Ω → ℝ)
    (hx : @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x)
    (hε : @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε)
    (hε1 : ∀ ω, ε ω ∈ Ioo 0 1) (hεc : (Set.range ε).Countable) (n : ℕ) :
    NullMeasurableSet (conf36Gt (fatG p) (xiGamma γ) c D P h p (fun ω => ε ω * R)
      (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n) P := by
  have hBc : ∀ ω, IsClosed (filledBall (D (h ω)) z₀ (τ ω)) := fun ω =>
    conf36_isClosed_filledBall _ _ _
  have hset : ∀ {Y : Set Ω}, MeasurableSet[setSigma (fun ω => filledBall (D (h ω)) z₀ (τ ω))] Y →
      NullMeasurableSet Y P := fun hY =>
    (hle _ (confD110_setSigma_le_localSigma0 h _ _ hY)).nullMeasurableSet
  have hem : Measurable[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))]
      (fun ω => ε ω * R) := hε.mul_const R
  have hzm : Measurable[localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))]
      (fun ω => conf36Grid (ε ω * R / 4) (x ω)) :=
    conf36_measurable_grid ((hε.mul_const R).div_const 4) hx
  have hec : (range fun ω => ε ω * R).Countable :=
    (hεc.image (· * R)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨ε ω, mem_range_self ω, rfl⟩)
  have hzc := conf36_range_grid_countable (m := fun ω => ε ω * R / 4)
    ((hεc.image (· * R / 4)).mono (by rintro _ ⟨ω, rfl⟩; exact ⟨ε ω, mem_range_self ω, rfl⟩)) x
  have eq : conf36Gt (fatG p) (xiGamma γ) c D P h p (fun ω => ε ω * R)
      (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n =
      ⋃ 𝔢 ∈ range (fun ω => ε ω * R), ⋃ 𝔷 ∈ range (fun ω => conf36Grid (ε ω * R / 4) (x ω)),
        {ω | ε ω * R = 𝔢 ∧ conf36Grid (ε ω * R / 4) (x ω) = 𝔷} ∩
          conf36Gt (fatG p) (xiGamma γ) c D P h p (fun ω => ε ω * R)
            (fun ω => conf36Grid (ε ω * R / 4) (x ω))
            (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop, mem_range]
    constructor
    · intro hω
      exact ⟨ε ω * R, ⟨ω, rfl⟩, conf36Grid (ε ω * R / 4) (x ω), ⟨ω, rfl⟩, ⟨rfl, rfl⟩, hω⟩
    · rintro ⟨_, _, _, _, _, hω⟩
      exact hω
  rw [eq]
  refine NullMeasurableSet.biUnion hec fun 𝔢 h𝔢 => NullMeasurableSet.biUnion hzc fun 𝔷 _ => ?_
  obtain ⟨ω₀, rfl⟩ := h𝔢
  exact conf36_Gt_piece_null hδ hδ8 hD hh hBc hset (mul_pos (hε1 ω₀).1 hR) 𝔷
    (hle _ ((hem (measurableSet_singleton _)).inter
      (hzm (measurableSet_singleton 𝔷)))).nullMeasurableSet n

/-- **Step 1, part (ii)**, in the form of `Conf36MeasNodeAE` -/
theorem conf36_Gt_aeEventIn {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (hδ : 0 < p.δ) (hδ8 : p.δ < 1 / 8) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (z₀ : ℂ) {R : ℝ} (hR : 0 < R) (τ : Ω → ℝ)
    (hle : localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ mΩ) (x : Ω → ℂ) (ε : Ω → ℝ)
    (hx : @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x)
    (hε : @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε)
    (hε1 : ∀ ω, ε ω ∈ Ioo 0 1) (hεc : (Set.range ε).Countable) (n : ℕ) :
    AEEventIn P mΩ (conf36Gt (fatG p) (xiGamma γ) c D P h p (fun ω => ε ω * R)
      (fun ω => conf36Grid (ε ω * R / 4) (x ω)) (fun ω => filledBall (D (h ω)) z₀ (τ ω)) n) :=
  conf36_aeEventIn_of_null (conf36_Gt_null hδ hδ8 hD hh z₀ hR τ hle x ε hx hε hε1 hεc n)

end LQGMetric.CONF
