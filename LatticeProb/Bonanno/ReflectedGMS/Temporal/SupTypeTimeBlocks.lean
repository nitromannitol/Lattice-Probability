/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.SupTypeTimeBlocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SupTypeTimeIndex

/-!
# The sup-type time blocks of Section 17

With the index `κ` of `SupTypeTimeIndex` (manuscript (17.3)), the block through `s` at the
parameter `m = 2^q` is

  `J_m(s) = the largest dyadic interval through s with κ(J) ≤ m`,

which "defines nested covariant partitions for almost every `s`" (page 40).  At a time with no
good block — a nonvertex time at which holding intervals accumulate — the manuscript's block is
undefined and its transports are set to zero; here the block is the singleton `{s}`, whose
Lebesgue measure is `0`, so that the transport kernel `|J|⁻¹ 1_J F` vanishes there exactly as the
manuscript prescribes.  Off the invariant gate `G` the blocks are the plain level-`⌊q⌋` dyadic
blocks, as in `FlowSpaceBlockSystem.gatedBlock`.

This module proves, carrier-generically under `HoldingData G θΩ SΩ hold`, every pointwise field of
the temporal block system EXCEPT the everywhere-positivity of the block length, which is FALSE for
these blocks and is replaced by positivity at almost every time (`volume_supBlock_pos_ae`):

* partition: `self_mem_supBlock`, `supBlock_eq_of_mem`;
* covariance: `supBlock_shift` (everywhere), `supBlock_scale_of_mem` (on the gate);
* measurability: `measurableSet_graph_supBlock`;
* length: `volume_supBlock_lt_top`, `volume_supBlock_pos_ae`, `volume_supBlock_pos_of_ne_zero`
  (positive at every vertex time);
* nesting in the parameter: `supBlock_nested`;
* the root chain: `supSel`, `selection_root_supSel`, `tendsto_supSel` ("every root dyadic
  interval occurs on a nonempty parameter interval `[κ(J), κ(J^(1)))`", from the strict increase
  `kappa_lt_succ`).

The assembly into the (weakened) `TemporalBlockSystem` / `GatedRootChainBlocks` is done where those
structures are generalised; nothing here is probabilistic.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal NNReal

namespace ReflectedGMS.SupTypeTimeBlocks

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance
open ReflectedGMS.Temporal.ActualDyadicTemporalBlocks ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.FlowSpaceBlockSystem ReflectedGMS.SupTypeTimeIndex

variable {Ω : Type*} [MeasurableSpace Ω] (hold : Ω → ℝ → ℝ≥0∞)

/-! ## 1. The selected level and the block -/

/-- **The selected level**: the coarsest good level through `s`. -/
noncomputable def selLevelK (q : ℚ) (ω : Ω) (D : Grid) (s : ℝ) : ℤ :=
  sSup {k : ℤ | GoodK hold q ω D k s}

open Classical in
/-- **The block `J_m(s)`** at `m = 2^q`: on the gate, the largest good dyadic block through `s`,
or `{s}` if there is none; off the gate the level-`⌊q⌋` dyadic block. -/
noncomputable def supBlock (G : Set Ω) (q : ℚ) (p : Ω × Grid) (s : ℝ) : Set ℝ :=
  if p.1 ∈ G then
    (if ∃ k : ℤ, GoodK hold q p.1 p.2 k s then timeBlockAt p.2 (selLevelK hold q p.1 p.2 s) s
      else {s})
  else timeBlockAt p.2 ⌊q⌋ s

variable {G : Set Ω} {θΩ SΩ : ℝ → Ω → Ω}

theorem supBlock_of_not_mem {q : ℚ} {p : Ω × Grid} (hp : p.1 ∉ G) (s : ℝ) :
    supBlock hold G q p s = timeBlockAt p.2 ⌊q⌋ s := by
  rw [supBlock, if_neg hp]

theorem supBlock_of_good {q : ℚ} {p : Ω × Grid} (hp : p.1 ∈ G) {s : ℝ}
    (hex : ∃ k : ℤ, GoodK hold q p.1 p.2 k s) :
    supBlock hold G q p s = timeBlockAt p.2 (selLevelK hold q p.1 p.2 s) s := by
  rw [supBlock, if_pos hp, if_pos hex]

theorem supBlock_of_bad {q : ℚ} {p : Ω × Grid} (hp : p.1 ∈ G) {s : ℝ}
    (hex : ¬ ∃ k : ℤ, GoodK hold q p.1 p.2 k s) : supBlock hold G q p s = {s} := by
  rw [supBlock, if_pos hp, if_neg hex]

/-! ### Lemmas not needing the holding data -/

theorem self_mem_supBlock (q : ℚ) (p : Ω × Grid) (s : ℝ) : s ∈ supBlock hold G q p s := by
  by_cases hp : p.1 ∈ G
  · by_cases hex : ∃ k : ℤ, GoodK hold q p.1 p.2 k s
    · rw [supBlock_of_good hold hp hex]
      exact mem_timeBlockAt_self p.2 _ s
    · rw [supBlock_of_bad hold hp hex]
      exact Set.mem_singleton s
  · rw [supBlock_of_not_mem hold hp]
    exact mem_timeBlockAt_self p.2 _ s

theorem volume_supBlock_lt_top (q : ℚ) (p : Ω × Grid) (s : ℝ) :
    volume (supBlock hold G q p s) < ⊤ := by
  by_cases hp : p.1 ∈ G
  · by_cases hex : ∃ k : ℤ, GoodK hold q p.1 p.2 k s
    · rw [supBlock_of_good hold hp hex, volume_timeBlockAt]
      exact ENNReal.ofReal_lt_top
    · rw [supBlock_of_bad hold hp hex, Real.volume_singleton]
      exact ENNReal.zero_lt_top
  · rw [supBlock_of_not_mem hold hp, volume_timeBlockAt]
    exact ENNReal.ofReal_lt_top

section Gate

variable (hd : HoldingData G θΩ SΩ hold)
include hd

theorem good_selLevelK {q : ℚ} {ω : Ω} (hω : ω ∈ G) {D : Grid} {s : ℝ}
    (hex : ∃ k : ℤ, GoodK hold q ω D k s) : GoodK hold q ω D (selLevelK hold q ω D s) s :=
  Int.csSup_mem hex (bddAbove_goodK hold hd hω q D s)

theorem le_selLevelK {q : ℚ} {ω : Ω} (hω : ω ∈ G) {D : Grid} {k : ℤ} {s : ℝ}
    (hk : GoodK hold q ω D k s) : k ≤ selLevelK hold q ω D s :=
  le_csSup (bddAbove_goodK hold hd hω q D s) hk

theorem not_goodK_succ_selLevelK {q : ℚ} {ω : Ω} (hω : ω ∈ G) {D : Grid} {s : ℝ} :
    ¬ GoodK hold q ω D (selLevelK hold q ω D s + 1) s := fun h => by
  have := le_selLevelK hold hd hω h
  omega

theorem selLevelK_eq_of {q : ℚ} {ω : Ω} (hω : ω ∈ G) {D : Grid} {k : ℤ} {s : ℝ}
    (hk : GoodK hold q ω D k s) (hk1 : ¬ GoodK hold q ω D (k + 1) s) :
    selLevelK hold q ω D s = k := by
  refine le_antisymm ?_ (le_selLevelK hold hd hω hk)
  by_contra hlt
  have hlt' : k < sSup {k : ℤ | GoodK hold q ω D k s} := not_le.1 hlt
  obtain ⟨a, ha, hka⟩ := exists_lt_of_lt_csSup ⟨k, hk⟩ hlt'
  exact hk1 (GoodK.mono_level hold (show k + 1 ≤ a by omega) ha)

/-! ## 2. The partition -/

/-- **The blocks partition the time axis.** -/
theorem supBlock_eq_of_mem {q : ℚ} {p : Ω × Grid} {s t : ℝ} (ht : t ∈ supBlock hold G q p s) :
    supBlock hold G q p t = supBlock hold G q p s := by
  by_cases hp : p.1 ∈ G
  · by_cases hex : ∃ k : ℤ, GoodK hold q p.1 p.2 k s
    · rw [supBlock_of_good hold hp hex] at ht
      have hgood : GoodK hold q p.1 p.2 (selLevelK hold q p.1 p.2 s) t :=
        (goodK_iff_of_mem hold le_rfl ht).2 (good_selLevelK hold hd hp hex)
      have hbad : ¬ GoodK hold q p.1 p.2 (selLevelK hold q p.1 p.2 s + 1) t := fun h =>
        not_goodK_succ_selLevelK hold hd hp ((goodK_iff_of_mem hold (by omega) ht).1 h)
      have hex' : ∃ k : ℤ, GoodK hold q p.1 p.2 k t := ⟨_, hgood⟩
      rw [supBlock_of_good hold hp hex', supBlock_of_good hold hp hex,
        selLevelK_eq_of hold hd hp hgood hbad]
      exact timeBlockAt_eq_of_mem ht
    · rw [supBlock_of_bad hold hp hex, Set.mem_singleton_iff] at ht
      rw [ht]
  · rw [supBlock_of_not_mem hold hp] at ht
    rw [supBlock_of_not_mem hold hp, supBlock_of_not_mem hold hp]
    exact timeBlockAt_eq_of_mem ht

/-! ## 3. Covariance -/

theorem exists_goodK_shift {q : ℚ} {ω : Ω} (hω : ω ∈ G) (r : ℝ) (D : Grid) (s : ℝ) :
    (∃ k : ℤ, GoodK hold q (θΩ r ω) (translate (timeVec r) D) k s)
      ↔ ∃ k : ℤ, GoodK hold q ω D k (s + r) :=
  exists_congr fun k => goodK_shift hold hd hω q r D k s

theorem selLevelK_shift {q : ℚ} {ω : Ω} (hω : ω ∈ G) (r : ℝ) (D : Grid) (s : ℝ) :
    selLevelK hold q (θΩ r ω) (translate (timeVec r) D) s = selLevelK hold q ω D (s + r) := by
  unfold selLevelK
  congr 1
  ext k
  exact goodK_shift hold hd hω q r D k s

/-- **Flow covariance of the blocks, at every point.** -/
theorem supBlock_shift {θ : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (q : ℚ) (p : Ω × Grid) (r s : ℝ) :
    supBlock hold G q (θ r p) s = {x : ℝ | x + r ∈ supBlock hold G q p (s + r)} := by
  obtain ⟨ω, D⟩ := p
  rw [hθ]
  by_cases hω : ω ∈ G
  · have hω' : θΩ r ω ∈ G := (hd.flow_mem r ω).2 hω
    by_cases hex : ∃ k : ℤ, GoodK hold q ω D k (s + r)
    · have hex' : ∃ k : ℤ, GoodK hold q (θΩ r ω) (translate (timeVec r) D) k s :=
        (exists_goodK_shift hold hd hω r D s).2 hex
      rw [supBlock_of_good hold (p := (θΩ r ω, translate (timeVec r) D)) hω' hex',
        supBlock_of_good hold (p := (ω, D)) hω hex]
      show timeBlockAt (translate (timeVec r) D)
          (selLevelK hold q (θΩ r ω) (translate (timeVec r) D) s) s
        = {x : ℝ | x + r ∈ timeBlockAt D (selLevelK hold q ω D (s + r)) (s + r)}
      rw [selLevelK_shift hold hd hω, timeBlockAt_translate_timeVec]
    · have hex' : ¬ ∃ k : ℤ, GoodK hold q (θΩ r ω) (translate (timeVec r) D) k s :=
        fun h => hex ((exists_goodK_shift hold hd hω r D s).1 h)
      rw [supBlock_of_bad hold (p := (θΩ r ω, translate (timeVec r) D)) hω' hex',
        supBlock_of_bad hold (p := (ω, D)) hω hex]
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact ⟨fun h => by rw [h], fun h => by linarith⟩
  · have hω' : θΩ r ω ∉ G := fun h => hω ((hd.flow_mem r ω).1 h)
    rw [supBlock_of_not_mem hold (p := (θΩ r ω, translate (timeVec r) D)) hω',
      supBlock_of_not_mem hold (p := (ω, D)) hω]
    exact timeBlockAt_translate_timeVec D r ⌊q⌋ s

theorem exists_goodK_scale {q : ℚ} {ω : Ω} (hω : ω ∈ G) {C : ℝ} (hC : 0 < C) (D : Grid)
    (s : ℝ) :
    (∃ k : ℤ, GoodK hold q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) k (C ^ 2 * s))
      ↔ ∃ k : ℤ, GoodK hold q ω D k s := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - levelShift (C ^ 2) D, (goodK_scale hold hd hω q hC D _ s).1 ?_⟩
    rwa [sub_add_cancel]
  · rintro ⟨k, hk⟩
    exact ⟨k + levelShift (C ^ 2) D, (goodK_scale hold hd hω q hC D k s).2 hk⟩

theorem selLevelK_scale {q : ℚ} {ω : Ω} (hω : ω ∈ G) {C : ℝ} (hC : 0 < C) (D : Grid) {s : ℝ}
    (hex : ∃ k : ℤ, GoodK hold q ω D k s) :
    selLevelK hold q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (C ^ 2 * s)
      = selLevelK hold q ω D s + levelShift (C ^ 2) D := by
  have hω' : SΩ C ω ∈ G := (hd.scale_mem C hC ω).2 hω
  refine selLevelK_eq_of hold hd hω'
    ((goodK_scale hold hd hω q hC D _ s).2 (good_selLevelK hold hd hω hex)) ?_
  intro h
  have h' : GoodK hold q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D)
      ((selLevelK hold q ω D s + 1) + levelShift (C ^ 2) D) (C ^ 2 * s) := by
    rwa [show selLevelK hold q ω D s + 1 + levelShift (C ^ 2) D
        = selLevelK hold q ω D s + levelShift (C ^ 2) D + 1 by ring]
  exact not_goodK_succ_selLevelK hold hd hω ((goodK_scale hold hd hω q hC D _ s).1 h')

/-- **Parabolic covariance of the blocks on the gate.** -/
theorem supBlock_scale_of_mem {S : ℝ → Ω × Grid → Ω × Grid}
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d)) (q : ℚ) {C : ℝ}
    (hC : 0 < C) {p : Ω × Grid} (hp : p.1 ∈ G) (s : ℝ) :
    supBlock hold G q (S C p) (C ^ 2 * s) = (fun x : ℝ => C ^ 2 * x) '' supBlock hold G q p s := by
  obtain ⟨ω, D⟩ := p
  have hω : ω ∈ G := hp
  have hω' : SΩ C ω ∈ G := (hd.scale_mem C hC ω).2 hω
  rw [hS, gridScale_of_pos hC]
  by_cases hex : ∃ k : ℤ, GoodK hold q ω D k s
  · have hex' := (exists_goodK_scale hold hd hω hC D s).2 hex
    rw [supBlock_of_good hold (p := (SΩ C ω, dilate (C ^ 2) (pow_pos hC 2) D)) hω' hex',
      supBlock_of_good hold (p := (ω, D)) hω hex]
    show timeBlockAt (dilate (C ^ 2) (pow_pos hC 2) D)
        (selLevelK hold q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (C ^ 2 * s)) (C ^ 2 * s)
      = (fun x : ℝ => C ^ 2 * x) '' timeBlockAt D (selLevelK hold q ω D s) s
    rw [selLevelK_scale hold hd hω hC D hex, timeBlockAt_dilate]
  · have hex' : ¬ ∃ k : ℤ, GoodK hold q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) k
        (C ^ 2 * s) := fun h => hex ((exists_goodK_scale hold hd hω hC D s).1 h)
    rw [supBlock_of_bad hold (p := (SΩ C ω, dilate (C ^ 2) (pow_pos hC 2) D)) hω' hex',
      supBlock_of_bad hold (p := (ω, D)) hω hex, Set.image_singleton]

/-! ## 4. Measurability -/

theorem measurableSet_goodK_on (q : ℚ) (k : ℤ) :
    MeasurableSet {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ GoodK hold q y.1.1 y.1.2 k y.2} :=
  (measurable_fst.fst hd.measurableSet_gate).inter (measurableSet_goodK hold hd q k)

theorem measurableSet_graph_supBlock (q : ℚ) :
    MeasurableSet {x : (Ω × Grid) × ℝ × ℝ | x.2.2 ∈ supBlock hold G q x.1 x.2.1} := by
  have hmap : Measurable fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ) :=
    measurable_fst.prodMk measurable_snd.fst
  have hmap2 : Measurable fun x : (Ω × Grid) × ℝ × ℝ =>
      (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ) :=
    ((measurable_fst.snd).prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hA : ∀ k : ℤ, MeasurableSet ((fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ))
      ⁻¹' {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ GoodK hold q y.1.1 y.1.2 k y.2}) :=
    fun k => hmap (measurableSet_goodK_on hold hd q k)
  have hB : ∀ k : ℤ, MeasurableSet ((fun x : (Ω × Grid) × ℝ × ℝ =>
      (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ)) ⁻¹'
        {z : (Grid × ℝ) × ℝ | z.2 ∈ timeBlockAt z.1.1 k z.1.2}) :=
    fun k => hmap2 (measurableSet_mem_timeBlockAt k)
  have hG : MeasurableSet ((fun x : (Ω × Grid) × ℝ × ℝ => x.1.1) ⁻¹' G) :=
    measurable_fst.fst hd.measurableSet_gate
  have hdiag : MeasurableSet {x : (Ω × Grid) × ℝ × ℝ | x.2.2 = x.2.1} := by
    have h1 : MeasurableSet {x : (Ω × Grid) × ℝ × ℝ | x.2.2 ≤ x.2.1} :=
      measurableSet_le measurable_snd.snd measurable_snd.fst
    have h2 : MeasurableSet {x : (Ω × Grid) × ℝ × ℝ | x.2.1 ≤ x.2.2} :=
      measurableSet_le measurable_snd.fst measurable_snd.snd
    have hEq : {x : (Ω × Grid) × ℝ × ℝ | x.2.2 = x.2.1}
        = {x : (Ω × Grid) × ℝ × ℝ | x.2.2 ≤ x.2.1} ∩ {x : (Ω × Grid) × ℝ × ℝ | x.2.1 ≤ x.2.2} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    rw [hEq]
    exact h1.inter h2
  have hset : {x : (Ω × Grid) × ℝ × ℝ | x.2.2 ∈ supBlock hold G q x.1 x.2.1}
      = (⋃ k : ℤ, (((fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ)) ⁻¹'
            {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ GoodK hold q y.1.1 y.1.2 k y.2})
          ∩ ((fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ)) ⁻¹'
            {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ GoodK hold q y.1.1 y.1.2 (k + 1) y.2})ᶜ)
          ∩ ((fun x : (Ω × Grid) × ℝ × ℝ => (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ)) ⁻¹'
            {z : (Grid × ℝ) × ℝ | z.2 ∈ timeBlockAt z.1.1 k z.1.2}))
        ∪ (((fun x : (Ω × Grid) × ℝ × ℝ => x.1.1) ⁻¹' G)
          ∩ (⋂ k : ℤ, ((fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ)) ⁻¹'
            {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ GoodK hold q y.1.1 y.1.2 k y.2})ᶜ)
          ∩ {x : (Ω × Grid) × ℝ × ℝ | x.2.2 = x.2.1})
        ∪ (((fun x : (Ω × Grid) × ℝ × ℝ => x.1.1) ⁻¹' G)ᶜ
          ∩ ((fun x : (Ω × Grid) × ℝ × ℝ => (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ)) ⁻¹'
            {z : (Grid × ℝ) × ℝ | z.2 ∈ timeBlockAt z.1.1 ⌊q⌋ z.1.2})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_compl_iff, Set.mem_iInter]
    by_cases hx : x.1.1 ∈ G
    · by_cases hex : ∃ k : ℤ, GoodK hold q x.1.1 x.1.2 k x.2.1
      · rw [supBlock_of_good hold (p := x.1) hx hex]
        constructor
        · intro h
          exact Or.inl (Or.inl ⟨selLevelK hold q x.1.1 x.1.2 x.2.1,
            ⟨⟨hx, good_selLevelK hold hd hx hex⟩,
              fun h' => not_goodK_succ_selLevelK hold hd hx h'.2⟩, h⟩)
        · rintro ((⟨k, ⟨⟨-, hk⟩, hk1⟩, h⟩ | ⟨⟨-, hall⟩, _⟩) | ⟨hn, _⟩)
          · rw [selLevelK_eq_of hold hd hx hk (fun h' => hk1 ⟨hx, h'⟩)]
            exact h
          · obtain ⟨k, hk⟩ := hex
            exact absurd ⟨hx, hk⟩ (hall k)
          · exact absurd hx hn
      · rw [supBlock_of_bad hold (p := x.1) hx hex, Set.mem_singleton_iff]
        constructor
        · intro h
          exact Or.inl (Or.inr ⟨⟨hx, fun k hk => hex ⟨k, hk.2⟩⟩, h⟩)
        · rintro ((⟨k, ⟨⟨-, hk⟩, -⟩, -⟩ | ⟨⟨-, -⟩, h⟩) | ⟨hn, _⟩)
          · exact absurd ⟨k, hk⟩ hex
          · exact h
          · exact absurd hx hn
    · rw [supBlock_of_not_mem hold (p := x.1) hx]
      constructor
      · intro h
        exact Or.inr ⟨hx, h⟩
      · rintro ((⟨k, ⟨⟨hG', -⟩, -⟩, -⟩ | ⟨⟨hG', -⟩, _⟩) | ⟨-, h⟩)
        · exact absurd hG' hx
        · exact absurd hG' hx
        · exact h
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_
  · exact MeasurableSet.iUnion fun k => ((hA k).inter (hA (k + 1)).compl).inter (hB k)
  · exact (hG.inter (MeasurableSet.iInter fun k => (hA k).compl)).inter hdiag
  · exact hG.compl.inter (hB ⌊q⌋)

/-! ## 5. Length -/

/-- **Positive length at every vertex time** (on the gate; everywhere off the gate). -/
theorem volume_supBlock_pos_of_ne_zero (q : ℚ) (p : Ω × Grid) {s : ℝ}
    (hs : p.1 ∈ G → hold p.1 s ≠ 0) : 0 < volume (supBlock hold G q p s) := by
  by_cases hp : p.1 ∈ G
  · have hex : ∃ k : ℤ, GoodK hold q p.1 p.2 k s := exists_goodK hold hd hp (hs hp) q p.2
    rw [supBlock_of_good hold hp hex, volume_timeBlockAt]
    exact ENNReal.ofReal_pos.2 (side_pos _ _)
  · rw [supBlock_of_not_mem hold hp, volume_timeBlockAt]
    exact ENNReal.ofReal_pos.2 (side_pos _ _)

/-- **Positive length at almost every time** ("for almost every `s`"). -/
theorem volume_supBlock_pos_ae (q : ℚ) (p : Ω × Grid) :
    ∀ᵐ s ∂(volume : Measure ℝ), 0 < volume (supBlock hold G q p s) := by
  by_cases hp : p.1 ∈ G
  · have hnull := hd.null_zero p.1 hp
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hnull
    by_contra h0
    exact hs (volume_supBlock_pos_of_ne_zero hold hd q p fun _ => h0)
  · exact Filter.Eventually.of_forall fun s =>
      volume_supBlock_pos_of_ne_zero hold hd q p fun h => absurd h hp

/-! ## 6. Nesting in the parameter -/

theorem supBlock_nested {q q' : ℚ} (hq : q ≤ q') (p : Ω × Grid) :
    supBlock hold G q p 0 ⊆ supBlock hold G q' p 0 := by
  by_cases hp : p.1 ∈ G
  · by_cases hex' : ∃ k : ℤ, GoodK hold q' p.1 p.2 k 0
    · by_cases hex : ∃ k : ℤ, GoodK hold q p.1 p.2 k 0
      · rw [supBlock_of_good hold hp hex, supBlock_of_good hold hp hex']
        exact timeBlockAt_subset_of_le p.2
          (le_selLevelK hold hd hp ((good_selLevelK hold hd hp hex).mono_q hold hq)) 0
      · rw [supBlock_of_bad hold hp hex]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact self_mem_supBlock hold q' p 0
    · have hex : ¬ ∃ k : ℤ, GoodK hold q p.1 p.2 k 0 := fun ⟨k, hk⟩ => hex' ⟨k, hk.mono_q hold hq⟩
      rw [supBlock_of_bad hold hp hex, supBlock_of_bad hold hp hex']
  · rw [supBlock_of_not_mem hold hp, supBlock_of_not_mem hold hp]
    exact timeBlockAt_subset_of_le p.2 (Int.floor_mono hq) 0

/-! ## 7. The root chain: every root block occurs on a nonempty parameter interval -/

/-- On the gate, for every level `n` there is a rational parameter at which the level-`n` root
block is good and its parent is not: `κ(J_n) ≤ 2^q < κ(J_{n+1})`. -/
theorem exists_sel_rat {ω : Ω} (hω : ω ∈ G) (D : Grid) (n : ℕ) :
    ∃ q : ℚ, GoodK hold q ω D n 0 ∧ ¬ GoodK hold q ω D ((n : ℤ) + 1) 0 := by
  have h0 := kappa_pos hold hd hω D n 0
  have hT := kappa_lt_top hold hd hω D n 0
  have hT' := kappa_lt_top hold hd hω D ((n : ℤ) + 1) 0
  have hlt := kappa_lt_succ hold hd hω D n 0
  have ha : 0 < (kappa hold ω D n 0).toReal := ENNReal.toReal_pos h0.ne' hT.ne
  have hab : (kappa hold ω D n 0).toReal < (kappa hold ω D ((n : ℤ) + 1) 0).toReal :=
    (ENNReal.toReal_lt_toReal hT.ne hT'.ne).2 hlt
  have hb : 0 < (kappa hold ω D ((n : ℤ) + 1) 0).toReal := ha.trans hab
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.logb_lt_logb one_lt_two ha hab)
  refine ⟨q, ?_, ?_⟩
  · unfold GoodK
    rw [← ENNReal.ofReal_toReal hT.ne]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (kappa hold ω D n 0).toReal
        = (2 : ℝ) ^ Real.logb 2 (kappa hold ω D n 0).toReal :=
          (Real.rpow_logb (by norm_num) (by norm_num) ha).symm
      _ ≤ (2 : ℝ) ^ (q : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1.le
  · unfold GoodK
    rw [← ENNReal.ofReal_toReal hT'.ne, not_le, ENNReal.ofReal_lt_ofReal_iff hb]
    calc (2 : ℝ) ^ (q : ℝ)
        < (2 : ℝ) ^ Real.logb 2 (kappa hold ω D ((n : ℤ) + 1) 0).toReal :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hq2
      _ = (kappa hold ω D ((n : ℤ) + 1) 0).toReal := Real.rpow_logb (by norm_num) (by norm_num) hb

open Classical in
/-- **The selecting parameters**: on the gate a rational `q` with `κ(J_n) ≤ 2^q < κ(J_{n+1})` at
the origin; off the gate the level itself. -/
noncomputable def supSel (p : Ω × Grid) (n : ℕ) : ℚ :=
  if h : p.1 ∈ G then Classical.choose (exists_sel_rat hold hd h p.2 n) else (n : ℚ)

theorem supSel_spec {p : Ω × Grid} (hp : p.1 ∈ G) (n : ℕ) :
    GoodK hold (supSel hold hd p n) p.1 p.2 n 0
      ∧ ¬ GoodK hold (supSel hold hd p n) p.1 p.2 ((n : ℤ) + 1) 0 := by
  unfold supSel
  rw [dif_pos hp]
  exact Classical.choose_spec (exists_sel_rat hold hd hp p.2 n)

theorem supSel_of_not_mem {p : Ω × Grid} (hp : p.1 ∉ G) (n : ℕ) :
    supSel hold hd p n = (n : ℚ) := by
  unfold supSel
  rw [dif_neg hp]

/-- **`selection_root`**: the level-`n` root block is the block at the selected parameter. -/
theorem selection_root_supSel (n : ℕ) (p : Ω × Grid) :
    rootTimeBlock p.2 (n : ℤ) = supBlock hold G (supSel hold hd p n) p 0 := by
  by_cases hp : p.1 ∈ G
  · obtain ⟨hgood, hbad⟩ := supSel_spec hold hd hp n
    simp only [supBlock_of_good hold hp ⟨_, hgood⟩, selLevelK_eq_of hold hd hp hgood hbad]
    rfl
  · rw [supBlock_of_not_mem hold hp, supSel_of_not_mem hold hd hp]
    show timeBlockAt p.2 (n : ℤ) 0 = timeBlockAt p.2 ⌊((n : ℕ) : ℚ)⌋ 0
    rw [Int.floor_natCast]

/-- On the gate, beyond some level no block through the origin is good at a fixed parameter. -/
theorem eventually_not_goodK {ω : Ω} (hω : ω ∈ G) (Q : ℚ) (D : Grid) :
    ∃ k₀ : ℤ, ∀ k : ℤ, k₀ ≤ k → ¬ GoodK hold Q ω D k 0 := by
  obtain ⟨k₀, hk₀⟩ := exists_not_goodK hold hd hω Q D 0
  exact ⟨k₀, fun k hk hg => hk₀ (GoodK.mono_level hold hk hg)⟩

/-- **`selection_tendsto`**: the selected parameters tend to infinity along the root chain. -/
theorem tendsto_supSel (p : Ω × Grid) : Tendsto (supSel hold hd p) atTop atTop := by
  by_cases hp : p.1 ∈ G
  · refine tendsto_atTop.2 fun Q => ?_
    obtain ⟨k₀, hk₀⟩ := eventually_not_goodK hold hd hp Q p.2
    refine eventually_atTop.2 ⟨k₀.toNat, fun n hn => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hgood := (supSel_spec hold hd hp n).1
    have hk : k₀ ≤ (n : ℤ) := le_trans (Int.self_le_toNat k₀) (by exact_mod_cast hn)
    exact hk₀ n hk (hgood.mono_q hold hlt.le)
  · have hEq : supSel hold hd p = fun n : ℕ => (n : ℚ) := funext fun n => supSel_of_not_mem hold hd hp n
    rw [hEq]
    exact tendsto_natCast_atTop_atTop

end Gate

end ReflectedGMS.SupTypeTimeBlocks
