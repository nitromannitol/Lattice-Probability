/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RootBlockGridProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GridBlockTransfer
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ActualDyadicTemporalBlocks
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridDilationInvariance
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicCylinderLaw
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableEndpointTransport

/-!
# `p:eq:gridprob` for the actual dyadic temporal blocks

`ReflectedGMS/Limit/GridBlockTransfer.lean` carries out the transfer step of
`p:prop:timeergodic` from two named probabilistic inputs about the grid law, bundled as
`GridBlockTransfer.GridChainData`.  This module **discharges every one of those inputs that
is a statement about the grid law alone**, for the actual one-dimensional marked dyadic
system of `Temporal/ActualDyadicTemporalBlocks`, leaving only the density-side hypotheses
and the complete-chain convergence `p:lem:timeconverge`.

## The blocks

The manuscript's *root blocks* at time `0` are the ancestor chain of the time origin:
`rootTimeBlock D k = timeBlockAt D k 0` is the level-`k` half-open dyadic time interval of
the marked grid `D` that contains `0`.  This is forced, not chosen: the event of
`p:eq:gridprob` asks for a block containing `(0,T]`, and every such block contains `0`.
`rootTimeBlock_eq` identifies it as `[o_k, o_k + 2^{φ+k})` where `o_k = D.origin k 0 ≤ 0`
is the grid origin at level `k` and `φ = D.phase` is the logarithmic phase, so the two
randomisations of the manuscript's "independent uniform one-dimensional dyadic system" —
the **log phase** and the **origin position** — are exactly the two coordinates that decide
the event.

## `p:eq:gridprob`

`grid_rootTimeBlock` is the `grid` field of `GridChainData` verbatim:

```
∀ δ > 0, ∃ p > 0, ∀ T > 0, ENNReal.ofReal p ≤ ν (gridBlockEvent rootTimeBlock δ T)
```

for **every** law `ν` realising `DyadicApproximation.UniformGridLaw`, hence unconditionally
for the constructed `DyadicGridLaw.gridMeasure`
(`Forms/DyadicCylinderLaw.uniformGridLaw_gridMeasure`).  No new probability primitive is
used: the whole input is the cylinder law at level `0` and depth `0`.

The two shape constraints of the field are met exactly, and neither can be improved:

* the constant depends on `δ` — it must, since as `δ ↓ 0` the events decrease to "a root
  block has length exactly `T`", a null event;
* the constant does **not** depend on `T`.  That is the load-bearing half, and it is free:
  by `UniformGridDilationInvariance.map_dilate_of_uniformGridLaw` the law is invariant under
  dilation by *every* positive real `s`, and `dilate_mem_gridBlockEvent` shows the scale-`T`
  event contains the image of the scale-one event under dilation by `T`, because the whole
  block family scales (`side_dilate`, `dilatedOrigin`) with the level reindexed by
  `levelShift T D`.  So `ν (E_δ(1)) ≤ ν (E_δ(T))` for every `T > 0`, and one positive
  constant at scale one serves every `T`.

At scale one, positivity is a two-coordinate computation on the level-`0` cylinder
(`measure_tightGrid`): on the phase window `[log₂(1+δ/2), log₂(1+δ)]` the level-`0` side
length lies in `[1+δ/2, 1+δ]`, and on the origin window `-o_0/σ_0 < δ/4` the block reaches
past `1`, since `σ_0(1 - δ/4) ≥ (1+δ/2)(1-δ/4) > 1`.  Both windows have positive measure and
the resulting constant

```
p_δ = (log₂(1+δ') - log₂(1+δ'/2)) · (δ'/4)²,     δ' = min δ (1/2),
```

is a lower bound for the manuscript's sharp `(log 2)⁻¹ ∫₁^{1+δ}(r-1)r⁻² dr`; the field asks
only for a positive constant, so the sharp value is not needed.  *Both* randomisations enter:
the phase alone cannot place a block boundary to the left of the origin, and the origin
position alone cannot make the block long enough.

## What else is discharged

`gridChainData_of_rootBlockDensity` assembles `GridChainData` from the residual data
`RootBlockDensity`, i.e. from the density-side hypotheses (nonnegativity, local
integrability) and the chain convergence alone: the block measurability, the positivity and
finiteness of the block lengths, and the measurability of the grid event
(`measurableSet_gridBlockEvent_rootTimeBlock`) are all proved here.

## What is *not* proved here

The `chain` field — `p:lem:timeconverge` with its limit identified as `𝔼[Γ]` — and the
density-side integrability.  Those are the content of `RootBlockDensity`, which is a
hypothesis everywhere below.  Nothing here certifies `p:lem:timeconverge`,
`p:prop:timeergodic`, `p:thm:areaclt` or either main theorem, and no ergodicity, no
triviality of a tail σ-field and no time-shift invariance of any law is assumed or asserted.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.RootBlockGridProbability

open ReflectedGMS.DyadicApproximation ReflectedGMS.UniformGridDilationInvariance
open ReflectedGMS.Temporal.ActualDyadicTemporalBlocks
open ReflectedGMS.MartingaleIngredients ReflectedGMS.MartingaleLimit
open ReflectedGMS.BracketTimeAverage ReflectedGMS.GridBlockTransfer

/-! ### The root time blocks -/

/-- **The root blocks of the marked dyadic time grid**: the level-`k` half-open dyadic time
interval containing the time origin.  This is the manuscript's ancestor chain through time
`0`, i.e. exactly the family of blocks that can contain an interval `(0,T]`. -/
noncomputable def rootTimeBlock (D : Grid) (k : ℤ) : Set ℝ := timeBlockAt D k 0

/-- The time origin sits in the level-`k` block of index `0`: the grid origin is in
`(-side, 0]`, so the containing index of the time `0` is `0`. -/
theorem timeIndexAt_zero (D : Grid) (k : ℤ) : timeIndexAt D k 0 = 0 := by
  have hσ : (0 : ℝ) < side D k := side_pos D k
  obtain ⟨h1, h2⟩ := D.origin_position k 0
  have hside : side D k = (2 : ℝ) ^ (D.phase + (k : ℝ)) := rfl
  have hcoord : timeCoord D k 0 = (0 - D.origin k 0) / side D k := rfl
  show ⌊timeCoord D k 0⌋ = 0
  refine Int.floor_eq_zero_iff.2 (Set.mem_Ico.2 ⟨?_, ?_⟩)
  · rw [hcoord]
    exact div_nonneg (by linarith) hσ.le
  · rw [hcoord, div_lt_one hσ, hside]
    linarith

/-- The root block in closed form: `[o_k, o_k + 2^{φ+k})`. -/
theorem rootTimeBlock_eq (D : Grid) (k : ℤ) :
    rootTimeBlock D k = Set.Ico (D.origin k 0) (D.origin k 0 + side D k) := by
  have hlow : timeLowerAt D k 0 = D.origin k 0 := by
    have h : timeLowerAt D k 0 = D.origin k 0 + side D k * ((timeIndexAt D k 0 : ℤ) : ℝ) := rfl
    rw [h, timeIndexAt_zero]
    push_cast
    ring
  show timeBlockAt D k 0 = Set.Ico (D.origin k 0) (D.origin k 0 + side D k)
  simp only [timeBlockAt, hlow]

theorem measurableSet_rootTimeBlock (D : Grid) (k : ℤ) : MeasurableSet (rootTimeBlock D k) :=
  measurableSet_timeBlockAt D k 0

theorem volume_rootTimeBlock (D : Grid) (k : ℤ) :
    volume (rootTimeBlock D k) = ENNReal.ofReal (side D k) := by
  rw [rootTimeBlock_eq, Real.volume_Ico]
  congr 1
  ring

theorem volume_rootTimeBlock_ne_zero (D : Grid) (k : ℤ) : volume (rootTimeBlock D k) ≠ 0 := by
  rw [volume_rootTimeBlock]
  exact fun h => absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 (side_pos D k))

theorem volume_rootTimeBlock_ne_top (D : Grid) (k : ℤ) : volume (rootTimeBlock D k) ≠ ⊤ := by
  rw [volume_rootTimeBlock]
  exact ENNReal.ofReal_ne_top

/-! ### Measurability of the grid event -/

/-- **The event of `p:eq:gridprob` is measurable.**  It is a countable union over the levels
of the chain, and at a fixed level it is cut out by the two grid coordinates
`D ↦ D.origin k 0` and `D ↦ side D k`. -/
theorem measurableSet_gridBlockEvent_rootTimeBlock (δ T : ℝ) :
    MeasurableSet (gridBlockEvent rootTimeBlock δ T) := by
  have hset : gridBlockEvent rootTimeBlock δ T
      = ⋃ k : ℤ, ({D : Grid | Set.Ioc (0 : ℝ) T ⊆ rootTimeBlock D k} ∩
          {D : Grid | volume (rootTimeBlock D k) ≤ ENNReal.ofReal ((1 + δ) * T)}) := by
    ext D
    constructor
    · rintro ⟨k, h1, h2⟩
      exact Set.mem_iUnion.2 ⟨k, h1, h2⟩
    · intro hD
      obtain ⟨k, h1, h2⟩ := Set.mem_iUnion.1 hD
      exact ⟨k, h1, h2⟩
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
  · rcases le_or_gt T 0 with hT | hT
    · -- CONDITIONAL, degenerate branch `T ≤ 0`: the interval is empty, the condition vacuous.
      have hempty : Set.Ioc (0 : ℝ) T = ∅ := Set.Ioc_eq_empty (not_lt.2 hT)
      have huniv : {D : Grid | Set.Ioc (0 : ℝ) T ⊆ rootTimeBlock D k} = Set.univ := by
        ext D
        simp [hempty]
      rw [huniv]
      exact MeasurableSet.univ
    · -- CONDITIONAL, main branch `0 < T`: since the origin is `≤ 0`, the containment is the
      -- single inequality `T < o_k + σ_k`.
      have hrw : {D : Grid | Set.Ioc (0 : ℝ) T ⊆ rootTimeBlock D k}
          = {D : Grid | T < D.origin k 0 + side D k} := by
        ext D
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, rootTimeBlock_eq]
        constructor
        · intro hsub
          exact (Set.mem_Ico.1 (hsub (Set.mem_Ioc.2 ⟨hT, le_rfl⟩))).2
        · intro hlt x hx
          exact Set.mem_Ico.2 ⟨le_trans (D.origin_position k 0).2 (Set.mem_Ioc.1 hx).1.le,
            lt_of_le_of_lt (Set.mem_Ioc.1 hx).2 hlt⟩
      rw [hrw]
      exact measurableSet_lt measurable_const
        ((ReflectedGMS.MeasurableEndpointTransport.measurable_gridOrigin k 0).add
          (ReflectedGMS.MeasurableEndpointTransport.measurable_gridSide k))
  · have hrw : {D : Grid | volume (rootTimeBlock D k) ≤ ENNReal.ofReal ((1 + δ) * T)}
        = {D : Grid | ENNReal.ofReal (side D k) ≤ ENNReal.ofReal ((1 + δ) * T)} := by
      ext D
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, volume_rootTimeBlock]
    rw [hrw]
    exact measurableSet_le
      (ReflectedGMS.MeasurableEndpointTransport.measurable_gridSide k).ennreal_ofReal
      measurable_const

/-! ### The tight root block at scale one

Both randomisations of the manuscript's one-dimensional dyadic system enter here: the
logarithmic phase fixes the level-`0` side length in `[1+δ/2, 1+δ]`, and the uniform origin
position keeps the origin in the leftmost `δ/4` fraction of its block, so that the block
still reaches past the time `1`.
-/

/-- The level-`0`, depth-`0` cylinder rectangle prescribing a phase window and an origin
window. -/
def tightCyl (δ : ℝ) : Set (ℝ × ((Fin 2 → ℝ) × (Fin 0 → Fin 2 → Fin 2))) :=
  Set.Icc (Real.logb 2 (1 + δ / 2)) (Real.logb 2 (1 + δ)) ×ˢ
    ((Set.univ.pi fun _ : Fin 2 => Set.Ico (0 : ℝ) (δ / 4)) ×ˢ Set.univ)

theorem measurableSet_tightCyl (δ : ℝ) : MeasurableSet (tightCyl δ) :=
  measurableSet_Icc.prod
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ico).prod MeasurableSet.univ)

/-- The corresponding grid event. -/
def tightGrid (δ : ℝ) : Set Grid := gridCylinder 0 0 ⁻¹' tightCyl δ

/-- **The probability of the tight root block at scale one**, from the cylinder law alone.
The phase factor is the length of the phase window and the origin factor is the square of
the length of the origin window, one factor for each of the two coordinates of the marked
grid. -/
theorem measure_tightGrid {ν : Measure Grid} (hlaw : UniformGridLaw ν) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ν (tightGrid δ)
      = ENNReal.ofReal (Real.logb 2 (1 + δ) - Real.logb 2 (1 + δ / 2))
          * ENNReal.ofReal (δ / 4) ^ 2 := by
  have hA : 0 < Real.logb 2 (1 + δ / 2) := Real.logb_pos (by norm_num) (by linarith)
  have hB : Real.logb 2 (1 + δ) < 1 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlt : Real.log (1 + δ) < Real.log 2 := Real.log_lt_log (by linarith) (by linarith)
    rw [Real.logb, div_lt_one hlog2]
    exact hlt
  have hsubA : Set.Icc (Real.logb 2 (1 + δ / 2)) (Real.logb 2 (1 + δ)) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    exact Set.mem_Ico.2 ⟨le_trans hA.le (Set.mem_Icc.1 hx).1,
      lt_of_le_of_lt (Set.mem_Icc.1 hx).2 hB⟩
  have hsubU : Set.Ico (0 : ℝ) (δ / 4) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    exact Set.mem_Ico.2 ⟨(Set.mem_Ico.1 hx).1, by linarith [(Set.mem_Ico.1 hx).2]⟩
  have hprob : IsProbabilityMeasure (PMF.uniformOfFintype (Fin 0 → Fin 2 → Fin 2)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hphase : (volume.restrict (Set.Ico (0 : ℝ) 1))
      (Set.Icc (Real.logb 2 (1 + δ / 2)) (Real.logb 2 (1 + δ)))
      = ENNReal.ofReal (Real.logb 2 (1 + δ) - Real.logb 2 (1 + δ / 2)) := by
    rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_self_of_subset_left hsubA,
      Real.volume_Icc]
  have hone : (volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico (0 : ℝ) (δ / 4))
      = ENNReal.ofReal (δ / 4) := by
    rw [Measure.restrict_apply' measurableSet_Ico, Set.inter_eq_self_of_subset_left hsubU,
      Real.volume_Ico, sub_zero]
  have hpi : (Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1))
      (Set.univ.pi fun _ : Fin 2 => Set.Ico (0 : ℝ) (δ / 4)) = ENNReal.ofReal (δ / 4) ^ 2 := by
    rw [Measure.pi_pi]
    simp only [hone, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [tightGrid, ← Measure.map_apply
      (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder 0 0) (measurableSet_tightCyl δ),
    hlaw.2 0 0, tightCyl, Measure.prod_prod, Measure.prod_prod, hpi, measure_univ, mul_one,
    hphase]

/-- The tight root block at scale one has positive probability, for every `δ ∈ (0, 1/2]`. -/
theorem measure_tightGrid_pos {ν : Measure Grid} (hlaw : UniformGridLaw ν) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) : 0 < ν (tightGrid δ) := by
  rw [measure_tightGrid hlaw hδ hδ2]
  have hlt : Real.logb 2 (1 + δ / 2) < Real.logb 2 (1 + δ) :=
    Real.logb_lt_logb (by norm_num) (by linarith) (by linarith)
  have h1 : 0 < ENNReal.ofReal (Real.logb 2 (1 + δ) - Real.logb 2 (1 + δ / 2)) :=
    ENNReal.ofReal_pos.2 (by linarith)
  have h2 : 0 < ENNReal.ofReal (δ / 4) := ENNReal.ofReal_pos.2 (by linarith)
  exact ENNReal.mul_pos h1.ne' (pow_ne_zero 2 h2.ne')

/-- **On the tight event the level-`0` root block is a tight cover of `(0,1]`.**  This is
the place where both grid randomisations are used: the phase bounds the block length and the
origin position makes the block reach past `1`. -/
theorem tightGrid_subset_gridBlockEvent {δ δ₀ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδδ : δ ≤ δ₀) : tightGrid δ ⊆ gridBlockEvent rootTimeBlock δ₀ 1 := by
  intro D hD
  obtain ⟨hphase, hrel, -⟩ := hD
  have hph : D.phase ∈ Set.Icc (Real.logb 2 (1 + δ / 2)) (Real.logb 2 (1 + δ)) := hphase
  have hrel' : ∀ i : Fin 2, -D.origin 0 i / side D 0 ∈ Set.Ico (0 : ℝ) (δ / 4) :=
    fun i => hrel i (Set.mem_univ i)
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hσ : (0 : ℝ) < side D 0 := side_pos D 0
  have hside0 : side D 0 = (2 : ℝ) ^ D.phase := by
    have h : side D 0 = (2 : ℝ) ^ (D.phase + (((0 : ℤ)) : ℝ)) := rfl
    rw [h]
    norm_num
  have hlow : 1 + δ / 2 ≤ side D 0 := by
    calc 1 + δ / 2 = (2 : ℝ) ^ (Real.logb 2 (1 + δ / 2)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ (2 : ℝ) ^ D.phase := (Real.rpow_le_rpow_left_iff h2).2 (Set.mem_Icc.1 hph).1
      _ = side D 0 := hside0.symm
  have hhigh : side D 0 ≤ 1 + δ := by
    calc side D 0 = (2 : ℝ) ^ D.phase := hside0
      _ ≤ (2 : ℝ) ^ (Real.logb 2 (1 + δ)) :=
          (Real.rpow_le_rpow_left_iff h2).2 (Set.mem_Icc.1 hph).2
      _ = 1 + δ := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hU : -D.origin 0 0 / side D 0 < δ / 4 := (Set.mem_Ico.1 (hrel' 0)).2
  rw [div_lt_iff₀ hσ] at hU
  have hkey : (1 : ℝ) < D.origin 0 0 + side D 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlow) (by linarith : (0 : ℝ) ≤ 1 - δ / 4),
      mul_nonneg hδ.le (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)]
  show ∃ k : ℤ, Set.Ioc (0 : ℝ) 1 ⊆ rootTimeBlock D k ∧
    volume (rootTimeBlock D k) ≤ ENNReal.ofReal ((1 + δ₀) * 1)
  refine ⟨0, ?_, ?_⟩
  · rw [rootTimeBlock_eq]
    intro x hx
    exact Set.mem_Ico.2 ⟨le_trans (D.origin_position 0 0).2 (Set.mem_Ioc.1 hx).1.le,
      lt_of_le_of_lt (Set.mem_Ioc.1 hx).2 hkey⟩
  · rw [volume_rootTimeBlock, mul_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### `T`-independence by dilation invariance -/

/-- **The scale-`T` event contains the dilate by `T` of the scale-one event.**  Dilating the
grid by `T` multiplies every block by `T` and reindexes the levels by `levelShift T D`. -/
theorem dilate_mem_gridBlockEvent {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) {D : Grid}
    (hD : D ∈ gridBlockEvent rootTimeBlock δ 1) :
    dilate T hT D ∈ gridBlockEvent rootTimeBlock δ T := by
  obtain ⟨k, hsub, hvol⟩ :
      ∃ k : ℤ, Set.Ioc (0 : ℝ) 1 ⊆ rootTimeBlock D k ∧
        volume (rootTimeBlock D k) ≤ ENNReal.ofReal ((1 + δ) * 1) := hD
  have hσ : (0 : ℝ) < side D k := side_pos D k
  have ha : D.origin k 0 ≤ 0 := (D.origin_position k 0).2
  rw [rootTimeBlock_eq] at hsub
  have hkey : (1 : ℝ) < D.origin k 0 + side D k :=
    (Set.mem_Ico.1 (hsub (Set.mem_Ioc.2 ⟨one_pos, le_rfl⟩))).2
  rw [volume_rootTimeBlock, mul_one] at hvol
  have hσle : side D k ≤ 1 + δ :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith : (0 : ℝ) ≤ 1 + δ)).1 hvol
  have hL : k + levelShift T D - levelShift T D = k := by ring
  have horig : (dilate T hT D).origin (k + levelShift T D) 0 = T * D.origin k 0 := by
    show dilatedOrigin T D (k + levelShift T D) 0 = T * D.origin k 0
    rw [dilatedOrigin, hL]
  have hside : side (dilate T hT D) (k + levelShift T D) = T * side D k := by
    rw [side_dilate hT, hL]
  have hblk : rootTimeBlock (dilate T hT D) (k + levelShift T D)
      = Set.Ico (T * D.origin k 0) (T * D.origin k 0 + T * side D k) := by
    rw [rootTimeBlock_eq, horig, hside]
  have hTa : T * D.origin k 0 ≤ 0 := by
    nlinarith [mul_nonneg hT.le (neg_nonneg.2 ha)]
  show ∃ l : ℤ, Set.Ioc (0 : ℝ) T ⊆ rootTimeBlock (dilate T hT D) l ∧
    volume (rootTimeBlock (dilate T hT D) l) ≤ ENNReal.ofReal ((1 + δ) * T)
  refine ⟨k + levelShift T D, ?_, ?_⟩
  · rw [hblk]
    intro x hx
    have hexp : T * (D.origin k 0 + side D k) = T * D.origin k 0 + T * side D k := by ring
    have hTlt : T * 1 < T * (D.origin k 0 + side D k) :=
      mul_lt_mul_of_pos_left hkey hT
    refine Set.mem_Ico.2 ⟨le_trans hTa (Set.mem_Ioc.1 hx).1.le, ?_⟩
    have hxT : x ≤ T := (Set.mem_Ioc.1 hx).2
    rw [hexp] at hTlt
    linarith
  · rw [volume_rootTimeBlock, hside]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_nonneg hT.le (sub_nonneg.2 hσle)]

/-- **The scale-one probability bounds every scale**, by dilation invariance of the uniform
dyadic grid law.  This is the `T`-independence the `grid` field requires. -/
theorem measure_gridBlockEvent_one_le {ν : Measure Grid} (hlaw : UniformGridLaw ν) {δ : ℝ}
    (hδ : 0 < δ) {T : ℝ} (hT : 0 < T) :
    ν (gridBlockEvent rootTimeBlock δ 1) ≤ ν (gridBlockEvent rootTimeBlock δ T) := by
  have hmeas : MeasurableSet (gridBlockEvent rootTimeBlock δ T) :=
    measurableSet_gridBlockEvent_rootTimeBlock δ T
  calc ν (gridBlockEvent rootTimeBlock δ 1)
      ≤ ν (dilate T hT ⁻¹' gridBlockEvent rootTimeBlock δ T) :=
        measure_mono fun D hD => dilate_mem_gridBlockEvent hδ hT hD
    _ = (Measure.map (dilate T hT) ν) (gridBlockEvent rootTimeBlock δ T) :=
        (Measure.map_apply (measurable_dilate T hT) hmeas).symm
    _ = ν (gridBlockEvent rootTimeBlock δ T) := by
        rw [map_dilate_of_uniformGridLaw hlaw hT]

/-! ### `p:eq:gridprob` -/

/-- **`p:eq:gridprob` for the actual dyadic temporal blocks.**  This is the `grid` field of
`GridBlockTransfer.GridChainData` verbatim, for the root blocks of any law realising
`DyadicApproximation.UniformGridLaw`.

The constant is `δ`-dependent — it must be — and `T`-independent, which is what the transfer
argument consumes, since its witness sequence is not known in advance. -/
theorem grid_rootTimeBlock {ν : Measure Grid} (hlaw : UniformGridLaw ν) :
    ∀ δ : ℝ, 0 < δ → ∃ p : ℝ, 0 < p ∧
      ∀ T : ℝ, 0 < T → ENNReal.ofReal p ≤ ν (gridBlockEvent rootTimeBlock δ T) := by
  intro δ hδ
  have : IsProbabilityMeasure ν := hlaw.1
  have hδ'pos : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
  have hδ'le2 : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hδ'le : min δ (1 / 2) ≤ δ := min_le_left _ _
  have hne : ν (tightGrid (min δ (1 / 2))) ≠ ⊤ := measure_ne_top ν _
  have hpos : 0 < ν (tightGrid (min δ (1 / 2))) := measure_tightGrid_pos hlaw hδ'pos hδ'le2
  refine ⟨(ν (tightGrid (min δ (1 / 2)))).toReal, ENNReal.toReal_pos hpos.ne' hne,
    fun T hT => ?_⟩
  rw [ENNReal.ofReal_toReal hne]
  exact le_trans (measure_mono (tightGrid_subset_gridBlockEvent hδ'pos hδ'le2 hδ'le))
    (measure_gridBlockEvent_one_le hlaw hδ hT)

/-! ### The residual data, and `GridChainData` -/

/-- **The residual, grid-law-free inputs of `GridBlockTransfer.GridChainData` for the root
blocks.**  Everything about the grid law itself is proved above; what is left is the
density-side integrability and the complete-chain convergence `p:lem:timeconverge` with its
limit already identified as `μ`.  Nothing here is asserted. -/
structure RootBlockDensity (ν : Measure Grid) (f : ℝ → ℝ) (μ : ℝ) : Prop where
  /-- The density is nonnegative, as in the transfer step of `p:prop:timeergodic`. -/
  nonneg : ∀ s : ℝ, 0 ≤ f s
  /-- The density is locally integrable along the time axis. -/
  intervalIntegrable : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable f volume 0 T
  /-- The density is integrable on every root block. -/
  integrableOn : ∀ (D : Grid) (k : ℤ), IntegrableOn f (rootTimeBlock D k) volume
  /-- **`p:lem:timeconverge`, with its limit identified as `μ`**: for almost every grid,
  every sufficiently long root block has block average within `η` of `μ`. -/
  chain : ∀ᵐ D ∂ν, ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ k : ℤ,
    ENNReal.ofReal R ≤ volume (rootTimeBlock D k) → |setAvg (rootTimeBlock D k) f - μ| ≤ η

/-- **The block data of the transfer step, with every grid-law input discharged.** -/
theorem gridChainData_of_rootBlockDensity {ν : Measure Grid} (hlaw : UniformGridLaw ν)
    {f : ℝ → ℝ} {μ : ℝ} (h : RootBlockDensity ν f μ) : GridChainData ν rootTimeBlock f μ :=
  { nonneg := h.nonneg
    intervalIntegrable := h.intervalIntegrable
    measurableSet_block := measurableSet_rootTimeBlock
    volume_ne_zero := volume_rootTimeBlock_ne_zero
    volume_ne_top := volume_rootTimeBlock_ne_top
    integrableOn := h.integrableOn
    measurableSet_grid := measurableSet_gridBlockEvent_rootTimeBlock
    grid := grid_rootTimeBlock hlaw
    chain := h.chain }

/-- The complete residual data for one nonnegative density: the data for `f` itself together
with the manuscript's truncation family (tex:1561), each member of which is a separate
instance of the temporal machinery and therefore data. -/
def HasRootBlockData (ν : Measure Grid) (f : ℝ → ℝ) (μ : ℝ) : Prop :=
  RootBlockDensity ν f μ ∧
    ∃ g : ℝ → ℝ → ℝ, ∃ μK : ℝ → ℝ,
      (∀ K : ℝ, 0 < K → ∀ s : ℝ, g K s ≤ f s) ∧
      (∀ K : ℝ, 0 < K → ∀ s : ℝ, g K s ≤ K) ∧
      (∀ K : ℝ, 0 < K → RootBlockDensity ν (g K) (μK K)) ∧
      Tendsto μK atTop (𝓝 μ)

theorem hasBlockData_of_hasRootBlockData {ν : Measure Grid} (hlaw : UniformGridLaw ν)
    {f : ℝ → ℝ} {μ : ℝ} (h : HasRootBlockData ν f μ) : HasBlockData ν rootTimeBlock f μ := by
  obtain ⟨hf, g, μK, hgle, hgbdd, hgdata, hμK⟩ := h
  exact ⟨gridChainData_of_rootBlockDensity hlaw hf, g, μK, hgle, hgbdd,
    fun K hK => gridChainData_of_rootBlockDensity hlaw (hgdata K hK), hμK⟩

/-! ### `p:lem:bracketlimit` for the actual quenched array -/

open ReflectedWalk

end ReflectedGMS.RootBlockGridProbability
