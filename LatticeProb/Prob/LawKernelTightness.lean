/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.LawKernelPrecompact

/-!
# Tightness of random continuous kernels

Let `Z` be a metric space and `Y` a metric space, and give `C(Z, Y)` the compact-open topology.
For a base point `z₀` and `L, δ > 0` the *kernel modulus failure* `kernelModulusFailure z₀ L δ`
is the open set of maps `f` for which some two points of the closed ball of radius `L` around `z₀`
at distance at most `δ` have images at distance more than `1 / L`.

* `LatticeProb.exists_isCompact_measure_le_of_kernelModuli`: a family of random elements of
  `C(Z, Y)` is tight as soon as (i) for every `L > 1` there is one `δ > 0`, valid for the whole
  family, such that the modulus failure of level `L` has probability at most `1 / L`, and (ii) for
  every `ζ > 0` there are compact sets `K z ⊆ Y` such that, with probability at least `1 - ζ`,
  all values `f z` lie in `K z`.  This is the Arzelà–Ascoli compactness criterion in
  probabilistic form (no measurability of the random elements is needed).
* `LatticeProb.exists_delta_forall_of_eventually`: if the bound of (i) holds for all large indices
  of a sequence of random elements, it holds for all indices after shrinking `δ`, because each
  random element is continuous.  It is an instance of `LatticeProb.exists_scale_forall_of_eventually`,
  the same statement for any null-measurable events that increase with the scale and have empty
  intersection over all scales.
* `LatticeProb.isTightMeasureSet_map_of_kernelModuli`: tightness of the family of laws.
-/

open Filter Topology Set MeasureTheory Metric

open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Failure

variable {Z Y : Type*} [PseudoMetricSpace Z] [MetricSpace Y]

/-- The modulus failure of level `L` and scale `δ`: some two points of the closed ball of radius
`L` around `z₀` at distance at most `δ` have images at distance more than `1 / L`. -/
def kernelModulusFailure (z₀ : Z) (L δ : ℝ) : Set C(Z, Y) :=
  {f | ∃ z w : Z, dist z z₀ ≤ L ∧ dist w z₀ ≤ L ∧ dist z w ≤ δ ∧ 1 / L < dist (f z) (f w)}

/-- The modulus failure sets are open in the compact-open topology. -/
theorem isOpen_kernelModulusFailure (z₀ : Z) (L δ : ℝ) :
    IsOpen (kernelModulusFailure (Y := Y) z₀ L δ) := by
  have h : kernelModulusFailure (Y := Y) z₀ L δ = ⋃ z : Z, ⋃ w : Z,
      ⋃ (_ : dist z z₀ ≤ L ∧ dist w z₀ ≤ L ∧ dist z w ≤ δ),
        {f : C(Z, Y) | 1 / L < dist (f z) (f w)} := by
    ext f
    constructor
    · rintro ⟨z, w, hz, hw, hzw, h⟩
      exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨w, mem_iUnion.2 ⟨⟨hz, hw, hzw⟩, h⟩⟩⟩
    · intro hf
      obtain ⟨z, hf⟩ := mem_iUnion.1 hf
      obtain ⟨w, hf⟩ := mem_iUnion.1 hf
      obtain ⟨⟨hz, hw, hzw⟩, h⟩ := mem_iUnion.1 hf
      exact ⟨z, w, hz, hw, hzw, h⟩
  rw [h]
  refine isOpen_iUnion fun z => isOpen_iUnion fun w => isOpen_iUnion fun _ => ?_
  exact isOpen_lt continuous_const ((continuous_eval_const z).dist (continuous_eval_const w))

/-- The modulus failure sets decrease with the scale. -/
theorem kernelModulusFailure_mono (z₀ : Z) (L : ℝ) {δ δ' : ℝ} (h : δ ≤ δ') :
    kernelModulusFailure (Y := Y) z₀ L δ ⊆ kernelModulusFailure z₀ L δ' :=
  fun _ ⟨z, w, hz, hw, hzw, hf⟩ => ⟨z, w, hz, hw, hzw.trans h, hf⟩

end Failure

section Main

variable {Z Y ι Ω : Type*} [PseudoMetricSpace Z] [CompactlyCoherentSpace Z] [MetricSpace Y]
  [MeasurableSpace Ω]

/-- **Tightness of random continuous kernels (Arzelà–Ascoli).**  Let `X i : Ω → C(Z, Y)`, `i ∈ ι`,
be maps and `μ i` measures on `Ω`.  Assume that for every `L > 1` there is `δ > 0` with
`μ i {X i ∈ kernelModulusFailure z₀ L δ} ≤ 1 / L` for all `i`, and that for every `ζ > 0` there
are compact sets `K z ⊆ Y` with `μ i {ω | ∃ z, X i ω z ∉ K z} ≤ ζ` for all `i`.  Then for every
`ζ > 0` there is a compact set `K ⊆ C(Z, Y)` with `μ i {X i ∉ K} ≤ ζ` for all `i`. -/
theorem exists_isCompact_measure_le_of_kernelModuli (μ : ι → Measure Ω) (X : ι → Ω → C(Z, Y))
    (z₀ : Z)
    (hmod : ∀ L : ℝ, 1 < L → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, μ i {ω | X i ω ∈ kernelModulusFailure z₀ L δ} ≤ ENNReal.ofReal (1 / L))
    (hpt : ∀ ζ : ℝ, 0 < ζ → ∃ K : Z → Set Y, (∀ z, IsCompact (K z)) ∧
      ∀ i, μ i {ω | ∃ z, X i ω z ∉ K z} ≤ ENNReal.ofReal ζ)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : Set C(Z, Y), IsCompact K ∧ ∀ i, μ i {ω | X i ω ∉ K} ≤ ENNReal.ofReal ζ := by
  obtain ⟨Kz, hKz, hKzμ⟩ := hpt (ζ / 2) (half_pos hζ)
  set ζ' : ℝ := min (ζ / 2) 1 with hζ'
  have hζ'0 : 0 < ζ' := lt_min (half_pos hζ) one_pos
  have hζ'le : ζ' ≤ ζ / 2 := min_le_left _ _
  have hζ'1 : ζ' ≤ 1 := min_le_right _ _
  set L : ℕ → ℝ := fun k => 2 * 2 ^ k / ζ' with hL
  have hL1 : ∀ k, 1 < L k := fun k => by
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    simp only [hL]
    rw [lt_div_iff₀ hζ'0]
    nlinarith
  have hLtop : Tendsto L atTop atTop := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    have h3 : Tendsto (fun k : ℕ => 2 * (2 : ℝ) ^ k) atTop atTop :=
      h2.const_mul_atTop two_pos
    exact h3.atTop_div_const hζ'0
  have hainv : ∀ k, 1 / L k = ζ' / 2 / 2 ^ k := fun k => by
    simp only [hL]
    field_simp
  choose δ hδpos hδ using fun k => hmod (L k) (hL1 k)
  set E : Set C(Z, Y) :=
    {f | (∀ k, f ∉ kernelModulusFailure z₀ (L k) (δ k)) ∧ ∀ z, f z ∈ Kz z} with hE
  have hequi : Equicontinuous ((↑) : E → Z → Y) := by
    have h := equicontinuous_of_ball_modulus ((fun f : C(Z, Y) => (f : Z → Y)) '' E) z₀ ?_
    · exact h.comp (fun f : E =>
        (⟨(f.1 : Z → Y), f.1, f.2, rfl⟩ : (fun f : C(Z, Y) => (f : Z → Y)) '' E))
    · intro L' hL'
      obtain ⟨k, hk⟩ := (hLtop.eventually_ge_atTop L').exists
      refine ⟨δ k, hδpos k, ?_⟩
      rintro _ ⟨f, hf, rfl⟩ z w hz hw hzw
      by_contra hlt
      exact hf.1 k ⟨z, w, hz.le.trans hk, hw.le.trans hk, hzw,
        lt_of_le_of_lt (one_div_le_one_div_of_le (by linarith) hk) (not_le.1 hlt)⟩
  have hK : IsCompact (closure E) :=
    isCompact_closure_of_equicontinuous_of_pointwise_compact E hequi
      (fun z => ⟨Kz z, hKz z, fun f hf => hf.2 z⟩)
  refine ⟨closure E, hK, fun i => ?_⟩
  have hsub : {ω | X i ω ∉ closure E} ⊆ {ω | ∃ z, X i ω z ∉ Kz z} ∪
      ⋃ k, {ω | X i ω ∈ kernelModulusFailure z₀ (L k) (δ k)} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
      not_not] at hnot
    exact hω (subset_closure ⟨fun k => hnot.2 k, hnot.1⟩)
  calc μ i {ω | X i ω ∉ closure E}
      ≤ μ i ({ω | ∃ z, X i ω z ∉ Kz z} ∪
          ⋃ k, {ω | X i ω ∈ kernelModulusFailure z₀ (L k) (δ k)}) := measure_mono hsub
    _ ≤ μ i {ω | ∃ z, X i ω z ∉ Kz z} +
          μ i (⋃ k, {ω | X i ω ∈ kernelModulusFailure z₀ (L k) (δ k)}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ζ / 2) +
          ∑' k, μ i {ω | X i ω ∈ kernelModulusFailure z₀ (L k) (δ k)} :=
        add_le_add (hKzμ i) (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal (ζ / 2) + ∑' k : ℕ, ENNReal.ofReal (ζ' / 2 / 2 ^ k) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        rw [← hainv k]
        exact hδ k i
    _ = ENNReal.ofReal (ζ / 2) + ENNReal.ofReal ζ' := by
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (summable_geometric_two' ζ')]
        rw [show (∑' k : ℕ, ζ' / 2 / 2 ^ k) = ζ' from tsum_geometric_two' ζ']
    _ ≤ ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hζ'le)
    _ = ENNReal.ofReal ζ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Main

section Antitone

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A family of null-measurable sets, increasing with the scale `δ > 0` and with empty intersection
over `δ > 0`, has measure tending to `0` as `δ ↓ 0`. -/
theorem tendsto_measure_of_biInter_eq_empty (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℝ → Set Ω)
    (hA : ∀ δ, NullMeasurableSet (A δ) μ) (hmono : ∀ δ δ', δ ≤ δ' → A δ ⊆ A δ')
    (hempty : (⋂ δ > (0 : ℝ), A δ) = ∅) :
    Tendsto (fun δ : ℝ => μ (A δ)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (s := A) (a := 0) (fun r _ => hA r)
    (fun i j _ hij => hmono i j hij) ⟨1, one_pos, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at h
  exact h

/-- **From large indices to all indices.**  Let `A n δ` be null-measurable events increasing with
`δ`, with empty intersection over `δ > 0` for each `n`.  If `μ n (A n δ₀) ≤ c` for all large `n`
at some scale `δ₀ > 0` and `c > 0`, then there is one scale `δ > 0` with `μ n (A n δ) ≤ c` for all
`n`. -/
theorem exists_scale_forall_of_eventually (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (A : ℕ → ℝ → Set Ω) (hA : ∀ n δ, NullMeasurableSet (A n δ) (μ n))
    (hmono : ∀ n δ δ', δ ≤ δ' → A n δ ⊆ A n δ')
    (hempty : ∀ n, (⋂ δ > (0 : ℝ), A n δ) = ∅) {c : ℝ≥0∞} (hc : 0 < c)
    (hev : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ᶠ n in atTop, μ n (A n δ₀) ≤ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, μ n (A n δ) ≤ c := by
  obtain ⟨δ₀, hδ₀, hN⟩ := hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 hN
  have hsm : ∀ n, ∀ᶠ δ : ℝ in 𝓝[>] 0, μ n (A n δ) ≤ c := fun n =>
    ((tendsto_order.1 (tendsto_measure_of_biInter_eq_empty (μ n) (A n) (hA n) (hmono n)
      (hempty n))).2 _ hc).mono fun _ h => h.le
  have hall := ((Finset.range N).eventually_all.2 fun n _ => hsm n).and (Ioo_mem_nhdsGT hδ₀)
  obtain ⟨δ, hδ, hδ0, hδδ₀⟩ := hall.exists
  refine ⟨δ, hδ0, fun n => ?_⟩
  by_cases hn : n < N
  · exact hδ n (Finset.mem_range.2 hn)
  · exact le_trans (measure_mono (hmono n δ δ₀ hδδ₀.le)) (hN n (not_lt.1 hn))

end Antitone

section Upgrade

variable {Z Y Ω : Type*} [PseudoMetricSpace Z] [ProperSpace Z] [MetricSpace Y]
  [MeasurableSpace Ω]

/-- A continuous map has no modulus failure of level `L > 0` at arbitrarily small scales. -/
theorem iInter_kernelModulusFailure_eq_empty (z₀ : Z) {L : ℝ} (hL : 0 < L) :
    (⋂ δ > (0 : ℝ), kernelModulusFailure (Y := Y) z₀ L δ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun f hf => ?_
  simp only [Set.mem_iInter] at hf
  have huc := (isCompact_closedBall z₀ L).uniformContinuousOn_of_continuous
    f.continuous.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc (1 / L) (by positivity)
  obtain ⟨z, w, hz, hw, hzw, hlt⟩ := hf (δ / 2) (half_pos hδ)
  have := hδf z (mem_closedBall.2 hz) w (mem_closedBall.2 hw) (by linarith)
  exact absurd hlt (not_lt.2 this.le)

/-- **From large indices to all indices for random continuous maps.**  Let `X n` be maps
`Ω → C(Z, Y)` such that the modulus failure events are null-measurable (for instance when `X n` is
almost everywhere measurable).  If the modulus failure of level `L` at some scale `δ₀` has
probability at most `1 / L` for all large `n`, there is one scale `δ > 0` with this property for
all `n`. -/
theorem exists_delta_forall_of_eventually (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (X : ℕ → Ω → C(Z, Y)) (z₀ : Z) {L : ℝ} (hL : 0 < L)
    (hX : ∀ n δ, NullMeasurableSet {ω | X n ω ∈ kernelModulusFailure z₀ L δ} (μ n))
    (hev : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      μ n {ω | X n ω ∈ kernelModulusFailure z₀ L δ} ≤ ENNReal.ofReal (1 / L)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n, μ n {ω | X n ω ∈ kernelModulusFailure z₀ L δ} ≤ ENNReal.ofReal (1 / L) :=
  exists_scale_forall_of_eventually μ (fun n δ => {ω | X n ω ∈ kernelModulusFailure z₀ L δ}) hX
    (fun _ _ _ h _ hω => kernelModulusFailure_mono z₀ L h hω)
    (fun n => by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have := iInter_kernelModulusFailure_eq_empty (Y := Y) z₀ hL
      exact (eq_empty_iff_forall_notMem.1 this) (X n ω) (by simpa using h))
    (ENNReal.ofReal_pos.2 (by positivity)) hev

end Upgrade


section Laws

variable {Z Y Ω : Type*} [PseudoMetricSpace Z] [CompactlyCoherentSpace Z] [MetricSpace Y]
  [MeasurableSpace Ω] [MeasurableSpace C(Z, Y)] [BorelSpace C(Z, Y)]

/-- **Tightness of the laws.**  Under the hypotheses of
`exists_isCompact_measure_le_of_kernelModuli`, with all `X i` measurable, the set of laws
`(μ i).map (X i)` is tight in `C(Z, Y)`. -/
theorem isTightMeasureSet_map_of_kernelModuli {ι : Type*}
    (μ : ι → Measure Ω) (X : ι → Ω → C(Z, Y)) (hX : ∀ i, Measurable (X i)) (z₀ : Z)
    (hmod : ∀ L : ℝ, 1 < L → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, μ i {ω | X i ω ∈ kernelModulusFailure z₀ L δ} ≤ ENNReal.ofReal (1 / L))
    (hpt : ∀ ζ : ℝ, 0 < ζ → ∃ K : Z → Set Y, (∀ z, IsCompact (K z)) ∧
      ∀ i, μ i {ω | ∃ z, X i ω z ∉ K z} ≤ ENNReal.ofReal ζ) :
    IsTightMeasureSet {ν : Measure C(Z, Y) | ∃ i, ν = (μ i).map (X i)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ζ, hζ0, hζε⟩ : ∃ ζ : ℝ, 0 < ζ ∧ ENNReal.ofReal ζ ≤ ε := by
    by_cases hεt : ε = ⊤
    · exact ⟨1, one_pos, by simp [hεt]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεt, (ENNReal.ofReal_toReal hεt).le⟩
  obtain ⟨K, hK, hKμ⟩ := exists_isCompact_measure_le_of_kernelModuli μ X z₀ hmod hpt hζ0
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [Measure.map_apply (hX i) hK.isClosed.measurableSet.compl]
  exact (hKμ i).trans hζε

end Laws

end LatticeProb
