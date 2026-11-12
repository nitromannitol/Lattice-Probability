import LatticeProb.LQG.MatingOfTreesCouplingLaw

/-!
# Pathwise events of a mating-of-trees coupling

Events of the curves of a mating-of-trees coupling that are measurable subsets of the space
`C(ℝ, E)` of continuous curves (compact-open topology, Borel σ-algebra).

* `ContinuousMap.isClosed_setOf_mem_image`: for compact `K ⊆ ℝ`, the pairs `(f, z)` with
  `z ∈ f '' K` form a closed set;
* `ContinuousMap.measurable_measure_image`: `f ↦ μ (f '' K)` is measurable for every s-finite Borel
  measure `μ`;
* `ContinuousMap.measurableSet_setOf_subset_image`: the event `U ⊆ f '' K` is measurable for open
  `U`;
* `ContinuousMap.tendsto_cocompact_iff_forall_rat`: properness of a continuous curve, read on
  rational times;
* `ContinuousMap.surjective_iff_denseRange_rat`: a proper continuous curve is surjective iff its
  values at rational times are dense;
* `ContinuousMap.measurableSet_spaceFilling`: the surjective proper curves rooted at `0` and
  parametrized by Lebesgue measure form a measurable set.

Consequently the space-filling and coverage clauses of a mating-of-trees coupling hold for every
measurable random element of the data space with the law of a coupling
(`IsCouplingData.spaceFilling_of_map_eq`, `IsCouplingData.coverage_of_map_eq`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- A continuous function of a real variable maps an open set into a closed set as soon as it does
so at rational points. -/
theorem Continuous.mem_of_forall_rat {Y : Type*} [TopologicalSpace Y] {g : ℝ → Y}
    (hg : Continuous g) {U : Set ℝ} (hU : IsOpen U) {C : Set Y} (hC : IsClosed C)
    (h : ∀ q : ℚ, (q : ℝ) ∈ U → g q ∈ C) : ∀ x ∈ U, g x ∈ C := by
  intro x hx
  have h1 : x ∈ closure (U ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter hU hx
  refine closure_minimal (t := g ⁻¹' C) ?_ (hC.preimage hg) h1
  rintro _ ⟨hu, q, rfl⟩
  exact h q hu

/-- An interval function that is monotone under inclusion, vanishes on degenerate intervals and
equals the length on intervals with rational endpoints equals the length on every interval. -/
theorem ENNReal.eq_ofReal_sub_of_forall_rat {F : ℝ → ℝ → ℝ≥0∞}
    (hmono : ∀ s t s' t' : ℝ, s ≤ s' → t' ≤ t → F s' t' ≤ F s t) (hdiag : ∀ s, F s s = 0)
    (h : ∀ q r : ℚ, (q : ℝ) ≤ r → F q r = ENNReal.ofReal ((r : ℝ) - q)) :
    ∀ s t : ℝ, s ≤ t → F s t = ENNReal.ofReal (t - s) := by
  intro s t hst
  rcases hst.eq_or_lt with rfl | hlt
  · rw [hdiag, sub_self, ENNReal.ofReal_zero]
  refine le_antisymm ?_ ?_
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s - ε / 2 < s by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t < t + ε / 2 by linarith)
    calc F s t ≤ F q r := hmono q r s t hq2.le hr1.le
      _ = ENNReal.ofReal ((r : ℝ) - q) := h q r (by linarith)
      _ ≤ ENNReal.ofReal (t - s + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (t - s) + ε := by
        rw [ENNReal.ofReal_add (by linarith) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
    obtain ⟨δ, hδpos, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ε : ℝ) / 2 ∧ δ ≤ (t - s) / 2 :=
      ⟨min ((ε : ℝ) / 2) ((t - s) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + δ by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t - δ < t by linarith)
    calc ENNReal.ofReal (t - s) ≤ ENNReal.ofReal (((r : ℝ) - q) + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal ((r : ℝ) - q) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = F q r + ε := by rw [h q r (by linarith), ENNReal.ofReal_coe_nnreal]
      _ ≤ F s t + ε := by
        gcongr
        exact hmono s t q r hq1.le hr2.le

namespace ContinuousMap

section Image

variable {E : Type*} [TopologicalSpace E]

/-- For compact `K ⊆ ℝ`, the pairs `(f, z)` of a continuous curve and a point of its image of `K`
form a closed subset of `C(ℝ, E) × E`. -/
theorem isClosed_setOf_mem_image [T2Space E] {K : Set ℝ} (hK : IsCompact K) :
    IsClosed {p : C(ℝ, E) × E | p.2 ∈ p.1 '' K} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcl : IsClosed {q : (C(ℝ, E) × E) × K | q.1.1 q.2 = q.1.2} :=
    isClosed_eq (ContinuousEval.continuous_eval.comp
      (continuous_fst.fst.prodMk (continuous_subtype_val.comp continuous_snd))) continuous_fst.snd
  convert isClosedMap_fst_of_compactSpace _ hcl using 1
  ext ⟨f, z⟩
  constructor
  · rintro ⟨u, hu, hfu⟩
    exact ⟨((f, z), ⟨u, hu⟩), hfu, rfl⟩
  · rintro ⟨⟨⟨g, w⟩, u⟩, hx, hxeq⟩
    simp only [Prod.mk.injEq] at hxeq
    obtain ⟨rfl, rfl⟩ := hxeq
    exact ⟨u, u.2, hx⟩

/-- For compact `K ⊆ ℝ` and an s-finite Borel measure `μ`, the measure `μ (f '' K)` of the image
of `K` is a measurable function of the curve `f`. -/
theorem measurable_measure_image [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SFinite μ] {K : Set ℝ} (hK : IsCompact K) :
    Measurable fun f : C(ℝ, E) => μ (f '' K) := by
  have : PolishSpace C(ℝ, E) := LQGMetric.polishSpace_continuousMap ℝ E
  exact measurable_measure_prodMk_left (isClosed_setOf_mem_image hK).measurableSet

/-- For open `U` and compact `K ⊆ ℝ`, the event that the image of `K` covers `U` is measurable. -/
theorem measurableSet_setOf_subset_image [T2Space E] [TopologicalSpace.SeparableSpace E]
    {U : Set E} (hU : IsOpen U) {K : Set ℝ} (hK : IsCompact K) :
    MeasurableSet {f : C(ℝ, E) | U ⊆ f '' K} := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense E
  have hset : {f : C(ℝ, E) | U ⊆ f '' K} = ⋂ z ∈ U ∩ D, {f : C(ℝ, E) | z ∈ f '' K} := by
    ext f
    simp only [mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h z hz
      exact h hz.1
    · intro h
      exact (hD.open_subset_closure_inter hU).trans
        (closure_minimal (fun z hz => h z hz) (hK.image f.continuous).isClosed)
  rw [hset]
  refine MeasurableSet.biInter (hDc.mono inter_subset_right) fun z _ => ?_
  exact ((isClosed_setOf_mem_image hK).preimage
    (continuous_id.prodMk continuous_const)).measurableSet

/-- The event that the values of a curve at rational times are dense is measurable. -/
theorem measurableSet_setOf_denseRange_rat [SecondCountableTopology E] :
    MeasurableSet {f : C(ℝ, E) | DenseRange fun q : ℚ => f q} := by
  have hb := TopologicalSpace.isBasis_countableBasis E
  have hset : {f : C(ℝ, E) | DenseRange fun q : ℚ => f q} =
      ⋂ o ∈ TopologicalSpace.countableBasis E,
        {f : C(ℝ, E) | o.Nonempty → ∃ q : ℚ, f q ∈ o} := by
    ext f
    simp only [mem_iInter, Set.mem_ofPred_eq]
    rw [DenseRange, hb.dense_iff]
    refine forall₂_congr fun o _ => imp_congr_right fun _ => ?_
    constructor
    · rintro ⟨_, hz, q, rfl⟩
      exact ⟨q, hz⟩
    · rintro ⟨q, hq⟩
      exact ⟨_, hq, q, rfl⟩
  rw [hset]
  refine MeasurableSet.biInter (TopologicalSpace.countable_countableBasis E) fun o ho => ?_
  by_cases hne : o.Nonempty
  · have : {f : C(ℝ, E) | o.Nonempty → ∃ q : ℚ, f q ∈ o} = ⋃ q : ℚ, {f : C(ℝ, E) | f q ∈ o} := by
      ext f
      simp [hne]
    rw [this]
    exact MeasurableSet.iUnion fun q => ((TopologicalSpace.isOpen_of_mem_countableBasis ho).preimage
      (ContinuousEvalConst.continuous_eval_const (q : ℝ))).measurableSet
  · have : {f : C(ℝ, E) | o.Nonempty → ∃ q : ℚ, f q ∈ o} = univ := by
      ext f
      simp [hne]
    rw [this]
    exact MeasurableSet.univ

end Image

section Proper

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A continuous curve `f : ℝ → E` is proper iff for every `n` there is `m` such that `‖f q‖ ≥ n`
at every rational time `q` with `|q| > m`. -/
theorem tendsto_cocompact_iff_forall_rat (f : C(ℝ, E)) :
    Tendsto f (cocompact ℝ) (cocompact E) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, (m : ℝ) < |(q : ℝ)| → (n : ℝ) ≤ ‖f q‖ := by
  rw [← Metric.cobounded_eq_cocompact (α := ℝ), ← Metric.cobounded_eq_cocompact (α := E),
    ← tendsto_norm_atTop_iff_cobounded, ← comap_norm_atTop,
    (atTop_basis.comap _).tendsto_iff atTop_basis]
  constructor
  · intro h n
    obtain ⟨m, -, hm⟩ := h n trivial
    obtain ⟨k, hk⟩ := exists_nat_ge m
    refine ⟨k, fun q hq => hm q ?_⟩
    simp only [mem_preimage, mem_Ici, Real.norm_eq_abs]
    linarith
  · intro h b _
    obtain ⟨n, hn⟩ := exists_nat_ge b
    obtain ⟨m, hm⟩ := h n
    refine ⟨m + 1, trivial, fun x hx => ?_⟩
    simp only [mem_preimage, mem_Ici, Real.norm_eq_abs] at hx ⊢
    have key := f.continuous.mem_of_forall_rat (isOpen_lt continuous_const continuous_abs)
      (isClosed_le continuous_const continuous_norm) (fun q hq => hm q hq)
    exact hn.trans (key x (by simp only [Set.mem_ofPred_eq]; linarith))

/-- A proper continuous curve is surjective iff its values at rational times are dense. -/
theorem surjective_iff_denseRange_rat (f : C(ℝ, E)) (hf : Tendsto f (cocompact ℝ) (cocompact E)) :
    Function.Surjective f ↔ DenseRange fun q : ℚ => f q := by
  constructor
  · intro hs
    exact hs.denseRange.comp Rat.denseRange_cast f.continuous
  · intro hd
    have hcl : IsClosed (range f) :=
      (isProperMap_iff_tendsto_cocompact.2 ⟨f.continuous, hf⟩).isClosed_range
    have hd' : Dense (range f) := hd.mono (by rintro _ ⟨q, rfl⟩; exact ⟨q, rfl⟩)
    have : range f = univ := by rw [← hcl.closure_eq]; exact hd'.closure_eq
    exact range_eq_univ.1 this

end Proper

/-- The space-filling property of a curve, read on rational times: surjective, proper, rooted at
`0` and parametrized by Lebesgue measure. -/
theorem spaceFilling_iff_rat (f : C(ℝ, ℂ)) :
    (Function.Surjective f ∧ Tendsto f (cocompact ℝ) (cocompact ℂ) ∧ f 0 = 0 ∧
      ∀ s t : ℝ, s ≤ t → volume (f '' Icc s t) = ENNReal.ofReal (t - s)) ↔
    (DenseRange (fun q : ℚ => f q) ∧
      (∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, (m : ℝ) < |(q : ℝ)| → (n : ℝ) ≤ ‖f q‖) ∧ f 0 = 0 ∧
      ∀ q r : ℚ, (q : ℝ) ≤ r → volume (f '' Icc (q : ℝ) r) = ENNReal.ofReal ((r : ℝ) - q)) := by
  constructor
  · rintro ⟨hs, ht, h0, hv⟩
    exact ⟨(surjective_iff_denseRange_rat f ht).1 hs, (tendsto_cocompact_iff_forall_rat f).1 ht,
      h0, fun q r hqr => hv q r hqr⟩
  · rintro ⟨hd, ht, h0, hv⟩
    have ht' := (tendsto_cocompact_iff_forall_rat f).2 ht
    refine ⟨(surjective_iff_denseRange_rat f ht').2 hd, ht', h0, ?_⟩
    exact ENNReal.eq_ofReal_sub_of_forall_rat (F := fun s t => volume (f '' Icc s t))
      (fun s t s' t' hs ht => measure_mono (image_mono (Icc_subset_Icc hs ht)))
      (fun s => by simp) hv

/-- The surjective proper curves rooted at `0` and parametrized by Lebesgue measure form a
measurable subset of `C(ℝ, ℂ)`. -/
theorem measurableSet_spaceFilling :
    MeasurableSet {f : C(ℝ, ℂ) | Function.Surjective f ∧ Tendsto f (cocompact ℝ) (cocompact ℂ) ∧
      f 0 = 0 ∧ ∀ s t : ℝ, s ≤ t → volume (f '' Icc s t) = ENNReal.ofReal (t - s)} := by
  have hset : {f : C(ℝ, ℂ) | Function.Surjective f ∧ Tendsto f (cocompact ℝ) (cocompact ℂ) ∧
      f 0 = 0 ∧ ∀ s t : ℝ, s ≤ t → volume (f '' Icc s t) = ENNReal.ofReal (t - s)} =
      {f : C(ℝ, ℂ) | DenseRange (fun q : ℚ => f q) ∧
        (∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, (m : ℝ) < |(q : ℝ)| → (n : ℝ) ≤ ‖f q‖) ∧ f 0 = 0 ∧
        ∀ q r : ℚ, (q : ℝ) ≤ r → volume (f '' Icc (q : ℝ) r) = ENNReal.ofReal ((r : ℝ) - q)} := by
    ext f
    exact spaceFilling_iff_rat f
  rw [hset]
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
  · exact measurableSet_setOfPred.1 measurableSet_setOf_denseRange_rat
  · refine Measurable.forall fun n => Measurable.exists fun m => Measurable.forall fun q =>
      Measurable.imp measurable_const ?_
    exact measurableSet_setOfPred.1
      (isClosed_le continuous_const (ContinuousEvalConst.continuous_eval_const (q : ℝ)).norm).measurableSet
  · exact measurableSet_setOfPred.1
      (isClosed_eq (ContinuousEvalConst.continuous_eval_const 0) continuous_const).measurableSet
  · refine Measurable.forall fun q => Measurable.forall fun r => Measurable.imp measurable_const ?_
    exact measurableSet_setOfPred.1
      (measurable_measure_image volume isCompact_Icc (measurableSet_singleton _))

end ContinuousMap

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

section Pathwise

variable (hC : IsCouplingData γ P V) (hV : Measurable V) (hV' : Measurable V')
  (hlaw : P'.map V' = P.map V)
include hC hV hV' hlaw

/-- The space-filling clause (surjective, proper, rooted at `0`, parametrized by Lebesgue measure)
holds for a measurable random element of the data space with the law of a coupling. -/
theorem IsCouplingData.spaceFilling_of_map_eq :
    ∀ᵐ ω ∂P', Function.Surjective (V' ω).ηL ∧
      Tendsto (V' ω).ηL (cocompact ℝ) (cocompact ℂ) ∧ (V' ω).ηL 0 = 0 ∧
      ∀ s t : ℝ, s ≤ t → volume ((V' ω).ηL '' Icc s t) = ENNReal.ofReal (t - s) :=
  ae_comp_of_map_eq hV hV' hlaw (measurable_ηL ContinuousMap.measurableSet_spaceFilling)
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).spaceFilling

/-- The coverage clause for the curve of the γ-quantum cone holds for a measurable random element
of the data space with the law of a coupling, with the same constants. -/
theorem IsCouplingData.coverage_of_map_eq :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ M : ℝ, 1 < M →
      P' {ω | ¬ Metric.ball (0 : ℂ) 1 ⊆ (V' ω).η '' Icc (-M) M} ≤
        ENNReal.ofReal (C * M ^ (-c)) := by
  obtain ⟨c, hc, C, hcov⟩ :=
    (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC).coverage
  refine ⟨c, hc, C, fun M hM => le_trans ?_ (hcov M hM)⟩
  have hS : MeasurableSet {v : CouplingData | ¬ Metric.ball (0 : ℂ) 1 ⊆ v.η '' Icc (-M) M} :=
    (measurable_η (ContinuousMap.measurableSet_setOf_subset_image Metric.isOpen_ball
      isCompact_Icc)).compl
  exact measure_preimage_le_of_map_eq hV hV' hlaw hS.nullMeasurableSet

end Pathwise

end MatedCRT

end MatedCRTHarmonic

end
