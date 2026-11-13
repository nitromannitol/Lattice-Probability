import LatticeProb.LQG.MatingOfTreesCouplingCells

/-!
# Degree functionals of a mating-of-trees coupling

The inner and outer degrees of a curve are suprema of natural numbers `N` over families of `N`
parameter intervals satisfying conditions on the curve. Such a supremum is the countable supremum
over `N` of the indicator of the projection of the set of admissible pairs (curve, parameters);
when that set is analytic, the degree is almost everywhere measurable for every finite Borel
measure, and its moments depend only on the law of the curve.

* `MeasureTheory.aemeasurable_toENNReal_of_eq_iSup_natCast`: the general measurability criterion;
* `ContinuousMap.isClosed_setOf_image_subset_closedBall`;
* `ContinuousMap.isOpen_setOf_image_subset_ball`, `measurableSet_setOf_image_Ioo_subset_ball`,
  `segmentReparam_image_Ioo`;
* `degInnerCond`, `analyticSet_setOf_degInnerCond`, `aemeasurable_degInner`; `degOuterCond`,
  `degOuterCond_iff`, `analyticSet_setOf_degOuterCond`, `aemeasurable_degOuter`;
* `lintegral_degInner_rpow_of_map_eq`, `lintegral_degOuter_rpow_of_map_eq`: the moments of the
  degrees depend only on the law of the curve;
* `IsCouplingData.degInner_moments_of_map_eq`, `IsCouplingData.degOuter_moments_of_map_eq`,
  `IsCouplingData.cellMoments_of_map_eq`: the second and third (hence all) cell-moment clauses of a
  mating-of-trees coupling hold for every measurable random element of the data space with the law
  of a coupling.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace MeasureTheory

/-- Let `f x` be the supremum of the natural numbers `N` for which some parameter `a : A N`
satisfies a condition `p N x a`. If each set `{(x, a) | p N x a}` is analytic, then `f`, viewed as
an extended nonnegative real, is almost everywhere measurable for every finite measure. -/
theorem aemeasurable_toENNReal_of_eq_iSup_natCast {X : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {A : ℕ → Type*} [∀ N, TopologicalSpace (A N)] {p : ∀ N, X → A N → Prop} {f : X → ℕ∞}
    (hf : ∀ x, f x = ⨆ (N : ℕ) (a : A N) (_ : p N x a), (N : ℕ∞))
    (hp : ∀ N, AnalyticSet {q : X × A N | p N q.1 q.2}) (μ : Measure X) [IsFiniteMeasure μ] :
    AEMeasurable (fun x => (f x : ℝ≥0∞)) μ := by
  have hfun : (fun x => (f x : ℝ≥0∞)) =
      fun x => ⨆ N : ℕ, {x | ∃ a, p N x a}.indicator (fun _ => (N : ℝ≥0∞)) x := by
    funext x
    rw [hf x, ENat.toENNReal_iSup]
    refine iSup_congr fun N => ?_
    by_cases h : ∃ a, p N x a
    · have hN : (⨆ (a : A N) (_ : p N x a), (N : ℕ∞)) = N := by
        obtain ⟨a, ha⟩ := h
        exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le a ha le_rfl)
      rw [hN]
      simp [h]
    · have hN : (⨆ (a : A N) (_ : p N x a), (N : ℕ∞)) = 0 :=
        le_antisymm (iSup₂_le fun a ha => (h ⟨a, ha⟩).elim) zero_le
      rw [hN]
      simp [h]
  rw [hfun]
  refine AEMeasurable.iSup fun N => aemeasurable_const.indicator₀ ?_
  have hset : {x | ∃ a, p N x a} = Prod.fst '' {q : X × A N | p N q.1 q.2} := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(x, a), ha, rfl⟩
    · rintro ⟨⟨x', a⟩, ha, rfl⟩
      exact ⟨a, ha⟩
  rw [hset]
  exact LatticeProb.AnalyticSet.nullMeasurableSet μ ((hp N).image_of_continuous continuous_fst)

end MeasureTheory

namespace ContinuousMap

/-- The pairs `(f, r)` such that `f` maps `K` into the closed ball of radius `r` about `0` form a
closed set. -/
theorem isClosed_setOf_image_subset_closedBall {E : Type*} [SeminormedAddCommGroup E]
    (K : Set ℝ) : IsClosed {p : C(ℝ, E) × ℝ | p.1 '' K ⊆ closedBall 0 p.2} := by
  have hset : {p : C(ℝ, E) × ℝ | p.1 '' K ⊆ closedBall 0 p.2} =
      ⋂ t ∈ K, {p : C(ℝ, E) × ℝ | ‖p.1 t‖ ≤ p.2} := by
    ext p
    rw [mem_iInter₂]
    constructor
    · intro h t ht
      exact mem_closedBall_zero_iff.1 (h (mem_image_of_mem _ ht))
    · rintro h _ ⟨t, ht, rfl⟩
      exact mem_closedBall_zero_iff.2 (h t ht)
  rw [hset]
  exact isClosed_biInter fun t _ => isClosed_le
    ((ContinuousEvalConst.continuous_eval_const t).comp continuous_fst).norm continuous_snd

/-- For compact `K`, the pairs `(f, r)` such that `f` maps `K` into the open ball of radius `r`
about `0` form an open set. -/
theorem isOpen_setOf_image_subset_ball {E : Type*} [SeminormedAddCommGroup E] {K : Set ℝ}
    (hK : IsCompact K) : IsOpen {p : C(ℝ, E) × ℝ | p.1 '' K ⊆ ball 0 p.2} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  have hP : ∀ t ∈ K, ∀ᶠ z : (C(ℝ, E) × ℝ) × ℝ in 𝓝 (p, t), ‖z.1.1 z.2‖ < z.1.2 := by
    intro t ht
    have hpt : ‖p.1 t‖ < p.2 := mem_ball_zero_iff.1 (hp (mem_image_of_mem _ ht))
    exact (isOpen_lt (ContinuousEval.continuous_eval.comp
      (continuous_fst.fst.prodMk continuous_snd)).norm continuous_fst.snd).mem_nhds hpt
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun (q : C(ℝ, E) × ℝ) (t : ℝ) => ‖q.1 t‖ < q.2) hP] with q hq
  rintro _ ⟨t, ht, rfl⟩
  exact mem_ball_zero_iff.2 (hq t ht)

/-- The pairs `(f, r)` such that `f` maps `(0, 1)` into the open ball of radius `r` about `0` form a
Borel set: `(0, 1)` is an increasing union of compact intervals. -/
theorem measurableSet_setOf_image_Ioo_subset_ball {E : Type*} [SeminormedAddCommGroup E] :
    MeasurableSet {p : C(ℝ, E) × ℝ | p.1 '' Ioo 0 1 ⊆ ball 0 p.2} := by
  have hset : {p : C(ℝ, E) × ℝ | p.1 '' Ioo 0 1 ⊆ ball 0 p.2} =
      ⋂ n : ℕ, {p : C(ℝ, E) × ℝ |
        p.1 '' Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)) ⊆ ball 0 p.2} := by
    ext p
    rw [mem_iInter]
    constructor
    · intro h n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have hle : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
      refine (image_mono (show Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)) ⊆ Ioo 0 1 from
        fun s hs => ⟨?_, ?_⟩)).trans h
      · exact lt_of_lt_of_le hpos hs.1
      · linarith [hs.2]
    · rintro h _ ⟨s, hs, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hs.1 (sub_pos.2 hs.2))
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h3 := lt_min_iff.1 hn
      exact h n (mem_image_of_mem _ ⟨by linarith [h3.1], by linarith [h3.2]⟩)
  rw [hset]
  exact MeasurableSet.iInter fun n => (isOpen_setOf_image_subset_ball isCompact_Icc).measurableSet

/-- For `a < b`, the reparametrized curve maps `(0, 1)` onto the image of `(a, b)`. -/
theorem segmentReparam_image_Ioo {E : Type*} [TopologicalSpace E] (f : C(ℝ, E)) {a b : ℝ}
    (hab : a < b) : segmentReparam (f, a, b) '' Ioo 0 1 = f '' Ioo a b := by
  have h1 : (fun s : ℝ => s * (b - a)) '' Ioo 0 1 = Ioo 0 (b - a) := by
    rw [Set.image_mul_right_Ioo _ _ (sub_pos.2 hab)]
    simp
  have h : (fun s : ℝ => a + s * (b - a)) '' Ioo 0 1 = Ioo a b := by
    rw [show (fun s : ℝ => a + s * (b - a)) = (fun x => a + x) ∘ (fun s => s * (b - a)) from rfl,
      Set.image_comp, h1, Set.image_const_add_Ioo]
    simp
  rw [← h, Set.image_image]
  rfl

end ContinuousMap

namespace MatedCRTHarmonic

namespace MatedCRT

open ContinuousMap

/-- The condition in the definition of `degInner`: the parameter intervals `[a i, a i + 1]` have
disjoint interiors, and their images lie in `degBall c` and meet `c([-1, 1])`. -/
def degInnerCond (N : ℕ) (c : C(ℝ, ℂ)) (a : Fin N → ℝ) : Prop :=
  (∀ i j, i ≠ j → Disjoint (Ioo (a i) (a i + 1)) (Ioo (a j) (a j + 1))) ∧
    ∀ i, c '' Icc (a i) (a i + 1) ⊆ degBall c ∧ (c '' Icc (a i) (a i + 1) ∩ c '' Icc (-1) 1).Nonempty

theorem degInner_eq_iSup_degInnerCond (c : C(ℝ, ℂ)) :
    degInner c = ⨆ (N : ℕ) (a : Fin N → ℝ) (_ : degInnerCond N c a), (N : ℕ∞) := rfl

/-- The admissible pairs (curve, parameters) of `degInner` form an analytic set: they are the
projection of a Borel set in which a point of each image `c([a i, a i + 1])` lying on `c([-1, 1])`
is recorded by its parameter. -/
theorem analyticSet_setOf_degInnerCond (N : ℕ) :
    AnalyticSet {q : C(ℝ, ℂ) × (Fin N → ℝ) | degInnerCond N q.1 q.2} := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  let S : Set (C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ)) :=
    {q | (∀ i j, i ≠ j → Disjoint (Ioo (q.2.1 i) (q.2.1 i + 1)) (Ioo (q.2.1 j) (q.2.1 j + 1))) ∧
      ∀ i, q.1 '' Icc (q.2.1 i) (q.2.1 i + 1) ⊆ degBall q.1 ∧
        q.2.2 i ∈ Icc (q.2.1 i) (q.2.1 i + 1) ∧ q.1 (q.2.2 i) ∈ q.1 '' Icc (-1) 1}
  have hS : MeasurableSet S := by
    have ha : ∀ i : Fin N, Continuous fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) => q.2.1 i :=
      fun i => (continuous_apply i).comp continuous_snd.fst
    have hs : ∀ i : Fin N, Continuous fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) => q.2.2 i :=
      fun i => (continuous_apply i).comp continuous_snd.snd
    refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
    · refine Measurable.forall fun i => Measurable.forall fun j =>
        Measurable.imp measurable_const ?_
      have heq : (fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) =>
          Disjoint (Ioo (q.2.1 i) (q.2.1 i + 1)) (Ioo (q.2.1 j) (q.2.1 j + 1))) =
          fun q => min (q.2.1 i + 1) (q.2.1 j + 1) ≤ max (q.2.1 i) (q.2.1 j) := by
        funext q
        exact propext Set.Ioo_disjoint_Ioo
      rw [heq]
      exact measurableSet_setOfPred.1 (measurableSet_le
        (((ha i).add continuous_const).min ((ha j).add continuous_const)).measurable
        ((ha i).max (ha j)).measurable)
    · refine Measurable.forall fun i => Measurable.and ?_ (Measurable.and ?_ ?_)
      · have hG : Continuous fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) =>
            segmentReparam (q.1, q.2.1 i, q.2.1 i + 1) :=
          segmentReparam.continuous.comp
            (continuous_fst.prodMk ((ha i).prodMk ((ha i).add continuous_const)))
        have hρ : Measurable fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) =>
            4 * diam (q.1 '' Icc (-1) 1) :=
          measurable_const.mul ((measurable_diam_image (E := ℂ) isCompact_Icc
            (nonempty_Icc.2 (by norm_num))).comp measurable_fst)
        have heq : (fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) =>
            q.1 '' Icc (q.2.1 i) (q.2.1 i + 1) ⊆ degBall q.1) =
            fun q => (segmentReparam (q.1, q.2.1 i, q.2.1 i + 1), 4 * diam (q.1 '' Icc (-1) 1)) ∈
              {p : C(ℝ, ℂ) × ℝ | p.1 '' Icc 0 1 ⊆ closedBall 0 p.2} := by
          funext q
          show _ = (segmentReparam (q.1, q.2.1 i, q.2.1 i + 1) '' Icc 0 1 ⊆
            closedBall 0 (4 * diam (q.1 '' Icc (-1) 1)))
          rw [segmentReparam_image_Icc q.1 (le_add_of_nonneg_right zero_le_one)]
          rfl
        rw [heq]
        exact measurableSet_setOfPred.1
          ((isClosed_setOf_image_subset_closedBall (E := ℂ) (Icc 0 1)).measurableSet.preimage
            (hG.measurable.prodMk hρ))
      · exact Measurable.and
          (measurableSet_setOfPred.1 (measurableSet_le (ha i).measurable (hs i).measurable))
          (measurableSet_setOfPred.1 (measurableSet_le (hs i).measurable
            ((ha i).add continuous_const).measurable))
      · exact measurableSet_setOfPred.1
          ((isClosed_setOf_mem_image (E := ℂ) isCompact_Icc).measurableSet.preimage
            (continuous_fst.prodMk (ContinuousEval.continuous_eval.comp
              (continuous_fst.prodMk (hs i)))).measurable)
  have hset : {q : C(ℝ, ℂ) × (Fin N → ℝ) | degInnerCond N q.1 q.2} =
      (fun q : C(ℝ, ℂ) × (Fin N → ℝ) × (Fin N → ℝ) => (q.1, q.2.1)) '' S := by
    ext ⟨c, a⟩
    constructor
    · rintro ⟨hD, hI⟩
      choose s hs using fun i => image_inter_nonempty_iff.1 (hI i).2
      exact ⟨(c, a, s), ⟨hD, fun i => ⟨(hI i).1, (hs i).1, (hs i).2⟩⟩, rfl⟩
    · rintro ⟨⟨c', a', s⟩, ⟨hD, hI⟩, hq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      exact ⟨hD, fun i => ⟨(hI i).1, image_inter_nonempty_iff.2 ⟨s i, (hI i).2.1, (hI i).2.2⟩⟩⟩
  rw [hset]
  exact hS.analyticSet.image_of_continuous (continuous_fst.prodMk continuous_snd.fst)

/-- The inner degree `degInner` is almost everywhere measurable for every finite Borel measure on
`C(ℝ, ℂ)`. -/
theorem aemeasurable_degInner (μ : Measure C(ℝ, ℂ)) [IsFiniteMeasure μ] :
    AEMeasurable (fun c => (degInner c : ℝ≥0∞)) μ :=
  aemeasurable_toENNReal_of_eq_iSup_natCast (A := fun N => Fin N → ℝ) (p := degInnerCond)
    degInner_eq_iSup_degInnerCond analyticSet_setOf_degInnerCond μ

/-- The condition in the definition of `degOuter`, with the endpoints `ab = (a, b)` of the
parameter intervals collected in one pair: the intervals `(a i, b i)` are nondegenerate with
disjoint interiors, their images lie in the interior of `degBall c`, and one endpoint is mapped to
the boundary of `degBall c` and the other into `c([-1, 1])`. -/
def degOuterCond (N : ℕ) (c : C(ℝ, ℂ)) (ab : (Fin N → ℝ) × (Fin N → ℝ)) : Prop :=
  (∀ i, ab.1 i < ab.2 i) ∧
    (∀ i j, i ≠ j → Disjoint (Ioo (ab.1 i) (ab.2 i)) (Ioo (ab.1 j) (ab.2 j))) ∧
      ∀ i, c '' Ioo (ab.1 i) (ab.2 i) ⊆ interior (degBall c) ∧
        ((c (ab.1 i) ∈ frontier (degBall c) ∧ c (ab.2 i) ∈ c '' Icc (-1) 1) ∨
          (c (ab.2 i) ∈ frontier (degBall c) ∧ c (ab.1 i) ∈ c '' Icc (-1) 1))

theorem degOuter_eq_iSup_degOuterCond (c : C(ℝ, ℂ)) :
    degOuter c = ⨆ (N : ℕ) (ab : (Fin N → ℝ) × (Fin N → ℝ)) (_ : degOuterCond N c ab),
      (N : ℕ∞) := by
  unfold degOuter
  refine iSup_congr fun N => ?_
  rw [iSup_prod]
  rfl

/-- `degOuterCond` in terms of the norm, the radius `4 diam (c([-1, 1]))` and the reparametrized
curves `s ↦ c(a i + s (b i - a i))` on `(0, 1)`. -/
theorem degOuterCond_iff (N : ℕ) (c : C(ℝ, ℂ)) (a b : Fin N → ℝ) :
    degOuterCond N c (a, b) ↔ (∀ i, a i < b i) ∧
      (∀ i j, i ≠ j → min (b i) (b j) ≤ max (a i) (a j)) ∧
      ∀ i, segmentReparam (c, a i, b i) '' Ioo 0 1 ⊆ ball 0 (4 * diam (c '' Icc (-1) 1)) ∧
        ((‖c (a i)‖ = 4 * diam (c '' Icc (-1) 1) ∧ c (b i) ∈ c '' Icc (-1) 1) ∨
          (‖c (b i)‖ = 4 * diam (c '' Icc (-1) 1) ∧ c (a i) ∈ c '' Icc (-1) 1)) := by
  simp only [degOuterCond, degBall, interior_closedBall', frontier_closedBall',
    mem_sphere_zero_iff_norm, Set.Ioo_disjoint_Ioo]
  constructor
  · rintro ⟨hab, hD, hI⟩
    exact ⟨hab, hD, fun i => by rw [segmentReparam_image_Ioo c (hab i)]; exact hI i⟩
  · rintro ⟨hab, hD, hI⟩
    exact ⟨hab, hD, fun i => by rw [← segmentReparam_image_Ioo c (hab i)]; exact hI i⟩

/-- The admissible pairs (curve, endpoints) of `degOuter` form a Borel, hence analytic, set. -/
theorem analyticSet_setOf_degOuterCond (N : ℕ) :
    AnalyticSet {q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) | degOuterCond N q.1 q.2} := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  have ha : ∀ i : Fin N, Continuous fun q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) => q.2.1 i :=
    fun i => (continuous_apply i).comp continuous_snd.fst
  have hb : ∀ i : Fin N, Continuous fun q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) => q.2.2 i :=
    fun i => (continuous_apply i).comp continuous_snd.snd
  have hρ : Measurable fun q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      4 * diam (q.1 '' Icc (-1) 1) :=
    measurable_const.mul ((measurable_diam_image (E := ℂ) isCompact_Icc
      (nonempty_Icc.2 (by norm_num))).comp measurable_fst)
  have hev : ∀ u : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ, Continuous u →
      Continuous fun q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) => q.1 (u q) :=
    fun u hu => ContinuousEval.continuous_eval.comp (continuous_fst.prodMk hu)
  have hmem : ∀ u : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ, Continuous u →
      Measurable fun q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
        q.1 (u q) ∈ q.1 '' Icc (-1) 1 :=
    fun u hu => measurableSet_setOfPred.1
      ((isClosed_setOf_mem_image (E := ℂ) isCompact_Icc).measurableSet.preimage
        (continuous_fst.prodMk (hev u hu)).measurable)
  have hsph : ∀ u : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ, Continuous u →
      Measurable fun q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
        ‖q.1 (u q)‖ = 4 * diam (q.1 '' Icc (-1) 1) :=
    fun u hu => measurableSet_setOfPred.1 (measurableSet_eq_fun (hev u hu).norm.measurable hρ)
  have hset : {q : C(ℝ, ℂ) × ((Fin N → ℝ) × (Fin N → ℝ)) | degOuterCond N q.1 q.2} =
      {q | (∀ i, q.2.1 i < q.2.2 i) ∧
        (∀ i j, i ≠ j → min (q.2.2 i) (q.2.2 j) ≤ max (q.2.1 i) (q.2.1 j)) ∧
        ∀ i, (segmentReparam (q.1, q.2.1 i, q.2.2 i), 4 * diam (q.1 '' Icc (-1) 1)) ∈
            {p : C(ℝ, ℂ) × ℝ | p.1 '' Ioo 0 1 ⊆ ball 0 p.2} ∧
          ((‖q.1 (q.2.1 i)‖ = 4 * diam (q.1 '' Icc (-1) 1) ∧ q.1 (q.2.2 i) ∈ q.1 '' Icc (-1) 1) ∨
            (‖q.1 (q.2.2 i)‖ = 4 * diam (q.1 '' Icc (-1) 1) ∧
              q.1 (q.2.1 i) ∈ q.1 '' Icc (-1) 1))} := by
    ext ⟨c, a, b⟩
    exact degOuterCond_iff N c a b
  rw [hset]
  refine MeasurableSet.analyticSet
    (measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ ?_)))
  · exact Measurable.forall fun i =>
      measurableSet_setOfPred.1 (measurableSet_lt (ha i).measurable (hb i).measurable)
  · exact Measurable.forall fun i => Measurable.forall fun j => Measurable.imp measurable_const
      (measurableSet_setOfPred.1
        (measurableSet_le ((hb i).min (hb j)).measurable ((ha i).max (ha j)).measurable))
  · refine Measurable.forall fun i => Measurable.and ?_ (Measurable.or ?_ ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_setOf_image_Ioo_subset_ball.preimage
        ((segmentReparam.continuous.comp
          (continuous_fst.prodMk ((ha i).prodMk (hb i)))).measurable.prodMk hρ))
    · exact (hsph _ (ha i)).and (hmem _ (hb i))
    · exact (hsph _ (hb i)).and (hmem _ (ha i))

/-- The outer degree `degOuter` is almost everywhere measurable for every finite Borel measure on
`C(ℝ, ℂ)`. -/
theorem aemeasurable_degOuter (μ : Measure C(ℝ, ℂ)) [IsFiniteMeasure μ] :
    AEMeasurable (fun c => (degOuter c : ℝ≥0∞)) μ :=
  aemeasurable_toENNReal_of_eq_iSup_natCast (A := fun N => (Fin N → ℝ) × (Fin N → ℝ))
    (p := degOuterCond) degOuter_eq_iSup_degOuterCond analyticSet_setOf_degOuterCond μ

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- The moments of the inner degree of the curve `η₀` agree for two measurable random elements of
the data space with the same law under a finite measure. -/
theorem lintegral_degInner_rpow_of_map_eq [IsFiniteMeasure P] (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) (p : ℝ) :
    ∫⁻ ω, ((degInner (V' ω).η₀ : ℝ≥0∞)) ^ p ∂P' = ∫⁻ ω, ((degInner (V ω).η₀ : ℝ≥0∞)) ^ p ∂P := by
  have hlaw₀ : P'.map (fun ω => (V' ω).η₀) = P.map (fun ω => (V ω).η₀) :=
    map_comp_of_map_eq hV hV' hlaw measurable_η₀
  exact lintegral_comp_of_map_eq (F := fun c => (degInner c : ℝ≥0∞) ^ p) (measurable_η₀.comp hV)
    (measurable_η₀.comp hV') hlaw₀ ((aemeasurable_degInner _).pow_const p)

/-- The second cell-moment clause (finite moments of order `p ∈ [1, 4/γ²)` of the inner degree of
`η₀`) holds for a measurable random element of the data space with the law of a coupling. -/
theorem IsCouplingData.degInner_moments_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∫⁻ ω, ((degInner (V' ω).η₀ : ℝ≥0∞)) ^ p ∂P' < ⊤ := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  intro p hp hpγ
  rw [lintegral_degInner_rpow_of_map_eq hV hV' hlaw p]
  exact hCP.cellMoments.2.1 p hp hpγ

/-- The moments of the outer degree of the curve `η₀` agree for two measurable random elements of
the data space with the same law under a finite measure. -/
theorem lintegral_degOuter_rpow_of_map_eq [IsFiniteMeasure P] (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V) (p : ℝ) :
    ∫⁻ ω, ((degOuter (V' ω).η₀ : ℝ≥0∞)) ^ p ∂P' = ∫⁻ ω, ((degOuter (V ω).η₀ : ℝ≥0∞)) ^ p ∂P := by
  have hlaw₀ : P'.map (fun ω => (V' ω).η₀) = P.map (fun ω => (V ω).η₀) :=
    map_comp_of_map_eq hV hV' hlaw measurable_η₀
  exact lintegral_comp_of_map_eq (F := fun c => (degOuter c : ℝ≥0∞) ^ p) (measurable_η₀.comp hV)
    (measurable_η₀.comp hV') hlaw₀ ((aemeasurable_degOuter _).pow_const p)

/-- The third cell-moment clause (finite moments of order `p ≥ 1` of the outer degree of `η₀`)
holds for a measurable random element of the data space with the law of a coupling. -/
theorem IsCouplingData.degOuter_moments_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ((degOuter (V' ω).η₀ : ℝ≥0∞)) ^ p ∂P' < ⊤ := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  intro p hp
  rw [lintegral_degOuter_rpow_of_map_eq hV hV' hlaw p]
  exact hCP.cellMoments.2.2 p hp

/-- The full cell-moment clause of a mating-of-trees coupling holds for a measurable random element
of the data space with the law of a coupling. -/
theorem IsCouplingData.cellMoments_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, diamAreaSup (V' ω).η₀ ^ p ∂P' < ⊤) ∧
      (∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∫⁻ ω, ((degInner (V' ω).η₀ : ℝ≥0∞)) ^ p ∂P' < ⊤) ∧
      (∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ((degOuter (V' ω).η₀ : ℝ≥0∞)) ^ p ∂P' < ⊤) :=
  ⟨hC.diamAreaSup_moments_of_map_eq hV hV' hlaw, hC.degInner_moments_of_map_eq hV hV' hlaw,
    hC.degOuter_moments_of_map_eq hV hV' hlaw⟩

end MatedCRT

end MatedCRTHarmonic

end
