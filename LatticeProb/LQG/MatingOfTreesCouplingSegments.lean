import LatticeProb.LQG.MatingOfTreesCouplingPathwise
import LatticeProb.LQG.MatingOfTreesCouplingVisits

/-!
# Segments of a continuous curve that contain balls

For a continuous curve `c : ℝ → ℂ`, the event `E_ε(R, r)` of Gwynne-Holden-Miller (every segment
`c([a, b]) ⊆ B_R(0)` of diameter at least `δ ^ (1 - r)`, `δ ∈ (0, ε]`, contains a ball of radius
`δ`) quantifies over uncountably many `δ, a, b`. Its complement is the projection of a Borel subset
of `C(ℝ, ℂ) × ℝ³`: after the affine reparametrization of `[a, b]` by `[0, 1]`, the condition that the
segment stays in the ball is open, the diameter condition is closed, and "contains a closed ball"
is a countable union of closed conditions (projection along a compact ball of centres). So the
complement is analytic, and the event is null-measurable for every finite Borel measure.

* `ContinuousMap.segmentReparam`: `(f, a, b) ↦ (s ↦ f (a + s (b - a)))`, continuous;
* `ContinuousMap.isClosed_setOf_le_diam_image`: for compact nonempty `K`, `{(f, c) | c ≤ diam (f '' K)}`
  is closed;
* `ContinuousMap.measurableSet_setOf_exists_closedBall_subset_image`;
* `analyticSet_setOf_not_segmentsContainBalls`,
  `nullMeasurableSet_setOf_not_segmentsContainBalls`;
* `IsCouplingData.segmentsContainBalls_of_map_eq`: the segment-ball clause of a mating-of-trees
  coupling holds, with the same constants, for every measurable random element of the data space
  with the law of a coupling.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace ContinuousMap

section Segment

variable {E : Type*} [TopologicalSpace E]

/-- The affine reparametrization `s ↦ f (a + s (b - a))` of a curve `f` on the segment `[a, b]`, as
a continuous function of `(f, a, b)`. -/
def segmentReparam : C(C(ℝ, E) × ℝ × ℝ, C(ℝ, E)) :=
  ContinuousMap.curry ⟨fun q : (C(ℝ, E) × ℝ × ℝ) × ℝ =>
    q.1.1 (q.1.2.1 + q.2 * (q.1.2.2 - q.1.2.1)),
    ContinuousEval.continuous_eval.comp (continuous_fst.fst.prodMk
      (continuous_fst.snd.fst.add
        (continuous_snd.mul (continuous_fst.snd.snd.sub continuous_fst.snd.fst))))⟩

theorem segmentReparam_apply (f : C(ℝ, E)) (a b s : ℝ) :
    segmentReparam (f, a, b) s = f (a + s * (b - a)) := rfl

/-- For `a ≤ b`, the reparametrized curve maps `[0, 1]` onto the image of `[a, b]`. -/
theorem segmentReparam_image_Icc (f : C(ℝ, E)) {a b : ℝ} (hab : a ≤ b) :
    segmentReparam (f, a, b) '' Icc 0 1 = f '' Icc a b := by
  have h1 : (fun s : ℝ => s * (b - a)) '' Icc 0 1 = Icc 0 (b - a) := by
    rw [Set.image_mul_right_Icc zero_le_one (sub_nonneg.2 hab)]
    simp
  have h : (fun s : ℝ => a + s * (b - a)) '' Icc 0 1 = Icc a b := by
    rw [show (fun s : ℝ => a + s * (b - a)) = (fun x => a + x) ∘ (fun s => s * (b - a)) from rfl,
      Set.image_comp, h1, Set.image_const_add_Icc]
    simp
  rw [← h, Set.image_image]
  rfl

end Segment

section Diam

variable {E : Type*} [PseudoMetricSpace E]

/-- For compact nonempty `K`, `c ≤ diam (f '' K)` iff two values of `f` on `K` are at distance at
least `c`. -/
theorem le_diam_image_iff {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) (f : C(ℝ, E))
    (c : ℝ) : c ≤ diam (f '' K) ↔ ∃ s ∈ K, ∃ t ∈ K, c ≤ dist (f s) (f t) := by
  constructor
  · intro hc
    obtain ⟨p, hp, hmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne)
      ((f.continuous.comp continuous_fst).dist (f.continuous.comp continuous_snd)).continuousOn
    refine ⟨p.1, hp.1, p.2, hp.2, hc.trans ?_⟩
    refine diam_le_of_forall_dist_le dist_nonneg ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact isMaxOn_iff.mp hmax (s, t) ⟨hs, ht⟩
  · rintro ⟨s, hs, t, ht, hst⟩
    exact hst.trans (dist_le_diam_of_mem (hK.image f.continuous).isBounded
      (mem_image_of_mem f hs) (mem_image_of_mem f ht))

/-- For compact nonempty `K ⊆ ℝ`, the pairs `(f, c)` with `c ≤ diam (f '' K)` form a closed set. -/
theorem isClosed_setOf_le_diam_image {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) :
    IsClosed {p : C(ℝ, E) × ℝ | p.2 ≤ diam (p.1 '' K)} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hev : ∀ g : (C(ℝ, E) × ℝ) × (K × K) → K, Continuous g →
      Continuous fun q : (C(ℝ, E) × ℝ) × (K × K) => q.1.1 (g q) := fun g hg =>
    ContinuousEval.continuous_eval.comp
      (continuous_fst.fst.prodMk (continuous_subtype_val.comp hg))
  have hcl : IsClosed {q : (C(ℝ, E) × ℝ) × (K × K) |
      q.1.2 ≤ dist (q.1.1 q.2.1) (q.1.1 q.2.2)} :=
    isClosed_le continuous_fst.snd ((hev _ continuous_snd.fst).dist (hev _ continuous_snd.snd))
  convert isClosedMap_fst_of_compactSpace _ hcl using 1
  ext ⟨f, c⟩
  show c ≤ diam (f '' K) ↔ _
  rw [le_diam_image_iff hK hne]
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨((f, c), (⟨s, hs⟩, ⟨t, ht⟩)), h, rfl⟩
  · rintro ⟨⟨⟨g, d⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, h, hxeq⟩
    simp only [Prod.mk.injEq] at hxeq
    obtain ⟨rfl, rfl⟩ := hxeq
    exact ⟨s, hs, t, ht, h⟩

end Diam

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `δ ≥ 0`, the closed ball `closedBall w δ` is `w + δ • closedBall 0 1`. -/
theorem _root_.Metric.closedBall_subset_iff_forall_add_smul {w : E} {δ : ℝ} (hδ : 0 ≤ δ)
    {S : Set E} : closedBall w δ ⊆ S ↔ ∀ u ∈ closedBall (0 : E) 1, w + δ • u ∈ S := by
  constructor
  · intro h u hu
    apply h
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ]
    exact mul_le_of_le_one_right hδ (mem_closedBall_zero_iff.mp hu)
  · intro h z hz
    rcases hδ.eq_or_lt with rfl | hδ
    · have hzw : z = w := by simpa using hz
      simpa [hzw] using h 0 (by simp)
    · have hu : δ⁻¹ • (z - w) ∈ closedBall (0 : E) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
        rw [mem_closedBall, dist_eq_norm] at hz
        exact (inv_mul_le_one₀ hδ).2 hz
      have := h _ hu
      rwa [smul_inv_smul₀ hδ.ne', add_sub_cancel] at this

variable [ProperSpace E]

/-- For compact `K ⊆ ℝ` and `n`, the pairs `(f, δ)` with `δ ≥ 0` such that the image of `K`
contains a closed ball of radius `δ` centred in `closedBall 0 n` form a closed set. -/
theorem isClosed_setOf_closedBall_subset_image {K : Set ℝ} (hK : IsCompact K) (n : ℝ) :
    IsClosed {p : C(ℝ, E) × ℝ | 0 ≤ p.2 ∧ ∃ w ∈ closedBall (0 : E) n, closedBall w p.2 ⊆ p.1 '' K} := by
  have : CompactSpace (closedBall (0 : E) n) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 n)
  have hcl : IsClosed ({q : (C(ℝ, E) × ℝ) × closedBall (0 : E) n | 0 ≤ q.1.2} ∩
      ⋂ u ∈ closedBall (0 : E) 1, {q | (q.2 : E) + q.1.2 • u ∈ q.1.1 '' K}) := by
    refine (isClosed_le continuous_const continuous_fst.snd).inter
      (isClosed_biInter fun u _ => ?_)
    exact (isClosed_setOf_mem_image hK).preimage (continuous_fst.fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).add (continuous_fst.snd.smul continuous_const)))
  convert isClosedMap_fst_of_compactSpace _ hcl using 1
  ext ⟨f, δ⟩
  constructor
  · rintro ⟨hδ, w, hw, hsub⟩
    refine ⟨((f, δ), ⟨w, hw⟩), ⟨hδ, ?_⟩, rfl⟩
    exact mem_iInter₂.2 fun u hu => (closedBall_subset_iff_forall_add_smul hδ).1 hsub u hu
  · rintro ⟨⟨⟨g, d⟩, ⟨w, hw⟩⟩, ⟨hδ, hsub⟩, hxeq⟩
    simp only [Prod.mk.injEq] at hxeq
    obtain ⟨rfl, rfl⟩ := hxeq
    exact ⟨hδ, w, hw, (closedBall_subset_iff_forall_add_smul hδ).2
      fun u hu => mem_iInter₂.1 hsub u hu⟩

/-- For compact `K ⊆ ℝ`, the pairs `(f, δ)` with `δ ≥ 0` such that the image of `K` contains a
closed ball of radius `δ` form a measurable set. -/
theorem measurableSet_setOf_exists_closedBall_subset_image {K : Set ℝ} (hK : IsCompact K) :
    MeasurableSet {p : C(ℝ, E) × ℝ | 0 ≤ p.2 ∧ ∃ w, closedBall w p.2 ⊆ p.1 '' K} := by
  have hset : {p : C(ℝ, E) × ℝ | 0 ≤ p.2 ∧ ∃ w, closedBall w p.2 ⊆ p.1 '' K} =
      ⋃ n : ℕ, {p : C(ℝ, E) × ℝ | 0 ≤ p.2 ∧
        ∃ w ∈ closedBall (0 : E) n, closedBall w p.2 ⊆ p.1 '' K} := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hδ, w, hw⟩
      obtain ⟨n, hn⟩ := exists_nat_ge ‖w‖
      exact ⟨n, hδ, w, mem_closedBall_zero_iff.2 hn, hw⟩
    · rintro ⟨n, hδ, w, -, hw⟩
      exact ⟨hδ, w, hw⟩
  rw [hset]
  exact MeasurableSet.iUnion fun n => (isClosed_setOf_closedBall_subset_image hK n).measurableSet

end Ball

end ContinuousMap

namespace MatedCRTHarmonic

namespace MatedCRT

open ContinuousMap

/-- The curves `c` for which the event `E_ε(R, r)` fails (some segment in `B_R(0)` of diameter at
least `δ ^ (1 - r)`, `δ ∈ (0, ε]`, contains no ball of radius `δ`) form an analytic set. -/
theorem analyticSet_setOf_not_segmentsContainBalls (R r ε : ℝ) :
    AnalyticSet {c : C(ℝ, ℂ) | ¬ SegmentsContainBalls c R r ε} := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  set G : C(C(ℝ, ℂ) × ℝ × ℝ, C(ℝ, ℂ)) := segmentReparam with hGdef
  have hG : Continuous fun q : C(ℝ, ℂ) × ℝ × ℝ × ℝ => G (q.1, q.2.2) :=
    G.continuous.comp (continuous_fst.prodMk continuous_snd.snd)
  set T : Set (C(ℝ, ℂ) × ℝ × ℝ × ℝ) := {q | (0 < q.2.1 ∧ q.2.1 ≤ ε) ∧ q.2.2.1 < q.2.2.2 ∧
      MapsTo (G (q.1, q.2.2)) (Icc 0 1) (ball 0 R) ∧
      q.2.1 ^ (1 - r) ≤ diam (G (q.1, q.2.2) '' Icc 0 1) ∧
      ¬ (0 ≤ q.2.1 ∧ ∃ w, closedBall w q.2.1 ⊆ G (q.1, q.2.2) '' Icc 0 1)} with hTdef
  have hT : MeasurableSet T := by
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
      (MeasurableSet.inter ?_ ?_)))
    · exact (measurableSet_lt measurable_const measurable_snd.fst).inter
        (measurableSet_le measurable_snd.fst measurable_const)
    · exact measurableSet_lt measurable_snd.snd.fst measurable_snd.snd.snd
    · exact hG.measurable (isOpen_setOfPred_mapsTo isCompact_Icc isOpen_ball).measurableSet
    · exact (hG.measurable.prodMk (measurable_snd.fst.pow_const (1 - r)))
        (isClosed_setOf_le_diam_image isCompact_Icc (nonempty_Icc.2 zero_le_one)).measurableSet
    · exact ((hG.measurable.prodMk measurable_snd.fst)
        (measurableSet_setOf_exists_closedBall_subset_image isCompact_Icc)).compl
  have hset : {c : C(ℝ, ℂ) | ¬ SegmentsContainBalls c R r ε} = Prod.fst '' T := by
    ext c
    constructor
    · intro hc
      by_contra hT'
      apply hc
      intro δ hδ a b hab hR hdiam
      by_contra hw
      have hEq : G (c, a, b) '' Icc 0 1 = c '' Icc a b := segmentReparam_image_Icc c hab.le
      refine hT' ⟨(c, δ, a, b), ⟨hδ, hab, ?_, ?_, ?_⟩, rfl⟩
      · rw [← hEq] at hR
        exact image_subset_iff.1 hR
      · show δ ^ (1 - r) ≤ diam (G (c, a, b) '' Icc 0 1)
        rw [hEq]
        exact hdiam
      · show ¬ (0 ≤ δ ∧ ∃ w, closedBall w δ ⊆ G (c, a, b) '' Icc 0 1)
        rw [hEq]
        rintro ⟨-, w, hw'⟩
        exact hw ⟨w, ball_subset_closedBall.trans hw'⟩
    · rintro ⟨⟨f, δ, a, b⟩, ⟨hδ, hab, hR, hdiam, hw⟩, rfl⟩ hc
      have hEq : G (f, a, b) '' Icc 0 1 = f '' Icc a b := segmentReparam_image_Icc f hab.le
      have hR' : f '' Icc a b ⊆ ball 0 R := by
        rw [← hEq]
        exact image_subset_iff.2 hR
      have hdiam' : δ ^ (1 - r) ≤ diam (f '' Icc a b) := by
        rw [← hEq]
        exact hdiam
      obtain ⟨w, hw'⟩ := hc δ hδ a b hab hR' hdiam'
      apply hw
      refine ⟨hδ.1.le, w, ?_⟩
      show closedBall w δ ⊆ G (f, a, b) '' Icc 0 1
      rw [hEq, ← closure_ball w hδ.1.ne']
      exact closure_minimal hw' (isCompact_Icc.image f.continuous).isClosed
  rw [hset]
  exact hT.analyticSet.image_of_continuous continuous_fst

/-- The event `E_ε(R, r)` is null-measurable for every finite Borel measure on `C(ℝ, ℂ)`. -/
theorem nullMeasurableSet_setOf_not_segmentsContainBalls (μ : Measure C(ℝ, ℂ)) [IsFiniteMeasure μ]
    (R r ε : ℝ) : NullMeasurableSet {c : C(ℝ, ℂ) | ¬ SegmentsContainBalls c R r ε} μ := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  exact LatticeProb.AnalyticSet.nullMeasurableSet μ (analyticSet_setOf_not_segmentsContainBalls R r ε)

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- The segment-ball clause of a mating-of-trees coupling holds, with the same constants, for a
measurable random element of the data space with the law of a coupling. -/
theorem IsCouplingData.segmentsContainBalls_of_map_eq (hC : IsCouplingData γ P V)
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V) :
    ∀ R : ℝ, 0 < R → ∀ r ∈ Ioo (0 : ℝ) 1, ∀ N : ℕ, ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P' {ω | ¬ SegmentsContainBalls (V' ω).ηL R r ε} ≤ ENNReal.ofReal (C * ε ^ N) := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have := hCP.isProbabilityMeasure
  intro R hR r hr N
  obtain ⟨C, hCε⟩ := hCP.segmentsContainBalls R hR r hr N
  refine ⟨C, fun ε hε => le_trans ?_ (hCε ε hε)⟩
  have hlawL : P'.map (fun ω => (V' ω).ηL) = P.map (fun ω => (V ω).ηL) :=
    map_comp_of_map_eq hV hV' hlaw measurable_ηL
  exact measure_preimage_le_of_map_eq (measurable_ηL.comp hV) (measurable_ηL.comp hV') hlawL
    (nullMeasurableSet_setOf_not_segmentsContainBalls _ R r ε)

end MatedCRT

end MatedCRTHarmonic

end
