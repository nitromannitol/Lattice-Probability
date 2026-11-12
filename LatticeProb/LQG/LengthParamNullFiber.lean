import LatticeProb.LQG.LengthMetricDerived

/-!
# Length-parametrized curves spend zero time at a point

For a Euclidean length metric `D` on `ℂ` and a curve `p` parametrized by `D`-length on `[0, T]`, an increment
`D(p a, p b)` is bounded by the Lebesgue time in `(a, b]` spent outside any compact set of parameters on which `p` is
constant. Summing over inscribed partitions bounds the length `T` by the time outside such a set, so every compact
constant fiber is Lebesgue-null, and the curve spends zero time at each point:
`∀ᵐ t ∈ [0, T], p t ≠ z` (`IsEuclideanLengthMetric.ae_ne_of_lengthParametrized`).

Consequence: in the Weyl scaling `e^{ξ f} · D` the value of the weight `f` at a single point never matters.
-/

namespace LatticeProb.LQG

open MeasureTheory Set
open scoped ENNReal

/-- A curve increment is bounded by the Lebesgue time outside a compact set
on which the curve is constant. -/
theorem IsEuclideanLengthMetric.ofReal_dist_le_time_outside_compact_fiber
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    {K : Set ℝ} (hK : IsCompact K) {z : ℂ} (hz : ∀ t ∈ K, p t = z) :
    ENNReal.ofReal (D (p a) (p b)) ≤ (volume.restrict Kᶜ) (Ioc a b) := by
  have hlip {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
      D (p s) (p t) ≤ t - s := by
    have h := dist_le_of_lengthParam hD hp hs ht
    rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)] at h
  let A := K ∩ Icc a b
  have hA : IsCompact A := isCompact_Icc.inter_left hK.isClosed
  by_cases hne : A.Nonempty
  · obtain ⟨c, hc⟩ := hA.exists_isLeast hne
    obtain ⟨d, hd⟩ := hA.exists_isGreatest hne
    have hcK : c ∈ K := hc.1.1
    have hdK : d ∈ K := hd.1.1
    have hac : a ≤ c := hc.1.2.1
    have hcd : c ≤ d := hc.2 hd.1
    have hdb : d ≤ b := hd.1.2.2
    have hleft : Ioo a c ⊆ Ioc a b ∩ Kᶜ := by
      intro t ht
      refine ⟨⟨ht.1, le_trans (le_of_lt ht.2) (le_trans hcd hdb)⟩, ?_⟩
      intro htK
      have := hc.2 ⟨htK, ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (le_trans hcd hdb)⟩⟩
      exact (not_lt_of_ge this) ht.2
    have hright : Ioo d b ⊆ Ioc a b ∩ Kᶜ := by
      intro t ht
      refine ⟨⟨lt_of_le_of_lt (le_trans hac hcd) ht.1, le_of_lt ht.2⟩, ?_⟩
      intro htK
      have := hd.2 ⟨htK, ⟨le_trans (le_trans hac hcd) (le_of_lt ht.1), le_of_lt ht.2⟩⟩
      exact (not_lt_of_ge this) ht.1
    have hdisj : Disjoint (Ioo a c) (Ioo d b) := by
      rw [disjoint_left]
      intro t ht ht'
      linarith [ht.2, ht'.1]
    have hmeasure : ENNReal.ofReal (c - a) + ENNReal.ofReal (b - d) ≤
        (volume.restrict Kᶜ) (Ioc a b) := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      calc
        _ = volume (Ioo a c ∪ Ioo d b) := by
          rw [measure_union hdisj measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo]
        _ ≤ volume (Ioc a b ∩ Kᶜ) := measure_mono (union_subset hleft hright)
    have hdist : D (p a) (p b) ≤ (c - a) + (b - d) := by
      have h1 := hlip (s := a) (t := c) ⟨ha, le_trans (le_trans hac hcd) hdb |>.trans hb⟩
        ⟨le_trans ha hac, le_trans hcd hdb |>.trans hb⟩ hac
      have h2 := hlip (s := d) (t := b) ⟨le_trans ha (le_trans hac hcd), le_trans hdb hb⟩
        ⟨le_trans ha hab, hb⟩ hdb
      have ht := hD.triangle (p a) (p c) (p b)
      rw [hz d hdK, ← hz c hcK] at h2
      linarith
    calc
      ENNReal.ofReal (D (p a) (p b)) ≤ ENNReal.ofReal ((c - a) + (b - d)) :=
        ENNReal.ofReal_le_ofReal hdist
      _ = ENNReal.ofReal (c - a) + ENNReal.ofReal (b - d) :=
        ENNReal.ofReal_add (sub_nonneg.mpr hac) (sub_nonneg.mpr hdb)
      _ ≤ _ := hmeasure
  · have hsub : Ioc a b ⊆ Kᶜ := by
      intro t ht htK
      exact hne ⟨t, htK, ⟨le_of_lt ht.1, ht.2⟩⟩
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_self_of_subset_left hsub, Real.volume_Ioc]
    exact ENNReal.ofReal_le_ofReal (hlip ⟨ha, le_trans hab hb⟩ ⟨le_trans ha hab, hb⟩ hab)

/-- The length of a unit-speed curve is bounded by the time spent outside any
compact set on which it is constant. -/
theorem IsEuclideanLengthMetric.curveLength_le_time_outside_compact_fiber
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    {K : Set ℝ} (hK : IsCompact K) {z : ℂ} (hz : ∀ t ∈ K, p t = z) :
    curveLength D p 0 T ≤ (volume.restrict Kᶜ) (Ioc 0 T) := by
  unfold curveLength
  apply iSup_le
  intro q
  let μ := volume.restrict Kᶜ
  calc
    _ ≤ ∑ i ∈ Finset.range q.1, μ (Ioc (q.2.1 i) (q.2.1 (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hD.symm]
      exact hD.ofReal_dist_le_time_outside_compact_fiber hp (q.2.2.2 i).1
        (q.2.2.1 (by omega)) (q.2.2.2 (i + 1)).2 hK hz
    _ = μ (⋃ i ∈ Finset.range q.1, Ioc (q.2.1 i) (q.2.1 (i + 1))) := by
      rw [measure_biUnion_finset ?_ (fun i hi => measurableSet_Ioc)]
      rintro i - j - hij
      simp only [Function.onFun]
      have hm := q.2.2.1
      rw [Set.disjoint_left]
      intro x hx hx'
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · have := hm (show i + 1 ≤ j by omega)
        exact (not_lt_of_ge (le_trans hx.2 this)) hx'.1
      · have := hm (show j + 1 ≤ i by omega)
        exact (not_lt_of_ge (le_trans hx'.2 this)) hx.1
    _ ≤ μ (Ioc 0 T) := by
      apply measure_mono
      intro x hx
      simp only [mem_iUnion, mem_Ioc] at hx
      obtain ⟨i, hi, hix, hxi⟩ := hx
      exact ⟨lt_of_le_of_lt (q.2.2.2 i).1 hix,
        le_trans hxi (q.2.2.2 (i + 1)).2⟩

/-- A compact constant fiber of a length-parametrized curve has zero
Lebesgue measure within its parameter interval. -/
theorem IsEuclideanLengthMetric.measure_compact_constant_fiber
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T)
    {K : Set ℝ} (hK : IsCompact K) {z : ℂ} (hz : ∀ t ∈ K, p t = z) :
    volume (Ioc 0 T ∩ K) = 0 := by
  have hlen := hD.curveLength_le_time_outside_compact_fiber hp hK hz
  rw [hp.2.2 0 T le_rfl hp.1 le_rfl, ← Real.volume_Ioc] at hlen
  rw [Measure.restrict_apply measurableSet_Ioc] at hlen
  have heq : volume (Ioc 0 T ∩ Kᶜ) = volume (Ioc 0 T) :=
    le_antisymm (measure_mono inter_subset_left) hlen
  have hadd := measure_inter_add_sdiff (μ := volume) (Ioc (0 : ℝ) T) hK.isClosed.measurableSet
  rw [sdiff_eq, heq] at hadd
  have hfin : volume (Ioc (0 : ℝ) T) ≠ ∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hz' := congrArg (fun x : ℝ≥0∞ => x - volume (Ioc (0 : ℝ) T)) hadd
  simpa [ENNReal.add_sub_cancel_right hfin] using hz'

/-- A length-parametrized curve spends zero Lebesgue time at each point. -/
theorem IsEuclideanLengthMetric.ae_ne_of_lengthParametrized
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) (z : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 T)), p t ≠ z := by
  let S : Set ℝ := Icc 0 T
  let : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let E : Set S := {t | p t = z}
  have hE : IsClosed E := isClosed_singleton.preimage
    (continuousOn_iff_continuous_domRestrict.mp hp.2.1)
  let K : Set ℝ := {t | t ∈ S ∧ p t = z}
  have hK : IsCompact K := by
    have h := hE.isCompact.image continuous_subtype_val
    convert h using 1
    ext t
    simp [K, E, and_comm]
  have hnull := hD.measure_compact_constant_fiber hp hK (z := z) (fun t ht => ht.2)
  have hKnull : volume K = 0 := by
    have hsub : K ⊆ (Ioc 0 T ∩ K) ∪ {0} := by
      intro t ht
      rcases eq_or_lt_of_le ht.1.1 with ht0 | ht0
      · exact Or.inr (by simpa using ht0.symm)
      · exact Or.inl ⟨⟨ht0, ht.1.2⟩, ht⟩
    apply measure_mono_null hsub
    exact measure_union_null hnull (measure_singleton 0)
  rw [ae_iff, Measure.restrict_apply' measurableSet_Icc]
  apply measure_mono_null _ hKnull
  intro t ht
  exact ⟨ht.2, not_ne_iff.mp ht.1⟩

end LatticeProb.LQG
