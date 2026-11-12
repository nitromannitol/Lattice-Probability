/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordVarianceAux1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScale
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCovMeas
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

/-!
# Node `V47`, auxiliary file 1: segment measures, splitting, growth and couplings

Measure-theoretic tools for the variance bound (4.7):

* Lebesgue measure on adjacent intervals, and affine images of `Leb|[0,1]`;
* **splitting** of the uniform measure on a chord into sub-chords (`toMeasure_wc_lin`);
* the **forward-edge growth bound**: a polygon whose edges all advance along a fixed direction
  at a fixed rate has growth constant independent of the number of edges (`forward_growth`);
* couplings of single segments;
* transport of growth bounds and couplings under similarities `z ↦ α z + β`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RecVar

open Blueprint.Draft

/-! ## Lebesgue measure on adjacent intervals -/

lemma restrict_Icc_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    volume.restrict (Icc a b) + volume.restrict (Icc b c) = volume.restrict (Icc a c) := by
  have h := Measure.restrict_union_add_inter (μ := (volume : Measure ℝ)) (Icc a b)
    (measurableSet_Icc (a := b) (b := c))
  rw [Icc_union_Icc_eq_Icc hab hbc, Icc_inter_Icc_eq_singleton hab hbc,
    Measure.restrict_eq_zero.2 Real.volume_singleton, add_zero] at h
  exact h.symm

lemma sum_restrict_Icc (P : ℕ → ℝ) (hP : ∀ i, P i ≤ P (i + 1)) (m : ℕ) :
    ∑ i ∈ Finset.range m, volume.restrict (Icc (P i) (P (i + 1))) =
      volume.restrict (Icc (P 0) (P m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih,
      restrict_Icc_add (monotone_nat_of_le_succ hP (Nat.zero_le m)) (hP m)]

/-- Affine image of the uniform measure on `[0,1]`. -/
lemma map_affine_restrict (a : ℝ) {h : ℝ} (hh : 0 < h) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun s : ℝ => a + s * h) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Icc a (a + h)) := by
  have hf : Measurable (fun s : ℝ => a + s * h) := by fun_prop
  ext B hB
  rw [Measure.map_apply hf hB, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
    Measure.restrict_apply (hf hB)]
  have e : (fun s : ℝ => a + s * h) ⁻¹' B ∩ Icc 0 1 =
      (· * h) ⁻¹' ((fun x => a + x) ⁻¹' (B ∩ Icc a (a + h))) := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · by_contra hs; push Not at hs; nlinarith
      · by_contra hs; push Not at hs; nlinarith
  rw [e, Real.volume_preimage_mul_right hh.ne', measure_preimage_add,
    abs_of_pos (inv_pos.2 hh)]

/-! ## Splitting a chord -/

/-- The point with parameter `t` on the line through `x` and `y`. -/
def lin (x y : ℂ) (t : ℝ) : ℂ := x + (t : ℂ) * (y - x)

lemma measurable_lin (x y : ℂ) : Measurable (lin x y) := by
  unfold lin; fun_prop

lemma segMeas_lin (x y : ℂ) {σ τ : ℝ} (hστ : σ ≤ τ) :
    ENNReal.ofReal (τ - σ) •
        ConstrCov.segMeas (lin x y σ) (lin x y τ) =
      (volume.restrict (Icc σ τ)).map (lin x y) := by
  rcases eq_or_lt_of_le hστ with h | h
  · subst h; simp
  · have haff : Measurable (fun s : ℝ => σ + s * (τ - σ)) := by fun_prop
    have e : (fun s : ℝ => lin x y σ +
        (s : ℂ) * (lin x y τ - lin x y σ)) =
        lin x y ∘ (fun s : ℝ => σ + s * (τ - σ)) := by
      funext s; simp only [lin, Function.comp]; push_cast; ring
    have hpos : 0 < τ - σ := sub_pos.2 h
    rw [ConstrCov.segMeas, e, ← Measure.map_map (measurable_lin x y) haff,
      map_affine_restrict σ hpos, Measure.map_smul _ (measurable_lin x y).aemeasurable,
      smul_smul, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
      one_smul, add_sub_cancel]

/-- **Splitting**: the chord pieces with parameters `τ 0 ≤ τ 1 ≤ … ≤ τ m` and weights
`τ (i+1) - τ i` add up to the uniform measure on the parameter interval `[τ 0, τ m]`. -/
lemma toMeasure_wc_lin (x y : ℂ) (τ : ℕ → ℝ) (hτ : ∀ i, τ i ≤ τ (i + 1)) (m : ℕ)
    (W : ℕ → ℝ) (hW : ∀ i, W i = τ (i + 1) - τ i) :
    (ConstrCov.wc m W (fun i => lin x y (τ i))).toMeasure =
      (volume.restrict (Icc (τ 0) (τ m))).map (lin x y) := by
  rw [ConstrCov.toMeasure_wc]
  have h1 : ((List.range m).map fun i => ENNReal.ofReal (W i) •
      ConstrCov.segMeas (lin x y (τ i)) (lin x y (τ (i + 1)))) =
      (List.range m).map fun i =>
        (volume.restrict (Icc (τ i) (τ (i + 1)))).map (lin x y) :=
    List.map_congr_left fun i _ => by rw [hW i, segMeas_lin x y (hτ i)]
  rw [h1]
  have h2 := ConstrCov.map_list_sum (measurable_lin x y)
    ((List.range m).map fun i => (volume : Measure ℝ).restrict (Icc (τ i) (τ (i + 1))))
  simp only [List.map_map, Function.comp_def] at h2
  rw [← h2, LFPPRecords.sum_map_range_eq, sum_restrict_Icc τ hτ m]

/-! ## Growth bounds -/

lemma growth_of_le {μ : Measure ℂ} {K : ℝ} (hK : 1 ≤ K)
    (h1 : ∀ z : ℂ, ∀ t > 0, μ (Metric.ball z t) ≤ 1)
    (h2 : ∀ z : ℂ, ∀ t > 0, μ (Metric.ball z t) ≤ ENNReal.ofReal (K * t)) :
    GrowthBound μ K 1 := by
  intro z t ht
  have a1 : (μ (Metric.ball z t)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact h1 z t ht)
  have a2 : (μ (Metric.ball z t)).toReal ≤ K * t :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by linarith) ht.le) (h2 z t ht)
  rw [div_one]
  rcases le_or_gt t 1 with htt | htt
  · rw [min_eq_right htt]; exact a2
  · rw [min_eq_left htt.le, mul_one]; linarith

lemma growth_mono {μ : Measure ℂ} {L L' R : ℝ} (hR : 0 ≤ R) (hG : GrowthBound μ L R)
    (hL : L ≤ L') : GrowthBound μ L' R := fun z t ht =>
  (hG z t ht).trans (mul_le_mul_of_nonneg_right hL
    (le_min zero_le_one (div_nonneg ht.le hR)))

lemma segMeas_growth {a b : ℂ} (hab : a ≠ b) {K : ℝ} (hK : 1 ≤ K) (hKab : 2 ≤ K * ‖b - a‖) :
    GrowthBound (ConstrCov.segMeas a b) K 1 := by
  refine growth_of_le hK (fun z t _ => ?_) (fun z t ht => ?_)
  · rw [← ConstrCov.segMeas_univ a b]; exact measure_mono (subset_univ _)
  · refine (ConstrCov.segMeas_ball_le a b z hab ht).trans (ENNReal.ofReal_le_ofReal ?_)
    have hv : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hab))
    rw [div_le_iff₀ hv]; nlinarith

lemma toMeasure_single (a b : ℂ) :
    SegComb.toMeasure [((1 : ℝ), a, b)] = ConstrCov.segMeas a b := by
  rw [TwoScale.toMeasure_cons, TwoScale.toMeasure_nil, add_zero, ENNReal.ofReal_one, one_smul]
  rfl

/-- Projection onto the direction of `v`, relative to `x`. -/
def proj (x v : ℂ) (p : ℂ) : ℝ := ((p - x) * (starRingEnd ℂ) v).re / ‖v‖

lemma abs_proj_sub_le (x : ℂ) {v : ℂ} (hv : v ≠ 0) (p q : ℂ) :
    |proj x v p - proj x v q| ≤ ‖p - q‖ := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold proj
  rw [← sub_div, ← Complex.sub_re, ← sub_mul, show p - x - (q - x) = p - q by ring, abs_div,
    abs_of_pos hv', div_le_iff₀ hv']
  calc |((p - q) * (starRingEnd ℂ) v).re| ≤ ‖(p - q) * (starRingEnd ℂ) v‖ :=
        Complex.abs_re_le_norm _
    _ = ‖p - q‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]

lemma proj_segPt (x v a b : ℂ) (s : ℝ) :
    proj x v (a + (s : ℂ) * (b - a)) = proj x v a + s * (proj x v b - proj x v a) := by
  unfold proj
  have : ((a + (s : ℂ) * (b - a) - x) * (starRingEnd ℂ) v).re =
      ((a - x) * (starRingEnd ℂ) v).re +
        s * (((b - x) * (starRingEnd ℂ) v).re - ((a - x) * (starRingEnd ℂ) v).re) := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [this]; ring

lemma segMeas_ball_le_proj (x : ℂ) {v : ℂ} (hv : v ≠ 0) (a b z : ℂ) (t : ℝ)
    (hD : 0 < proj x v b - proj x v a) :
    ConstrCov.segMeas a b (Metric.ball z t) ≤
      ENNReal.ofReal (proj x v b - proj x v a)⁻¹ *
        volume.restrict (Icc (proj x v a) (proj x v b)) (Ioo (proj x v z - t) (proj x v z + t)) := by
  set D := proj x v b - proj x v a with hDdef
  have hmeas : Measurable fun s : ℝ => a + (s : ℂ) * (b - a) := by fun_prop
  have haff : Measurable fun s : ℝ => proj x v a + s * D := by fun_prop
  have h1 : ConstrCov.segMeas a b (Metric.ball z t) ≤
      (volume.restrict (Icc (0 : ℝ) 1)).map (fun s : ℝ => proj x v a + s * D)
        (Ioo (proj x v z - t) (proj x v z + t)) := by
    unfold ConstrCov.segMeas
    rw [Measure.map_apply hmeas measurableSet_ball, Measure.map_apply haff measurableSet_Ioo]
    refine measure_mono fun s hs => ?_
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hs ⊢
    have h := lt_of_le_of_lt (abs_proj_sub_le x hv (a + (s : ℂ) * (b - a)) z) hs
    rw [proj_segPt, ← hDdef] at h
    rw [mem_Ioo]
    constructor <;> linarith [(abs_lt.1 h).1, (abs_lt.1 h).2]
  refine h1.trans (le_of_eq ?_)
  rw [map_affine_restrict _ hD, Measure.smul_apply, smul_eq_mul,
    show proj x v a + D = proj x v b by rw [hDdef]; ring]

lemma le_of_chain (P : ℕ → ℝ) {m : ℕ} (hP : ∀ i < m, P i ≤ P (i + 1)) : P 0 ≤ P m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact (ih fun i hi => hP i (by omega)).trans (hP m (by omega))

lemma sum_restrict_Icc' (P : ℕ → ℝ) {m : ℕ} (hP : ∀ i < m, P i ≤ P (i + 1)) :
    ∑ i ∈ Finset.range m, volume.restrict (Icc (P i) (P (i + 1))) =
      volume.restrict (Icc (P 0) (P m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih fun i hi => hP i (by omega),
      restrict_Icc_add (le_of_chain P fun i hi => hP i (by omega)) (hP m (by omega))]

/-- **Forward-edge growth bound.**  If every edge advances along the direction `v` by at least
`W i / κ`, the combination has growth `2 κ t` on balls of radius `t`, whatever the number of
edges. -/
lemma forward_growth {m : ℕ} {W : ℕ → ℝ} {V : ℕ → ℂ} (x : ℂ) {v : ℂ} (hv : v ≠ 0) {κ : ℝ}
    (hκ : 0 ≤ κ) (hW0 : ∀ i < m, 0 ≤ W i)
    (hD : ∀ i < m, 0 < proj x v (V (i + 1)) - proj x v (V i))
    (hWD : ∀ i < m, W i ≤ κ * (proj x v (V (i + 1)) - proj x v (V i)))
    (z : ℂ) (t : ℝ) :
    (ConstrCov.wc m W V).toMeasure (Metric.ball z t) ≤ ENNReal.ofReal (2 * κ * t) := by
  rw [ConstrCov.toMeasure_wc, ConstrCov.measure_list_sum_apply, List.map_map,
    ConstrCov.list_sum_map_range_ennreal]
  simp only [Function.comp, Measure.smul_apply, smul_eq_mul]
  set I := Ioo (proj x v z - t) (proj x v z + t) with hI
  set P : ℕ → ℝ := fun i => proj x v (V i) with hP
  have hmono : ∀ i < m, P i ≤ P (i + 1) := fun i hi => by
    show proj x v (V i) ≤ proj x v (V (i + 1)); linarith [hD i hi]
  calc ∑ i ∈ Finset.range m,
        ENNReal.ofReal (W i) * ConstrCov.segMeas (V i) (V (i + 1)) (Metric.ball z t)
      ≤ ∑ i ∈ Finset.range m,
          ENNReal.ofReal κ * volume.restrict (Icc (P i) (P (i + 1))) I := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hDi := hD i hi'
        calc ENNReal.ofReal (W i) * ConstrCov.segMeas (V i) (V (i + 1)) (Metric.ball z t)
            ≤ ENNReal.ofReal (W i) * (ENNReal.ofReal (proj x v (V (i + 1)) - proj x v (V i))⁻¹ *
                volume.restrict (Icc (P i) (P (i + 1))) I) := by
              gcongr
              exact segMeas_ball_le_proj x hv (V i) (V (i + 1)) z t hDi
          _ = ENNReal.ofReal (W i * (proj x v (V (i + 1)) - proj x v (V i))⁻¹) *
                volume.restrict (Icc (P i) (P (i + 1))) I := by
              rw [← mul_assoc, ENNReal.ofReal_mul (hW0 i hi')]
          _ ≤ ENNReal.ofReal κ * volume.restrict (Icc (P i) (P (i + 1))) I := by
              gcongr
              rw [← div_eq_mul_inv, div_le_iff₀ hDi]
              exact hWD i hi'
    _ = ENNReal.ofReal κ * volume.restrict (Icc (P 0) (P m)) I := by
        rw [← Finset.mul_sum, ← Measure.finsetSum_apply, sum_restrict_Icc' P hmono]
    _ ≤ ENNReal.ofReal κ * volume I := by
        gcongr; exact Measure.restrict_le_self
    _ = ENNReal.ofReal (2 * κ * t) := by
        rw [hI, Real.volume_Ioo, ← ENNReal.ofReal_mul hκ]; ring_nf

/-! ## Couplings -/

lemma coupled_seg {a b a' b' : ℂ} {u : ℝ} (ha : ‖a - a'‖ ≤ u) (hb : ‖b - b'‖ ≤ u) :
    CoupledWithin (ConstrCov.segMeas a b) (ConstrCov.segMeas a' b') u := by
  refine ⟨(volume.restrict (Icc (0 : ℝ) 1)).map (ConstrCov.pairSeg a b a' b'), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (ConstrCov.measurable_pairSeg _ _ _ _)]; rfl
  · rw [Measure.map_map measurable_snd (ConstrCov.measurable_pairSeg _ _ _ _)]; rfl
  · rw [ae_map_iff (ConstrCov.measurable_pairSeg _ _ _ _).aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ConstrCov.norm_segPt_sub_le ha hb hs

/-! ## Similarities -/

lemma measurable_simMap (s : ℂ × ℂ) : Measurable (simMap s) := by
  unfold simMap; fun_prop

lemma simMap_sub (s : ℂ × ℂ) (u v : ℂ) : simMap s u - simMap s v = s.1 * (u - v) := by
  simp only [simMap]; ring

lemma norm_simMap_sub (s : ℂ × ℂ) (u v : ℂ) :
    ‖simMap s u - simMap s v‖ = ‖s.1‖ * ‖u - v‖ := by
  rw [simMap_sub, norm_mul]

lemma segMeas_image_simMap (s : ℂ × ℂ) (p : ℝ × ℂ × ℂ) :
    TwoScale.segMeas (p.1, simMap s p.2.1, simMap s p.2.2) =
      (TwoScale.segMeas p).map (simMap s) := by
  unfold TwoScale.segMeas
  rw [Measure.map_map (measurable_simMap s) (TwoScale.continuous_segPt p).measurable]
  congr 1; funext r; simp only [TwoScale.segPt, simMap, Function.comp]; ring

lemma toMeasure_image_simMap (s : ℂ × ℂ) (c : SegComb) :
    (c.image (simMap s)).toMeasure = c.toMeasure.map (simMap s) := by
  induction c with
  | nil => simp [SegComb.image, TwoScale.toMeasure_nil]
  | cons p c ih =>
    have : SegComb.image (simMap s) (p :: c) =
        (p.1, simMap s p.2.1, simMap s p.2.2) :: SegComb.image (simMap s) c := rfl
    rw [this, TwoScale.toMeasure_cons, TwoScale.toMeasure_cons, ih, segMeas_image_simMap,
      Measure.map_add _ _ (measurable_simMap s),
      Measure.map_smul _ (measurable_simMap s).aemeasurable]

lemma growthBound_map_simMap {μ : Measure ℂ} {L R : ℝ} {s : ℂ × ℂ} (hs : s.1 ≠ 0)
    (hG : GrowthBound μ L R) : GrowthBound (μ.map (simMap s)) L (‖s.1‖ * R) := by
  have hα : 0 < ‖s.1‖ := norm_pos_iff.2 hs
  intro z t ht
  rw [Measure.map_apply (measurable_simMap s) measurableSet_ball]
  have e : simMap s ⁻¹' Metric.ball z t = Metric.ball ((z - s.2) / s.1) (t / ‖s.1‖) := by
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm]
    rw [lt_div_iff₀ hα, ← norm_mul,
      show (w - (z - s.2) / s.1) * s.1 = simMap s w - z by
        rw [sub_mul, div_mul_cancel₀ _ hs]; simp only [simMap]; ring]
  rw [e]
  have := hG ((z - s.2) / s.1) (t / ‖s.1‖) (div_pos ht hα)
  rwa [div_div] at this

lemma coupledWithin_map_simMap {μ ν : Measure ℂ} {u : ℝ} (s : ℂ × ℂ)
    (h : CoupledWithin μ ν u) :
    CoupledWithin (μ.map (simMap s)) (ν.map (simMap s)) (‖s.1‖ * u) := by
  obtain ⟨cpl, h1, h2, hae⟩ := h
  have hF : Measurable fun q : ℂ × ℂ => (simMap s q.1, simMap s q.2) := by
    unfold simMap; fun_prop
  refine ⟨cpl.map fun q => (simMap s q.1, simMap s q.2), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hF, ← h1,
      Measure.map_map (measurable_simMap s) measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hF, ← h2,
      Measure.map_map (measurable_simMap s) measurable_snd]
    rfl
  · have hms : MeasurableSet {q : ℂ × ℂ | ‖q.1 - q.2‖ ≤ ‖s.1‖ * u} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [ae_map_iff hF.aemeasurable hms]
    filter_upwards [hae] with q hq
    show ‖simMap s q.1 - simMap s q.2‖ ≤ ‖s.1‖ * u
    rw [norm_simMap_sub]
    exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)

lemma isProb_image (f : ℂ → ℂ) {c : SegComb} (hc : c.IsProb) : (c.image f).IsProb := by
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [SegComb.image, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hc.1 q hq
  · rw [← hc.2]
    simp [SegComb.image, SegComb.mass, List.map_map, Function.comp_def]

lemma edges_map (T : ℂ → ℂ) (z : List ℂ) : edges (z.map T) = (edges z).map (Prod.map T T) := by
  simp only [edges]
  rw [← List.map_tail, List.zip_map]

lemma polyLen_map (s : ℂ × ℂ) (z : List ℂ) :
    polyLen (z.map (simMap s)) = ‖s.1‖ * polyLen z := by
  simp only [polyLen, edges_map, List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd,
    norm_simMap_sub, List.sum_map_mul_left]

lemma polyComb_map (s : ℂ × ℂ) (hs : s.1 ≠ 0) (z : List ℂ) :
    polyComb (z.map (simMap s)) = (polyComb z).image (simMap s) := by
  have hn : ‖s.1‖ ≠ 0 := norm_ne_zero_iff.2 hs
  simp only [polyComb, SegComb.image, edges_map, List.map_map, Function.comp_def, Prod.map_fst,
    Prod.map_snd, norm_simMap_sub, polyLen_map]
  exact List.map_congr_left fun e _ => by rw [mul_div_mul_left _ _ hn]

end LQGDimension.RecVar
