/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ConstrainedCovMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel

/-!
# Segment combinations on a common edge index: probability, growth, couplings, crude bounds

For `wc M W V` (weights `W i` on the edges `[V i, V (i+1)]`, `i < M`) we prove the hypotheses of
`TwoScaleCovBound`: `IsProb`, the growth bound `GrowthBound (toMeasure) L 1` when the weights are
at most proportional to the edge lengths, and couplings with displacement `u` between two
combinations with the *same weights* whose vertices are `u`-close.  We also prove the crude bound
`|logCov c c'| ≤ TV(c) TV(c') K` when all pairings are bounded by `K`, and a bound for
`segLogPair` of a bounded segment against a nondegenerate one.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.ConstrCov

open Blueprint.Draft

/-- Weights `W i` on the edges `[V i, V (i+1)]`, `i < M`. -/
def wc (M : ℕ) (W : ℕ → ℝ) (V : ℕ → ℂ) : SegComb :=
  (List.range M).map fun i : ℕ => (W i, V i, V (i + 1))

/-- The uniform probability measure on the segment `[a, b]`. -/
def segMeas (a b : ℂ) : Measure ℂ :=
  (volume.restrict (Icc (0 : ℝ) 1)).map (fun s : ℝ => a + (s : ℂ) * (b - a))

lemma measurable_segPt (a b : ℂ) : Measurable (fun s : ℝ => a + (s : ℂ) * (b - a)) := by
  fun_prop

lemma list_sum_map_range_real (n : ℕ) (F : ℕ → ℝ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma list_sum_map_range_ennreal (n : ℕ) (F : ℕ → ENNReal) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma measure_list_sum_apply {α : Type*} [MeasurableSpace α] (l : List (Measure α))
    (s : Set α) : l.sum s = (l.map fun μ => μ s).sum := by
  induction l with
  | nil => simp
  | cons μ l ih => simp [Measure.add_apply, ih]

lemma map_list_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (l : List (Measure α)) :
    l.sum.map f = (l.map fun μ => μ.map f).sum := by
  induction l with
  | nil => simp
  | cons μ l ih => simp [Measure.map_add _ _ hf, ih]

lemma ae_list_sum {α : Type*} [MeasurableSpace α] (l : List (Measure α)) {p : α → Prop}
    (h : ∀ μ ∈ l, ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂l.sum, p x := by
  induction l with
  | nil => simp
  | cons μ l ih =>
    rw [List.sum_cons, ae_add_measure_iff]
    exact ⟨h μ (by simp), ih fun ν hν => h ν (List.mem_cons_of_mem _ hν)⟩

lemma toMeasure_wc (M : ℕ) (W : ℕ → ℝ) (V : ℕ → ℂ) :
    (wc M W V).toMeasure =
      ((List.range M).map fun i => ENNReal.ofReal (W i) • segMeas (V i) (V (i + 1))).sum := by
  unfold SegComb.toMeasure wc segMeas
  rw [List.map_map]
  rfl

lemma mass_wc (M : ℕ) (W : ℕ → ℝ) (V : ℕ → ℂ) :
    (wc M W V).mass = ∑ i ∈ Finset.range M, W i := by
  unfold SegComb.mass wc
  rw [List.map_map, ← list_sum_map_range_real]
  rfl

lemma isProb_wc {M : ℕ} {W : ℕ → ℝ} (V : ℕ → ℂ) (hW : ∀ i < M, 0 ≤ W i)
    (hsum : ∑ i ∈ Finset.range M, W i = 1) : (wc M W V).IsProb := by
  refine ⟨fun p hp => ?_, by rw [mass_wc, hsum]⟩
  unfold wc at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact hW i (List.mem_range.1 hi)

/-! ## Growth -/

lemma segMeas_univ (a b : ℂ) : segMeas a b univ = 1 := by
  unfold segMeas
  rw [Measure.map_apply (measurable_segPt a b) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  simp

lemma segMeas_ball_le (a b z : ℂ) (hab : a ≠ b) {t : ℝ} (_ht : 0 < t) :
    segMeas a b (Metric.ball z t) ≤ ENNReal.ofReal (2 * t / ‖b - a‖) := by
  have hv : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hab))
  unfold segMeas
  rw [Measure.map_apply (measurable_segPt a b) Metric.isOpen_ball.measurableSet]
  refine (Measure.restrict_apply_le _ _).trans ?_
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun s₁ hs₁ s₂ hs₂ => ?_)
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hs₁ hs₂
  have e : ((a + (s₁ : ℂ) * (b - a)) - z) - ((a + (s₂ : ℂ) * (b - a)) - z) =
      ((s₁ - s₂ : ℝ) : ℂ) * (b - a) := by push_cast; ring
  have h := norm_sub_le ((a + (s₁ : ℂ) * (b - a)) - z) ((a + (s₂ : ℂ) * (b - a)) - z)
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  rw [le_div_iff₀ hv]
  linarith

/-- **Growth bound** for `wc` combinations whose weights are at most `λ` times the edge
lengths and have total mass at most one. -/
lemma growth_wc {M : ℕ} {W : ℕ → ℝ} {V : ℕ → ℂ} {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hW0 : ∀ i < M, 0 ≤ W i) (hsum : ∑ i ∈ Finset.range M, W i ≤ 1)
    (hne : ∀ i < M, V i ≠ V (i + 1)) (hlam : ∀ i < M, W i ≤ lam * ‖V (i + 1) - V i‖) :
    GrowthBound (wc M W V).toMeasure (max 1 (2 * lam * M)) 1 := by
  intro z t ht
  rw [toMeasure_wc, measure_list_sum_apply, List.map_map, list_sum_map_range_ennreal]
  simp only [Function.comp, Measure.smul_apply, smul_eq_mul]
  set X := ∑ i ∈ Finset.range M,
    ENNReal.ofReal (W i) * segMeas (V i) (V (i + 1)) (Metric.ball z t) with hX
  have h1 : X ≤ ENNReal.ofReal 1 := by
    calc X ≤ ∑ i ∈ Finset.range M, ENNReal.ofReal (W i) := Finset.sum_le_sum fun i _ => by
          calc _ ≤ ENNReal.ofReal (W i) * 1 := by
                gcongr
                rw [← segMeas_univ (V i) (V (i + 1))]
                exact measure_mono (subset_univ _)
            _ = _ := mul_one _
      _ = ENNReal.ofReal (∑ i ∈ Finset.range M, W i) :=
          (ENNReal.ofReal_sum_of_nonneg fun i hi => hW0 i (Finset.mem_range.1 hi)).symm
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hsum
  have h2 : X ≤ ENNReal.ofReal (2 * lam * M * t) := by
    calc X ≤ ∑ i ∈ Finset.range M, ENNReal.ofReal (2 * lam * t) :=
          Finset.sum_le_sum fun i hi => by
            have hi' := Finset.mem_range.1 hi
            have hv : 0 < ‖V (i + 1) - V i‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne i hi').symm)
            calc _ ≤ ENNReal.ofReal (W i) * ENNReal.ofReal (2 * t / ‖V (i + 1) - V i‖) := by
                  gcongr; exact segMeas_ball_le _ _ _ (hne i hi') ht
              _ = ENNReal.ofReal (W i * (2 * t / ‖V (i + 1) - V i‖)) :=
                  (ENNReal.ofReal_mul (hW0 i hi')).symm
              _ ≤ ENNReal.ofReal (2 * lam * t) := ENNReal.ofReal_le_ofReal (by
                  rw [mul_div_assoc', div_le_iff₀ hv]
                  have := hlam i hi'
                  nlinarith)
      _ = ENNReal.ofReal (∑ i ∈ Finset.range M, 2 * lam * t) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm
      _ = ENNReal.ofReal (2 * lam * M * t) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring_nf
  have hX1 : X.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one h1
  have hX2 : X.toReal ≤ 2 * lam * M * t := ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  rw [div_one]
  rcases le_or_gt t 1 with htt | htt
  · rw [min_eq_right htt]
    calc X.toReal ≤ 2 * lam * M * t := hX2
      _ ≤ max 1 (2 * lam * M) * t := by gcongr; exact le_max_right _ _
  · rw [min_eq_left htt.le, mul_one]
    exact hX1.trans (le_max_left _ _)

/-! ## Couplings -/

/-- The pair of points with parameter `s` on `[a,b]` and `[a',b']`. -/
def pairSeg (a b a' b' : ℂ) (s : ℝ) : ℂ × ℂ :=
  (a + (s : ℂ) * (b - a), a' + (s : ℂ) * (b' - a'))

lemma measurable_pairSeg (a b a' b' : ℂ) : Measurable (pairSeg a b a' b') := by
  unfold pairSeg; fun_prop

lemma norm_segPt_sub_le {a b a' b' : ℂ} {u s : ℝ} (ha : ‖a - a'‖ ≤ u) (hb : ‖b - b'‖ ≤ u)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(a + (s : ℂ) * (b - a)) - (a' + (s : ℂ) * (b' - a'))‖ ≤ u := by
  have e : (a + (s : ℂ) * (b - a)) - (a' + (s : ℂ) * (b' - a')) =
      ((1 - s : ℝ) : ℂ) * (a - a') + (s : ℂ) * (b - b') := by push_cast; ring
  have h1 : 0 ≤ 1 - s := by linarith [hs.2]
  rw [e]
  calc _ ≤ ‖((1 - s : ℝ) : ℂ) * (a - a')‖ + ‖(s : ℂ) * (b - b')‖ := norm_add_le _ _
    _ = (1 - s) * ‖a - a'‖ + s * ‖b - b'‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg hs.1]
    _ ≤ (1 - s) * u + s * u := by gcongr; exact hs.1
    _ = u := by ring

/-- **Edgewise coupling** of two combinations with the same weights. -/
lemma coupled_wc {M : ℕ} {W : ℕ → ℝ} {V V' : ℕ → ℂ} {u : ℝ}
    (hV : ∀ i ≤ M, ‖V i - V' i‖ ≤ u) :
    CoupledWithin (wc M W V).toMeasure (wc M W V').toMeasure u := by
  refine ⟨((List.range M).map fun i => ENNReal.ofReal (W i) •
    (volume.restrict (Icc (0:ℝ) 1)).map (pairSeg (V i) (V (i + 1)) (V' i) (V' (i + 1)))).sum,
    ?_, ?_, ?_⟩
  · rw [map_list_sum measurable_fst, toMeasure_wc, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    rw [Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_map measurable_fst (measurable_pairSeg _ _ _ _)]
    rfl
  · rw [map_list_sum measurable_snd, toMeasure_wc, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    rw [Measure.map_smul _ measurable_snd.aemeasurable,
      Measure.map_map measurable_snd (measurable_pairSeg _ _ _ _)]
    rfl
  · refine ae_list_sum _ fun μ hμ => ?_
    rw [List.mem_map] at hμ
    obtain ⟨i, hi, rfl⟩ := hμ
    have hi' := List.mem_range.1 hi
    refine Measure.ae_smul_measure ?_ _
    rw [ae_map_iff (measurable_pairSeg _ _ _ _).aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact norm_segPt_sub_le (hV i hi'.le) (hV (i + 1) hi') hs

/-! ## Crude bounds -/

lemma abs_inner_logCov_le (p : ℝ × ℂ × ℂ) (c' : SegComb) {K : ℝ} (_hK0 : 0 ≤ K)
    (hK : ∀ p' ∈ c', |segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2| ≤ K) :
    |(c'.map fun p' => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum| ≤
      |p.1| * (c'.map fun q => |q.1|).sum * K := by
  induction c' with
  | nil => simp
  | cons q c' ih =>
    simp only [List.map_cons, List.sum_cons]
    have hq := hK q (by simp)
    have ih' := ih (fun r hr => hK r (List.mem_cons_of_mem _ hr))
    have h1 : |p.1 * q.1 * segLogPair p.2.1 p.2.2 q.2.1 q.2.2| ≤ |p.1| * |q.1| * K := by
      rw [abs_mul, abs_mul]; gcongr
    calc _ ≤ |p.1 * q.1 * segLogPair p.2.1 p.2.2 q.2.1 q.2.2| +
          |(c'.map fun p' => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum| :=
          abs_add_le _ _
      _ ≤ |p.1| * |q.1| * K + |p.1| * (c'.map fun q => |q.1|).sum * K := add_le_add h1 ih'
      _ = _ := by ring

/-- `|logCov c c'| ≤ TV(c) TV(c') K` when all pairings are bounded by `K`. -/
lemma abs_logCov_le (c c' : SegComb) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ p ∈ c, ∀ p' ∈ c', |segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2| ≤ K) :
    |c.logCov c'| ≤ (c.map fun p => |p.1|).sum * (c'.map fun p => |p.1|).sum * K := by
  unfold SegComb.logCov
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons]
    have hin := abs_inner_logCov_le p c' hK0 (hK p (by simp))
    have ih' := ih (fun q hq q' hq' => hK q (List.mem_cons_of_mem _ hq) q' hq')
    calc _ ≤ _ + _ := abs_add_le _ _
      _ ≤ |p.1| * (c'.map fun q => |q.1|).sum * K +
          (c.map fun p => |p.1|).sum * (c'.map fun p => |p.1|).sum * K := add_le_add hin ih'
      _ = _ := by ring

/-- Crude bound for the log pairing of a bounded segment with a nondegenerate one. -/
lemma abs_segLogPair_le {a b a' b' : ℂ} (hne : a' ≠ b') {R ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlen : ℓ ≤ ‖b' - a'‖) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (ha' : ‖a'‖ ≤ R) (hb' : ‖b'‖ ≤ R) :
    |segLogPair a b a' b'| ≤ 2 * R + (|Real.log ℓ| + |Real.log (2 * R)|) +
      ∫ u in (-(2 * R / ℓ + 1))..(2 * R / ℓ + 1), |Real.log u| := by
  have hv : 0 < ‖b' - a'‖ := lt_of_lt_of_le hℓ hlen
  have hR0 : 0 ≤ R := (norm_nonneg _).trans ha
  have hseg : ∀ (p q : ℂ) (s : ℝ), ‖p‖ ≤ R → ‖q‖ ≤ R → s ∈ Icc (0:ℝ) 1 →
      ‖p + (s : ℂ) * (q - p)‖ ≤ R := by
    intro p q s hp hq hs
    have e : p + (s : ℂ) * (q - p) = ((1 - s : ℝ) : ℂ) * p + (s : ℂ) * q := by push_cast; ring
    rw [e]
    calc _ ≤ ‖((1 - s : ℝ) : ℂ) * p‖ + ‖(s : ℂ) * q‖ := norm_add_le _ _
      _ = (1 - s) * ‖p‖ + s * ‖q‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2]), abs_of_nonneg hs.1]
      _ ≤ (1 - s) * R + s * R := by gcongr <;> linarith [hs.1, hs.2]
      _ = R := by ring
  have hdist : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, HeatKernel.segDist a b a' b' q ≤ 2 * R := by
    intro q hq
    unfold HeatKernel.segDist
    calc _ ≤ ‖a + (q.1 : ℂ) * (b - a)‖ + ‖a' + (q.2 : ℂ) * (b' - a')‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hseg a b q.1 ha hb hq.1) (hseg a' b' q.2 ha' hb' hq.2)
      _ = 2 * R := by ring
  have hlogv : |Real.log ‖b' - a'‖| ≤ |Real.log ℓ| + |Real.log (2 * R)| := by
    have hv2 : ‖b' - a'‖ ≤ 2 * R := by
      calc _ ≤ ‖b'‖ + ‖a'‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    have h1 := Real.log_le_log hℓ hlen
    have h2 := Real.log_le_log hv hv2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log ℓ), abs_nonneg (Real.log (2 * R))]
    · linarith [le_abs_self (Real.log (2 * R)), abs_nonneg (Real.log ℓ)]
  set J := ∫ u in (-(2 * R / ℓ + 1))..(2 * R / ℓ + 1), |Real.log u| with hJ
  have hproj : ∀ s ∈ Icc (0 : ℝ) 1, |HeatKernel.segProj a b a' b' s| ≤ 2 * R / ℓ := by
    intro s hs
    have h := HeatKernel.segDist_lower a b a' b' hne s 0
    have h2 := hdist (s, 0) ⟨hs, by simp⟩
    rw [zero_sub, abs_neg] at h
    rw [le_div_iff₀ hℓ]
    nlinarith [abs_nonneg (HeatKernel.segProj a b a' b' s)]
  have hinner : ∀ s ∈ Icc (0 : ℝ) 1, ‖∫ s' in (0:ℝ)..1,
      -Real.log ‖(a + (s : ℂ) * (b - a)) - (a' + (s' : ℂ) * (b' - a'))‖‖ ≤
      2 * R + (|Real.log ℓ| + |Real.log (2 * R)|) + J := by
    intro s hs
    set c := HeatKernel.segProj a b a' b' s
    have hcK := hproj s hs
    have hint : IntervalIntegrable (fun s' => 2 * R + |Real.log ‖b' - a'‖| + |Real.log (s' - c)|)
        volume 0 1 := by
      refine intervalIntegrable_const.add ?_
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
        (HeatKernel.integrable_abs_log_sub_Ioc c)
    refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hint).trans ?_
    · filter_upwards [(measure_eq_zero_iff_ae_notMem.1 (measure_singleton c))] with s' hs' hmem
      have hne' : s' ≠ c := hs'
      rw [Real.norm_eq_abs, abs_neg]
      exact HeatKernel.abs_log_segDist_le a b a' b' hne hdist (s, s')
        ⟨hs, Ioc_subset_Icc_self hmem⟩ hne'
    · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
          (HeatKernel.integrable_abs_log_sub_Ioc c)), intervalIntegral.integral_const,
        intervalIntegral.integral_of_le zero_le_one]
      have := HeatKernel.setIntegral_abs_log_sub_le hcK
      simp only [sub_zero, smul_eq_mul, one_mul]
      linarith
  unfold segLogPair
  rw [← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (fun s hs => hinner s (by rw [uIoc_of_le zero_le_one] at hs; exact Ioc_subset_Icc_self hs))
  simpa using this

end LQGDimension.ConstrCov
