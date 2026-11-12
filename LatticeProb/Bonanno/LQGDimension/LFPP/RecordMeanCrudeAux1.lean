/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanCrudeAux1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScaleAux3

/-!
# Node `M45`, auxiliary file 1: log-kernel bounds for aligned segment combinations

All estimates of the crude mean bound (4.5) reduce to Lemma 3.1 (`TwoScale.logCov_twoScale_bound`)
applied to *single* uniform segment measures:

* `abs_mix_le`: for segments `a, a'` of length `≥ ℓ` whose endpoints are `u`-close, and segments
  `b, b'` whose endpoints are `v`-close, the four-point log pairing
  `mix a a' b b' = P(a,b) - P(a,b') - P(a',b) + P(a',b')` is at most `256 max(1, 2/ℓ) √(uv)`.
  (Growth of a segment of length `≥ ℓ` at scale `1`, and the same-parameter coupling.)
* `abs_logCov_aligned_le`: for two combinations `Σ wᵢ ν_{sᵢ}` and `Σ w'ᵢ ν_{s'ᵢ}` on a common
  index set with equal total masses, `|logCov(c - c', c - c')| ≤ 256 G (A √u + B √(2ρ))²`, where
  `A = Σ |wᵢ|`, `B = Σ |wᵢ - w'ᵢ|`, `u` bounds the endpoint displacements `sᵢ ↔ s'ᵢ`, and `ρ`
  bounds the endpoints.  (Split `c - c'` into a *shape change* `Σ wᵢ (ν_{sᵢ} - ν_{s'ᵢ})` and a
  zero-mass *weight change* `Σ βᵢ (ν_{s'ᵢ} - ν_t)`.)
* `abs_logCov_self_le`: the crude bound `|logCov(c, c)| ≤ 256 G (2 A √(2ρ))²` for any zero-mass
  combination of segments of length `≥ ℓ` in the ball of radius `ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.RMCrude

open Blueprint.Draft TwoScale

/-! ## Single segments -/

/-- Log pairing of two segments given by their endpoints. -/
def lp (a b : ℂ × ℂ) : ℝ := segLogPair a.1 a.2 b.1 b.2

/-- The four-point mixed difference of log pairings. -/
def mix (a a' b b' : ℂ × ℂ) : ℝ := lp a b - lp a b' - lp a' b + lp a' b'

/-- Growth constant at scale `1` of a segment of length `≥ ℓ`. -/
def gcst (ℓ : ℝ) : ℝ := max 1 (2 / ℓ)

lemma gcst_nonneg (ℓ : ℝ) : 0 ≤ gcst ℓ := le_trans zero_le_one (le_max_left _ _)

lemma toMeasure_single (a : ℂ × ℂ) :
    SegComb.toMeasure [((1 : ℝ), a)] = segMeas ((1 : ℝ), a) := by
  rw [toMeasure_cons, toMeasure_nil, ENNReal.ofReal_one, one_smul, add_zero]

lemma isProb_single (a : ℂ × ℂ) : SegComb.IsProb [((1 : ℝ), a)] :=
  ⟨fun p hp => by simp at hp; rw [hp]; norm_num, by simp [SegComb.mass]⟩

lemma segMeas_ball_le' (p : ℝ × ℂ × ℂ) (hab : p.2.1 ≠ p.2.2) (z : ℂ) (t : ℝ) :
    segMeas p (Metric.ball z t) ≤ ENNReal.ofReal (2 * t / ‖p.2.2 - p.2.1‖) := by
  have hv : 0 < ‖p.2.2 - p.2.1‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hab))
  unfold segMeas
  rw [Measure.map_apply (continuous_segPt p).measurable Metric.isOpen_ball.measurableSet]
  refine (Measure.restrict_apply_le _ _).trans ?_
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun s₁ hs₁ s₂ hs₂ => ?_)
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, segPt] at hs₁ hs₂
  have e : ((p.2.1 + (s₁ : ℂ) * (p.2.2 - p.2.1)) - z) - ((p.2.1 + (s₂ : ℂ) * (p.2.2 - p.2.1)) - z) =
      ((s₁ - s₂ : ℝ) : ℂ) * (p.2.2 - p.2.1) := by push_cast; ring
  have h := norm_sub_le ((p.2.1 + (s₁ : ℂ) * (p.2.2 - p.2.1)) - z)
    ((p.2.1 + (s₂ : ℂ) * (p.2.2 - p.2.1)) - z)
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  rw [le_div_iff₀ hv]
  linarith

/-- **Growth** of a single segment of length `≥ ℓ` at scale `1`. -/
lemma growth_single {a : ℂ × ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) (ha : ℓ ≤ ‖a.2 - a.1‖) :
    GrowthBound (SegComb.toMeasure [((1 : ℝ), a)]) (gcst ℓ) 1 := by
  intro z t ht
  rw [toMeasure_single]
  have hne : a.1 ≠ a.2 := by
    intro h; rw [h, sub_self, norm_zero] at ha; linarith
  have hv : 0 < ‖a.2 - a.1‖ := lt_of_lt_of_le hℓ ha
  have h1 : (segMeas ((1 : ℝ), a) (Metric.ball z t)).toReal ≤ 1 := by
    have := prob_le_one (μ := segMeas ((1 : ℝ), a)) (s := Metric.ball z t)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  have h2 : (segMeas ((1 : ℝ), a) (Metric.ball z t)).toReal ≤ 2 * t / ‖a.2 - a.1‖ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (segMeas_ball_le' ((1 : ℝ), a) hne z t)
  have h3 : 2 * t / ‖a.2 - a.1‖ ≤ 2 / ℓ * t := by
    calc 2 * t / ‖a.2 - a.1‖ ≤ 2 * t / ℓ := div_le_div_of_nonneg_left (by positivity) hℓ ha
      _ = 2 / ℓ * t := by ring
  rw [div_one]
  rcases le_or_gt t 1 with htt | htt
  · rw [min_eq_right htt]
    calc _ ≤ 2 / ℓ * t := h2.trans h3
      _ ≤ gcst ℓ * t := by gcongr; exact le_max_right _ _
  · rw [min_eq_left htt.le, mul_one]
    exact h1.trans (le_max_left _ _)

lemma norm_segPt_sub_le' {a b a' b' : ℂ} {u s : ℝ} (ha : ‖a - a'‖ ≤ u) (hb : ‖b - b'‖ ≤ u)
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

/-- **Same-parameter coupling** of two single segments. -/
lemma coupled_single {a a' : ℂ × ℂ} {u : ℝ} (h1 : ‖a.1 - a'.1‖ ≤ u) (h2 : ‖a.2 - a'.2‖ ≤ u) :
    CoupledWithin (SegComb.toMeasure [((1 : ℝ), a)]) (SegComb.toMeasure [((1 : ℝ), a')]) u := by
  rw [toMeasure_single, toMeasure_single]
  have hm : Measurable (fun s : ℝ => (segPt ((1 : ℝ), a) s, segPt ((1 : ℝ), a') s)) :=
    ((continuous_segPt _).prodMk (continuous_segPt _)).measurable
  refine ⟨(volume.restrict (Icc (0 : ℝ) 1)).map
    (fun s : ℝ => (segPt ((1 : ℝ), a) s, segPt ((1 : ℝ), a') s)), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]; rfl
  · rw [Measure.map_map measurable_snd hm]; rfl
  · rw [ae_map_iff hm.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact norm_segPt_sub_le' h1 h2 hs

lemma logCov_single_mix (a a' b b' : ℂ × ℂ) :
    SegComb.logCov (SegComb.sub [((1 : ℝ), a)] [((1 : ℝ), a')])
      (SegComb.sub [((1 : ℝ), b)] [((1 : ℝ), b')]) = mix a a' b b' := by
  rw [logCov_eq_pairing, pairing_sub_sub]
  simp [pairing, mix, lp]

/-- **Lemma 3.1 for single segments.** -/
theorem abs_mix_le {a a' b b' : ℂ × ℂ} {ℓ u v : ℝ} (hℓ : 0 < ℓ) (ha : ℓ ≤ ‖a.2 - a.1‖)
    (ha' : ℓ ≤ ‖a'.2 - a'.1‖) (hu : 0 ≤ u) (hv : 0 ≤ v) (h1 : ‖a.1 - a'.1‖ ≤ u)
    (h2 : ‖a.2 - a'.2‖ ≤ u) (h3 : ‖b.1 - b'.1‖ ≤ v) (h4 : ‖b.2 - b'.2‖ ≤ v) :
    |mix a a' b b'| ≤ 256 * gcst ℓ * √(u * v) := by
  have key := logCov_twoScale_bound (isProb_single a) (isProb_single a') (isProb_single b)
    (isProb_single b') one_pos hu hv (growth_single hℓ ha) (growth_single hℓ ha')
    (coupled_single h1 h2) (coupled_single h3 h4)
  rwa [logCov_single_mix, div_one] at key

/-! ## Combinations indexed by `range N` -/

lemma list_sum_map_range (n : ℕ) (F : ℕ → ℝ) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma logCov_range (N N' : ℕ) (g g' : ℕ → ℝ × ℂ × ℂ) :
    SegComb.logCov ((List.range N).map g) ((List.range N').map g') =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N', (g i).1 * (g' j).1 * lp (g i).2 (g' j).2 := by
  unfold SegComb.logCov
  rw [List.map_map, list_sum_map_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, List.map_map]
  rw [list_sum_map_range]
  rfl

lemma list_map_range_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- Bound for a weighted double sum. -/
lemma abs_dsum_le (N : ℕ) (a b : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (k : ℝ)
    (hK : ∀ i < N, ∀ j < N, |K i j| ≤ k) :
    |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i * b j * K i j| ≤
      (∑ i ∈ Finset.range N, |a i|) * (∑ j ∈ Finset.range N, |b j|) * k := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hK i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj))
    (by positivity)

/-- **Aligned bound.**  Shape change plus zero-mass weight change. -/
theorem abs_logCov_aligned_le {N : ℕ} (g g' : ℕ → ℝ × ℂ × ℂ) (t : ℂ × ℂ) {ℓ ρ u A B : ℝ}
    (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hmass : ∑ i ∈ Finset.range N, (g i).1 = ∑ i ∈ Finset.range N, (g' i).1)
    (hlen : ∀ i < N, ℓ ≤ ‖(g i).2.2 - (g i).2.1‖ ∧ ℓ ≤ ‖(g' i).2.2 - (g' i).2.1‖)
    (htlen : ℓ ≤ ‖t.2 - t.1‖)
    (hball : ∀ i < N, ‖(g' i).2.1‖ ≤ ρ ∧ ‖(g' i).2.2‖ ≤ ρ)
    (htball : ‖t.1‖ ≤ ρ ∧ ‖t.2‖ ≤ ρ)
    (hclose : ∀ i < N, ‖(g i).2.1 - (g' i).2.1‖ ≤ u ∧ ‖(g i).2.2 - (g' i).2.2‖ ≤ u)
    (hA : ∑ i ∈ Finset.range N, |(g i).1| ≤ A)
    (hB : ∑ i ∈ Finset.range N, |(g i).1 - (g' i).1| ≤ B) :
    |SegComb.logCov (SegComb.sub ((List.range N).map g) ((List.range N).map g'))
        (SegComb.sub ((List.range N).map g) ((List.range N).map g'))| ≤
      256 * gcst ℓ * (A * √u + B * √(2 * ρ)) ^ 2 := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans htball.1
  set w : ℕ → ℝ := fun i => (g i).1 with hw
  set w' : ℕ → ℝ := fun i => (g' i).1 with hw'
  set s : ℕ → ℂ × ℂ := fun i => (g i).2 with hs
  set s' : ℕ → ℂ × ℂ := fun i => (g' i).2 with hs'
  set β : ℕ → ℝ := fun i => w i - w' i with hβdef
  have hβ : ∑ i ∈ Finset.range N, β i = 0 := by
    rw [hβdef]; simp only; rw [Finset.sum_sub_distrib]; exact sub_eq_zero.2 hmass
  rw [logCov_eq_pairing, pairing_sub_sub, ← logCov_eq_pairing, ← logCov_eq_pairing,
    ← logCov_eq_pairing, ← logCov_eq_pairing, logCov_range, logCov_range, logCov_range,
    logCov_range]
  set T1 := ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    w i * w j * mix (s i) (s' i) (s j) (s' j) with hT1
  set T2 := ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    w i * β j * mix (s i) (s' i) (s' j) t with hT2
  set T3 := ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    β i * w j * mix (s' i) t (s j) (s' j) with hT3
  set T4 := ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    β i * β j * mix (s' i) t (s' j) t with hT4
  have hsplit : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (g i).1 * (g j).1 * lp (g i).2 (g j).2 -
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (g i).1 * (g' j).1 * lp (g i).2 (g' j).2 -
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (g' i).1 * (g j).1 * lp (g' i).2 (g j).2 +
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (g' i).1 * (g' j).1 * lp (g' i).2 (g' j).2 =
      T1 + T2 + T3 + T4 := by
    have hR : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (β j * (w i * (lp (s i) t - lp (s' i) t) + β i * lp (s' i) t) +
          β i * (w j * (lp t (s j) - lp t (s' j)) + β j * lp t (s' j)) -
          β i * (β j * lp t t)) = 0 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, hβ, zero_mul, mul_zero, zero_add, sub_zero]
    rw [hT1, hT2, hT3, hT4, ← add_zero (_ + _ + _ + _), ← hR]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hβdef, hw, hw', hs, hs', mix]
    ring
  rw [hsplit]
  have hk1 : ∀ i < N, ∀ j < N, |mix (s i) (s' i) (s j) (s' j)| ≤ 256 * gcst ℓ * √(u * u) :=
    fun i hi j hj => abs_mix_le hℓ (hlen i hi).1 (hlen i hi).2 hu hu (hclose i hi).1
      (hclose i hi).2 (hclose j hj).1 (hclose j hj).2
  have hfar : ∀ j < N, ‖(s' j).1 - t.1‖ ≤ 2 * ρ ∧ ‖(s' j).2 - t.2‖ ≤ 2 * ρ := fun j hj =>
    ⟨(norm_sub_le _ _).trans (by linarith [(hball j hj).1, htball.1]),
      (norm_sub_le _ _).trans (by linarith [(hball j hj).2, htball.2])⟩
  have h2ρ : (0 : ℝ) ≤ 2 * ρ := by linarith
  have hk2 : ∀ i < N, ∀ j < N, |mix (s i) (s' i) (s' j) t| ≤ 256 * gcst ℓ * √(u * (2 * ρ)) :=
    fun i hi j hj => abs_mix_le hℓ (hlen i hi).1 (hlen i hi).2 hu h2ρ (hclose i hi).1
      (hclose i hi).2 (hfar j hj).1 (hfar j hj).2
  have hk3 : ∀ i < N, ∀ j < N, |mix (s' i) t (s j) (s' j)| ≤ 256 * gcst ℓ * √((2 * ρ) * u) :=
    fun i hi j hj => abs_mix_le hℓ (hlen i hi).2 htlen h2ρ hu (hfar i hi).1 (hfar i hi).2
      (hclose j hj).1 (hclose j hj).2
  have hk4 : ∀ i < N, ∀ j < N, |mix (s' i) t (s' j) t| ≤ 256 * gcst ℓ * √((2 * ρ) * (2 * ρ)) :=
    fun i hi j hj => abs_mix_le hℓ (hlen i hi).2 htlen h2ρ h2ρ (hfar i hi).1 (hfar i hi).2
      (hfar j hj).1 (hfar j hj).2
  have e1 := abs_dsum_le N w w _ _ hk1
  have e2 := abs_dsum_le N w β _ _ hk2
  have e3 := abs_dsum_le N β w _ _ hk3
  have e4 := abs_dsum_le N β β _ _ hk4
  have hA0 : 0 ≤ ∑ i ∈ Finset.range N, |w i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ ∑ i ∈ Finset.range N, |β i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hA' : ∑ i ∈ Finset.range N, |w i| ≤ A := hA
  have hB' : ∑ i ∈ Finset.range N, |β i| ≤ B := hB
  have hG := gcst_nonneg ℓ
  set a := ∑ i ∈ Finset.range N, |w i|
  set b := ∑ i ∈ Finset.range N, |β i|
  have hsu : √(u * u) = u := Real.sqrt_mul_self hu
  have hsρ : √((2 * ρ) * (2 * ρ)) = 2 * ρ := Real.sqrt_mul_self h2ρ
  have hs2 : √(u * (2 * ρ)) = √u * √(2 * ρ) := Real.sqrt_mul hu _
  have hs3 : √((2 * ρ) * u) = √u * √(2 * ρ) := by rw [mul_comm]; exact hs2
  rw [hsu] at e1
  rw [hs2] at e2
  rw [hs3] at e3
  rw [hsρ] at e4
  have hsqu : √u ^ 2 = u := Real.sq_sqrt hu
  have hsqρ : √(2 * ρ) ^ 2 = 2 * ρ := Real.sq_sqrt h2ρ
  have hsu0 : 0 ≤ √u := Real.sqrt_nonneg _
  have hsρ0 : 0 ≤ √(2 * ρ) := Real.sqrt_nonneg _
  have hK : 0 ≤ 256 * gcst ℓ := by positivity
  calc |T1 + T2 + T3 + T4| ≤ |T1| + |T2| + |T3| + |T4| := by
        have := abs_add_le (T1 + T2 + T3) T4
        have := abs_add_le (T1 + T2) T3
        have := abs_add_le T1 T2
        linarith
    _ ≤ a * a * (256 * gcst ℓ * u) + a * b * (256 * gcst ℓ * (√u * √(2 * ρ))) +
        b * a * (256 * gcst ℓ * (√u * √(2 * ρ))) + b * b * (256 * gcst ℓ * (2 * ρ)) := by
        linarith
    _ ≤ A * A * (256 * gcst ℓ * u) + A * B * (256 * gcst ℓ * (√u * √(2 * ρ))) +
        B * A * (256 * gcst ℓ * (√u * √(2 * ρ))) + B * B * (256 * gcst ℓ * (2 * ρ)) := by
        have hAn : 0 ≤ A := hA0.trans hA'
        have hBn : 0 ≤ B := hB0.trans hB'
        have hAA : a * a ≤ A * A := mul_le_mul hA' hA' hA0 hAn
        have hAB : a * b ≤ A * B := mul_le_mul hA' hB' hB0 hAn
        have hBA : b * a ≤ B * A := mul_le_mul hB' hA' hA0 hBn
        have hBB : b * b ≤ B * B := mul_le_mul hB' hB' hB0 hBn
        have k1 : 0 ≤ 256 * gcst ℓ * u := by positivity
        have k2 : 0 ≤ 256 * gcst ℓ * (√u * √(2 * ρ)) := by positivity
        have k4 : 0 ≤ 256 * gcst ℓ * (2 * ρ) := by positivity
        linarith [mul_le_mul_of_nonneg_right hAA k1, mul_le_mul_of_nonneg_right hAB k2,
          mul_le_mul_of_nonneg_right hBA k2, mul_le_mul_of_nonneg_right hBB k4]
    _ = 256 * gcst ℓ * (A * √u + B * √(2 * ρ)) ^ 2 := by
        rw [add_sq, mul_pow, mul_pow, hsqu, hsqρ]; ring

/-- **Crude bound** for a zero-mass combination in `range` form. -/
theorem abs_logCov_self_range_le {N : ℕ} (g : ℕ → ℝ × ℂ × ℂ) (t : ℂ × ℂ) {ℓ ρ A : ℝ}
    (hℓ : 0 < ℓ) (hmass : ∑ i ∈ Finset.range N, (g i).1 = 0)
    (hlen : ∀ i < N, ℓ ≤ ‖(g i).2.2 - (g i).2.1‖) (htlen : ℓ ≤ ‖t.2 - t.1‖)
    (hball : ∀ i < N, ‖(g i).2.1‖ ≤ ρ ∧ ‖(g i).2.2‖ ≤ ρ) (htball : ‖t.1‖ ≤ ρ ∧ ‖t.2‖ ≤ ρ)
    (hA : ∑ i ∈ Finset.range N, |(g i).1| ≤ A) :
    |SegComb.logCov ((List.range N).map g) ((List.range N).map g)| ≤
      256 * gcst ℓ * (A * √(2 * ρ) + A * √(2 * ρ)) ^ 2 := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans htball.1
  have key := abs_logCov_aligned_le (N := N) (u := 2 * ρ) g (fun _ => ((0 : ℝ), t)) t hℓ
    (by linarith)
    (by simpa using hmass) (fun i hi => ⟨hlen i hi, htlen⟩) htlen (fun _ _ => htball) htball
    (fun i hi => ⟨(norm_sub_le _ _).trans (by linarith [(hball i hi).1, htball.1]),
      (norm_sub_le _ _).trans (by linarith [(hball i hi).2, htball.2])⟩) hA
    (by simpa using hA)
  have e : SegComb.logCov (SegComb.sub ((List.range N).map g)
        ((List.range N).map fun _ => ((0 : ℝ), t)))
      (SegComb.sub ((List.range N).map g) ((List.range N).map fun _ => ((0 : ℝ), t))) =
      SegComb.logCov ((List.range N).map g) ((List.range N).map g) := by
    rw [logCov_eq_pairing, pairing_sub_sub, ← logCov_eq_pairing, ← logCov_eq_pairing,
      ← logCov_eq_pairing, ← logCov_eq_pairing, logCov_range N N g (fun _ => ((0 : ℝ), t)),
      logCov_range N N (fun _ => ((0 : ℝ), t)) g,
      logCov_range N N (fun _ => ((0 : ℝ), t)) (fun _ => ((0 : ℝ), t))]
    simp
  rwa [e] at key

/-- Total variation of a combination. -/
def tv (c : SegComb) : ℝ := (c.map fun p => |p.1|).sum

/-- **Crude bound** for an arbitrary zero-mass combination. -/
theorem abs_logCov_self_le (c : SegComb) (t : ℂ × ℂ) {ℓ ρ A : ℝ} (hℓ : 0 < ℓ)
    (hmass : c.mass = 0) (hlen : ∀ p ∈ c, ℓ ≤ ‖p.2.2 - p.2.1‖) (htlen : ℓ ≤ ‖t.2 - t.1‖)
    (hball : ∀ p ∈ c, ‖p.2.1‖ ≤ ρ ∧ ‖p.2.2‖ ≤ ρ) (htball : ‖t.1‖ ≤ ρ ∧ ‖t.2‖ ≤ ρ)
    (hA : tv c ≤ A) :
    |c.logCov c| ≤ 256 * gcst ℓ * (A * √(2 * ρ) + A * √(2 * ρ)) ^ 2 := by
  set g : ℕ → ℝ × ℂ × ℂ := fun i => c.getD i (0, 0, 0) with hg
  have hc : (List.range c.length).map g = c := list_map_range_getD c _
  have hmem : ∀ i < c.length, g i ∈ c := fun i hi => by
    rw [hg]; simp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  rw [← hc]
  refine abs_logCov_self_range_le g t hℓ ?_ (fun i hi => hlen _ (hmem i hi)) htlen
    (fun i hi => hball _ (hmem i hi)) htball ?_
  · rw [← list_sum_map_range]
    have : ((List.range c.length).map fun i => (g i).1) = c.map fun p => p.1 := by
      rw [← hc, List.map_map, List.length_map, List.length_range]; rfl
    rw [this]; exact hmass
  · rw [← list_sum_map_range]
    have : ((List.range c.length).map fun i => |(g i).1|) = c.map fun p => |p.1| := by
      rw [← hc, List.map_map, List.length_map, List.length_range]; rfl
    rw [this]; exact hA

lemma tv_sub (c c' : SegComb) : tv (c.sub c') = tv c + tv c' := by
  unfold tv SegComb.sub
  rw [List.map_append, List.sum_append, List.map_map]
  congr 2
  apply List.map_congr_left
  intro p _
  simp

end LQGDimension.RMCrude
