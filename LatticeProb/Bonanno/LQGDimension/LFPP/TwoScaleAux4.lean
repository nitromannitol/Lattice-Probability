/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TwoScaleAux4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScaleAux3

/-!
# Lemma 3.1, auxiliary file 4: the circle-average regularization

For zero-mass combinations `c, c'` whose first argument is nondegenerate,
`circCov ε c c' = (2π)⁻² ∫∫ logCov(c + ε e^{iθ}, c' + ε e^{iφ}) dθ dφ`
(`circCov_eq_avg`): the `log max(|x|, 1)` normalization terms of `gffGreen` cancel because the
masses vanish, and Fubini is justified by the integrability of the logarithmic singularity in
all four variables `(θ, φ, s, s')` (`integrable_log_tDist_fst`).

Translations preserve probability, growth and coupling (`trans`), so the unregularized bound of
`TwoScaleAux3` applies to every pair of translates, and averaging gives the regularized bound
`circCov_twoScale_bound`.

The Fubini part follows the same route as the circle-average computation of node `L31d`, but
with the *first* segment nondegenerate (the coarse side).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.TwoScale

open Blueprint.Draft HeatKernel

/-! ## Translation of segment combinations -/

/-- Translate every segment by `τ`. -/
def trans (τ : ℂ) (c : SegComb) : SegComb := c.image (· + τ)

lemma trans_cons (τ : ℂ) (p : ℝ × ℂ × ℂ) (c : SegComb) :
    trans τ (p :: c) = (p.1, p.2.1 + τ, p.2.2 + τ) :: trans τ c := rfl

lemma trans_sub (τ : ℂ) (a b : SegComb) : trans τ (a.sub b) = (trans τ a).sub (trans τ b) := by
  simp [trans, SegComb.image, SegComb.sub, List.map_append, List.map_map, Function.comp_def]

lemma isProb_trans (τ : ℂ) {c : SegComb} (hc : c.IsProb) : (trans τ c).IsProb := by
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [trans, SegComb.image, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hc.1 q hq
  · rw [← hc.2]
    simp [trans, SegComb.image, SegComb.mass, List.map_map, Function.comp_def]

lemma segMeas_trans (τ : ℂ) (p : ℝ × ℂ × ℂ) :
    segMeas (p.1, p.2.1 + τ, p.2.2 + τ) = (segMeas p).map (· + τ) := by
  unfold segMeas
  rw [Measure.map_map (measurable_add_const τ) (continuous_segPt p).measurable]
  congr 1
  funext s
  simp only [segPt, Function.comp_apply]
  ring

lemma toMeasure_trans (τ : ℂ) (c : SegComb) :
    (trans τ c).toMeasure = c.toMeasure.map (· + τ) := by
  induction c with
  | nil => simp [trans, SegComb.image, toMeasure_nil]
  | cons p c ih =>
    rw [trans_cons, toMeasure_cons, toMeasure_cons, ih, segMeas_trans,
      Measure.map_add _ _ (measurable_add_const τ),
      Measure.map_smul _ (measurable_add_const τ).aemeasurable]

lemma growthBound_map_add {μ : Measure ℂ} {L R : ℝ} (τ : ℂ) (hG : GrowthBound μ L R) :
    GrowthBound (μ.map (· + τ)) L R := by
  intro z r hr
  rw [Measure.map_apply (measurable_add_const τ) measurableSet_ball]
  have : (· + τ) ⁻¹' Metric.ball z r = Metric.ball (z - τ) r := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm]
    rw [show x + τ - z = x - (z - τ) by ring]
  rw [this]
  exact hG _ r hr

lemma coupledWithin_map_add {μ ν : Measure ℂ} {u : ℝ} (τ : ℂ) (h : CoupledWithin μ ν u) :
    CoupledWithin (μ.map (· + τ)) (ν.map (· + τ)) u := by
  obtain ⟨cpl, h1, h2, hae⟩ := h
  have hF : Measurable fun q : ℂ × ℂ => (q.1 + τ, q.2 + τ) := by fun_prop
  refine ⟨cpl.map fun q => (q.1 + τ, q.2 + τ), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hF, ← h1,
      Measure.map_map (measurable_add_const τ) measurable_fst]
    try rfl
  · rw [Measure.map_map measurable_snd hF, ← h2,
      Measure.map_map (measurable_add_const τ) measurable_snd]
    try rfl
  · have hms : MeasurableSet {q : ℂ × ℂ | ‖q.1 - q.2‖ ≤ u} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [ae_map_iff hF.aemeasurable hms]
    filter_upwards [hae] with q hq
    simpa [add_sub_add_right_eq_sub] using hq

/-- The unregularized bound for translates. -/
lemma logCov_trans_bound {μR νR μr νr : SegComb} {L R u v : ℝ}
    (hμR : μR.IsProb) (hνR : νR.IsProb) (hμr : μr.IsProb) (hνr : νr.IsProb)
    (hR : 0 < R) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hGμ : GrowthBound μR.toMeasure L R) (hGν : GrowthBound νR.toMeasure L R)
    (hcR : CoupledWithin μR.toMeasure νR.toMeasure u)
    (hcr : CoupledWithin μr.toMeasure νr.toMeasure v) (τ₁ τ₂ : ℂ) :
    |(trans τ₁ (μR.sub νR)).logCov (trans τ₂ (μr.sub νr))| ≤
      256 * L * Real.sqrt (u * v) / R := by
  rw [trans_sub, trans_sub]
  refine logCov_twoScale_bound (isProb_trans τ₁ hμR) (isProb_trans τ₁ hνR)
    (isProb_trans τ₂ hμr) (isProb_trans τ₂ hνr) hR hu hv ?_ ?_ ?_ ?_
  · rw [toMeasure_trans]; exact growthBound_map_add τ₁ hGμ
  · rw [toMeasure_trans]; exact growthBound_map_add τ₁ hGν
  · rw [toMeasure_trans, toMeasure_trans]; exact coupledWithin_map_add τ₁ hcR
  · rw [toMeasure_trans, toMeasure_trans]; exact coupledWithin_map_add τ₂ hcr

/-! ## Circle parameters -/

/-- The measure `dθ dφ` on `(0, 2π]²`. -/
def circSq : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))

instance : IsFiniteMeasure circSq := by unfold circSq; infer_instance

lemma circSq_real_univ : circSq.real univ = (2 * π) ^ 2 := by
  simp [circSq, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, Real.volume_Ioc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le, sq]

lemma ae_mem_circSq : ∀ᵐ r ∂circSq, r ∈ Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π) := by
  rw [circSq, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with r hr
  exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hr

/-- The compact parameter box `[0,2π]² × [0,1]²`. -/
def box : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

lemma isCompact_box : IsCompact box :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)

lemma ae_mem_box : ∀ᵐ x ∂(circSq.prod unitSq), x ∈ box := by
  rw [circSq, unitSq, Measure.prod_restrict, Measure.prod_restrict, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem ((measurableSet_Ioc.prod measurableSet_Ioc).prod
    (measurableSet_Ioc.prod measurableSet_Ioc))] with x hx
  exact Set.prod_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self) hx

lemma integrable_box_of_continuous {g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hg : Continuous g) :
    Integrable g (circSq.prod unitSq) := by
  obtain ⟨C, hC⟩ := isCompact_box.exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_box] with x hx
  exact hC x hx

lemma integrable_unitSq_of_continuous {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    Integrable g unitSq := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hg.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_unitSq] with q hq
  exact hC q (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hq)

/-- The point `ε e^{iθ}`. -/
def cpt (ε θ : ℝ) : ℂ := (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

lemma continuous_cpt (ε : ℝ) : Continuous (cpt ε) := by unfold cpt; fun_prop

/-- The `log max(|·|, 1)` term of `gffGreen` along a translated segment. -/
def lmx (a b : ℂ) (ε s θ : ℝ) : ℝ := Real.log (max ‖a + (s : ℂ) * (b - a) + cpt ε θ‖ 1)

lemma continuous_lmx (a b : ℂ) (ε : ℝ) : Continuous fun p : ℝ × ℝ => lmx a b ε p.1 p.2 := by
  unfold lmx
  refine Continuous.log ?_ fun p => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have := continuous_cpt ε
  fun_prop

/-- `∫₀¹ log max(|a + s(b-a) + ε e^{iθ}|, 1) ds`. -/
def lmInt (a b : ℂ) (ε θ : ℝ) : ℝ := ∫ s in Ioc (0 : ℝ) 1, lmx a b ε s θ

/-- Distance between points of the segments `[a,b] + ε e^{iθ}` and `[a',b'] + ε e^{iφ}`. -/
def tDist (ε : ℝ) (a b a' b' : ℂ) (r q : ℝ × ℝ) : ℝ :=
  segDist (a + cpt ε r.1) (b + cpt ε r.1) (a' + cpt ε r.2) (b' + cpt ε r.2) q

lemma continuous_tDist (ε : ℝ) (a b a' b' : ℂ) :
    Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => tDist ε a b a' b' x.1 x.2 := by
  have := continuous_cpt ε
  unfold tDist segDist
  fun_prop

lemma segProj_translate (a b a' b' α β : ℂ) (s : ℝ) :
    segProj (a + α) (b + α) (a' + β) (b' + β) s =
      ((a + α + (s : ℂ) * (b - a) - (a' + β)).re * (b' - a').re +
        (a + α + (s : ℂ) * (b - a) - (a' + β)).im * (b' - a').im) /
      ((b' - a').re ^ 2 + (b' - a').im ^ 2) := by
  simp only [segProj, add_sub_add_right_eq_sub]

/-- Projection parameter onto the (translated) first segment, used after swapping. -/
lemma continuous_tProj' (ε : ℝ) (a b a' b' : ℂ) :
    Continuous fun x : (ℝ × ℝ) × ℝ =>
      segProj (a' + cpt ε x.1.2) (b' + cpt ε x.1.2) (a + cpt ε x.1.1) (b + cpt ε x.1.1) x.2 := by
  simp only [segProj_translate]
  have := continuous_cpt ε
  fun_prop

/-! ## The logarithmic singularity with the first segment nondegenerate -/

lemma segDist_swap (a b a' b' : ℂ) (q : ℝ × ℝ) :
    segDist a' b' a b q.swap = segDist a b a' b' q := by
  simp only [segDist, Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]

lemma integral_unitSq_swap (f : ℝ × ℝ → ℝ) : ∫ q, f q.swap ∂unitSq = ∫ q, f q ∂unitSq := by
  unfold unitSq; exact integral_prod_swap f

lemma integrable_log_segDist_fst (a b a' b' : ℂ) (hab : a ≠ b) :
    Integrable (fun q => Real.log (segDist a b a' b' q)) unitSq := by
  have h := integrable_log_segDist a' b' a b hab
  unfold unitSq at h ⊢
  refine h.swap.congr (ae_of_all _ fun q => ?_)
  simp only [Function.comp_apply, segDist_swap]

lemma segLogPair_eq_fst (a b a' b' : ℂ) (hab : a ≠ b) :
    segLogPair a b a' b' = -∫ q, Real.log (segDist a b a' b' q) ∂unitSq := by
  have hint : Integrable (fun q => -Real.log (segDist a b a' b' q)) unitSq :=
    (integrable_log_segDist_fst a b a' b' hab).neg
  rw [← integral_neg]
  unfold unitSq at hint ⊢
  rw [integral_prod _ hint]
  simp only [segLogPair, intervalIntegral.integral_of_le zero_le_one, segDist]

/-- `∫_{unitSq} |log(s' - σ(s))| ≤ ∫_{-(K+1)}^{K+1} |log u|` when `|σ| ≤ K` on `[0,1]`. -/
lemma integral_abs_log_sub_unitSq_le {σ : ℝ → ℝ} (hσ : Continuous σ) {K : ℝ}
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, |σ s| ≤ K) :
    ∫ q, |Real.log (q.2 - σ q.1)| ∂unitSq ≤ ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  have hint := integrable_abs_log_sub_unitSq hσ
  unfold unitSq at hint ⊢
  rw [integral_prod _ hint]
  have hb : ∀ s ∈ Ioc (0 : ℝ) 1, ‖∫ s' in Ioc (0 : ℝ) 1, |Real.log ((s, s').2 - σ (s, s').1)|‖ ≤
      ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    exact setIntegral_abs_log_sub_le (hK s (Ioc_subset_Icc_self hs))
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
    measure_Ioc_lt_top hb
  refine (Real.le_norm_self _).trans (h.trans (le_of_eq ?_))
  simp [Real.volume_real_Ioc]

/-- Uniform bound for `∫ |log D|` over the unit square (second segment nondegenerate). -/
lemma integral_abs_log_segDist_le (a b a' b' : ℂ) (hb' : a' ≠ b') {R K : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, segDist a b a' b' q ≤ R)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, |segProj a b a' b' s| ≤ K) :
    ∫ q, |Real.log (segDist a b a' b' q)| ∂unitSq ≤
      R + |Real.log ‖b' - a'‖| + ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  have h1 : Integrable (fun q => |Real.log (segDist a b a' b' q)|) unitSq :=
    (integrable_log_segDist a b a' b' hb').abs
  have h2' : Integrable (fun q : ℝ × ℝ => |Real.log (q.2 - segProj a b a' b' q.1)|) unitSq :=
    integrable_abs_log_sub_unitSq (continuous_segProj a b a' b')
  have h2 : Integrable (fun q : ℝ × ℝ => R + |Real.log ‖b' - a'‖| +
      |Real.log (q.2 - segProj a b a' b' q.1)|) unitSq := (integrable_const _).add h2'
  calc ∫ q, |Real.log (segDist a b a' b' q)| ∂unitSq ≤
        ∫ q, (R + |Real.log ‖b' - a'‖| + |Real.log (q.2 - segProj a b a' b' q.1)|) ∂unitSq := by
        refine integral_mono_ae h1 h2 ?_
        filter_upwards [ae_mem_unitSq, ae_ne_graph_unitSq (continuous_segProj a b a' b').measurable]
          with q hq hne
        exact abs_log_segDist_le a b a' b' hb' hR q
          (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hq) hne
    _ = R + |Real.log ‖b' - a'‖| + ∫ q, |Real.log (q.2 - segProj a b a' b' q.1)| ∂unitSq := by
        rw [integral_add (integrable_const _) h2', integral_const, unitSq_real_univ, one_smul]
    _ ≤ _ := by
        gcongr
        exact integral_abs_log_sub_unitSq_le (continuous_segProj a b a' b') hK

/-- The same bound with the *first* segment nondegenerate. -/
lemma integral_abs_log_segDist_fst_le (a b a' b' : ℂ) (hab : a ≠ b) {R K : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, segDist a' b' a b q ≤ R)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, |segProj a' b' a b s| ≤ K) :
    ∫ q, |Real.log (segDist a b a' b' q)| ∂unitSq ≤
      R + |Real.log ‖b - a‖| + ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  have h := integral_unitSq_swap (fun q => |Real.log (segDist a' b' a b q)|)
  simp only [segDist_swap] at h
  rw [h]
  exact integral_abs_log_segDist_le a' b' a b hab hR hK

/-- **Integrability of the logarithmic singularity in all four variables** (first segment
nondegenerate). -/
lemma integrable_log_tDist_fst (ε : ℝ) (a b a' b' : ℂ) (hab : a ≠ b) :
    Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.log (tDist ε a b a' b' x.1 x.2))
      (circSq.prod unitSq) := by
  have hmeas : Measurable fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.log (tDist ε a b a' b' x.1 x.2) :=
    (continuous_tDist ε a b a' b').measurable.log
  have hcR : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) =>
      segDist (a' + cpt ε x.1.2) (b' + cpt ε x.1.2) (a + cpt ε x.1.1) (b + cpt ε x.1.1) x.2 := by
    have := continuous_cpt ε
    unfold segDist
    fun_prop
  obtain ⟨R, hR⟩ := isCompact_box.exists_bound_of_continuousOn hcR.continuousOn
  obtain ⟨K, hK⟩ := ((isCompact_Icc.prod isCompact_Icc).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (continuous_tProj' ε a b a' b').continuousOn
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun r => ?_, ?_⟩
  · show Integrable (fun q => Real.log (tDist ε a b a' b' r q)) unitSq
    unfold tDist
    exact integrable_log_segDist_fst _ _ _ _ fun h => hab (add_right_cancel h)
  · refine Integrable.of_bound hmeas.aestronglyMeasurable.norm.integral_prod_right'
      (R + |Real.log ‖b - a‖| + ∫ u in (-(K + 1))..(K + 1), |Real.log u|) ?_
    filter_upwards [ae_mem_circSq] with r hr
    have h0 : 0 ≤ ∫ q, ‖Real.log (tDist ε a b a' b' r q)‖ ∂unitSq :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [Real.norm_eq_abs]
    have key := integral_abs_log_segDist_fst_le (a + cpt ε r.1) (b + cpt ε r.1) (a' + cpt ε r.2)
      (b' + cpt ε r.2) (fun h => hab (add_right_cancel h)) (R := R) (K := K)
      (fun q hq => (le_abs_self _).trans (by
        have := hR (r, q) ⟨hr, hq⟩
        rw [Real.norm_eq_abs] at this
        exact this))
      (fun s hs => by
        have := hK (r, s) ⟨hr, hs⟩
        rw [Real.norm_eq_abs] at this
        exact this)
    rw [add_sub_add_right_eq_sub] at key
    exact key

/-- The integrand of `segCircCov` in the variables `((θ, φ), (s, s'))`. -/
def grInt (ε : ℝ) (a b a' b' : ℂ) (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  gffGreen (a + (x.2.1 : ℂ) * (b - a) + (ε : ℂ) * Complex.exp ((x.1.1 : ℂ) * Complex.I))
    (a' + (x.2.2 : ℂ) * (b' - a') + (ε : ℂ) * Complex.exp ((x.1.2 : ℂ) * Complex.I))

lemma grInt_eq (ε : ℝ) (a b a' b' : ℂ) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    grInt ε a b a' b' x = -Real.log (tDist ε a b a' b' x.1 x.2) + lmx a b ε x.2.1 x.1.1 +
      lmx a' b' ε x.2.2 x.1.2 := by
  have h : ∀ (α β s s' : ℂ), a + α + s * (b + α - (a + α)) - (a' + β + s' * (b' + β - (a' + β))) =
      a + s * (b - a) + α - (a' + s' * (b' - a') + β) := by intros; ring
  simp only [grInt, gffGreen, tDist, segDist, lmx, cpt, h]

lemma integrable_grInt_fst (ε : ℝ) (a b a' b' : ℂ) (hab : a ≠ b) :
    Integrable (grInt ε a b a' b') (circSq.prod unitSq) := by
  have h1 := (integrable_log_tDist_fst ε a b a' b' hab).neg
  have h2 : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => lmx a b ε x.2.1 x.1.1) (circSq.prod unitSq) :=
    integrable_box_of_continuous ((continuous_lmx a b ε).comp
      (by fun_prop : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => (x.2.1, x.1.1)))
  have h3 : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => lmx a' b' ε x.2.2 x.1.2)
      (circSq.prod unitSq) :=
    integrable_box_of_continuous ((continuous_lmx a' b' ε).comp
      (by fun_prop : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => (x.2.2, x.1.2)))
  exact ((h1.add h2).add h3).congr (ae_of_all _ fun x => (grInt_eq ε a b a' b' x).symm)

/-- **Fubini for one pair of segments** (first segment nondegenerate). -/
lemma segCircCov_eq_fst (ε : ℝ) (a b a' b' : ℂ) (hab : a ≠ b) :
    segCircCov ε a b a' b' =
      (2 * π)⁻¹ ^ 2 * ∫ r, ∫ q, grInt ε a b a' b' (r, q) ∂unitSq ∂circSq := by
  have hf := integrable_grInt_fst ε a b a' b' hab
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  set H : ℝ × ℝ → ℝ := fun q => ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
    grInt ε a b a' b' ((θ, φ), q) with hH
  have hHae : H =ᵐ[unitSq] fun q => ∫ r, grInt ε a b a' b' (r, q) ∂circSq := by
    filter_upwards [hf.prod_left_ae] with q hq
    simp only [hH]
    unfold circSq at hq ⊢
    rw [integral_prod _ hq]
    simp only [intervalIntegral.integral_of_le h2π]
  have hHi : Integrable H unitSq := hf.integral_prod_right.congr hHae.symm
  have hseg : segCircCov ε a b a' b' = (2 * π)⁻¹ ^ 2 * ∫ q, H q ∂unitSq := by
    unfold unitSq at hHi ⊢
    rw [integral_prod _ hHi]
    simp only [segCircCov, gffCircleCov, hH, grInt, intervalIntegral.integral_of_le zero_le_one,
      integral_const_mul]
  rw [hseg, integral_congr_ae hHae, ← integral_prod_symm _ hf, integral_prod _ hf]

/-- The inner integral over the segment parameters, for fixed circle parameters. -/
lemma integral_grInt_eq_fst (ε : ℝ) (a b a' b' : ℂ) (hab : a ≠ b) (r : ℝ × ℝ) :
    ∫ q, grInt ε a b a' b' (r, q) ∂unitSq =
      segLogPair (a + cpt ε r.1) (b + cpt ε r.1) (a' + cpt ε r.2) (b' + cpt ε r.2) +
        lmInt a b ε r.1 + lmInt a' b' ε r.2 := by
  have hb2 : a + cpt ε r.1 ≠ b + cpt ε r.1 := fun h => hab (add_right_cancel h)
  have i1 : Integrable (fun q => -Real.log (segDist (a + cpt ε r.1) (b + cpt ε r.1)
      (a' + cpt ε r.2) (b' + cpt ε r.2) q)) unitSq := (integrable_log_segDist_fst _ _ _ _ hb2).neg
  have i2 : Integrable (fun q : ℝ × ℝ => lmx a b ε q.1 r.1) unitSq :=
    integrable_unitSq_of_continuous ((continuous_lmx a b ε).comp
      (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1, r.1)))
  have i3 : Integrable (fun q : ℝ × ℝ => lmx a' b' ε q.2 r.2) unitSq :=
    integrable_unitSq_of_continuous ((continuous_lmx a' b' ε).comp
      (by fun_prop : Continuous fun q : ℝ × ℝ => (q.2, r.2)))
  have hpt : ∀ q, grInt ε a b a' b' (r, q) = -Real.log (segDist (a + cpt ε r.1) (b + cpt ε r.1)
      (a' + cpt ε r.2) (b' + cpt ε r.2) q) + lmx a b ε q.1 r.1 + lmx a' b' ε q.2 r.2 := by
    intro q
    rw [grInt_eq]
    rfl
  simp only [hpt]
  have i12 : Integrable (fun q => -Real.log (segDist (a + cpt ε r.1) (b + cpt ε r.1)
      (a' + cpt ε r.2) (b' + cpt ε r.2) q) + lmx a b ε q.1 r.1) unitSq := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_neg, segLogPair_eq_fst _ _ _ _ hb2]
  unfold unitSq
  rw [integral_fun_fst (fun s => lmx a b ε s r.1), integral_fun_snd (fun s => lmx a' b' ε s r.2)]
  simp [lmInt, Real.volume_real_Ioc]

/-! ## Summation over pairs -/

lemma inner_split (c' : SegComb) (k w a : ℝ) (G B : ℝ × ℂ × ℂ → ℝ) :
    (c'.map fun p' => k * (w * p'.1 * (G p' + a + B p'))).sum =
      k * (c'.map fun p' => w * p'.1 * G p').sum + k * w * a * c'.mass +
        k * w * (c'.map fun p' => p'.1 * B p').sum := by
  induction c' with
  | nil => simp [SegComb.mass]
  | cons q c' ih =>
    rw [List.map_cons, List.sum_cons, ih, mass_cons]
    simp only [List.map_cons, List.sum_cons]
    ring

lemma outer_split (c : SegComb) (k m' : ℝ) (X A : ℝ × ℂ × ℂ → ℝ) (Bs : ℝ) :
    (c.map fun p => k * X p + k * p.1 * A p * m' + k * p.1 * Bs).sum =
      k * (c.map X).sum + k * m' * (c.map fun p => p.1 * A p).sum + k * Bs * c.mass := by
  induction c with
  | nil => simp [SegComb.mass]
  | cons q c ih =>
    rw [List.map_cons, List.sum_cons, ih, mass_cons]
    simp only [List.map_cons, List.sum_cons]
    ring

lemma logCov_trans (τ₁ τ₂ : ℂ) (c c' : SegComb) :
    (trans τ₁ c).logCov (trans τ₂ c') = (c.map fun p => (c'.map fun p' => p.1 * p'.1 *
      segLogPair (p.2.1 + τ₁) (p.2.2 + τ₁) (p'.2.1 + τ₂) (p'.2.2 + τ₂)).sum).sum := by
  simp [SegComb.logCov, trans, SegComb.image, List.map_map, Function.comp_def]

/-- The inner integral for the pair `(p, p')` at circle parameters `r`. -/
def phiPair (ε : ℝ) (p p' : ℝ × ℂ × ℂ) (r : ℝ × ℝ) : ℝ :=
  segLogPair (p.2.1 + cpt ε r.1) (p.2.2 + cpt ε r.1) (p'.2.1 + cpt ε r.2) (p'.2.2 + cpt ε r.2) +
    lmInt p.2.1 p.2.2 ε r.1 + lmInt p'.2.1 p'.2.2 ε r.2

lemma integral_grInt_eq_phiPair (ε : ℝ) (p p' : ℝ × ℂ × ℂ) (hab : p.2.1 ≠ p.2.2) (r : ℝ × ℝ) :
    ∫ q, grInt ε p.2.1 p.2.2 p'.2.1 p'.2.2 (r, q) ∂unitSq = phiPair ε p p' r :=
  integral_grInt_eq_fst ε _ _ _ _ hab r

/-- **The circle-average covariance is the average of the log covariance of translates.** -/
theorem circCov_eq_avg (ε : ℝ) (c c' : SegComb) (hc : c.Nondeg) (hm : c.mass = 0)
    (hm' : c'.mass = 0) :
    c.circCov ε c' =
      (2 * π)⁻¹ ^ 2 * ∫ r, (trans (cpt ε r.1) c).logCov (trans (cpt ε r.2) c') ∂circSq := by
  have hpair : ∀ p ∈ c, ∀ p' ∈ c',
      Integrable (fun r => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r)) circSq ∧
      p.1 * p'.1 * segCircCov ε p.2.1 p.2.2 p'.2.1 p'.2.2 =
        ∫ r, (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r) ∂circSq := by
    intro p hp p' _
    by_cases h0 : p.1 = 0
    · simp [h0]
    · have hab := hc p hp h0
      have hΦi : Integrable (phiPair ε p p') circSq :=
        (integrable_grInt_fst ε p.2.1 p.2.2 p'.2.1 p'.2.2 hab).integral_prod_left.congr
          (ae_of_all _ fun r => integral_grInt_eq_phiPair ε p p' hab r)
      refine ⟨(hΦi.const_mul _).const_mul _, ?_⟩
      rw [segCircCov_eq_fst ε _ _ _ _ hab]
      simp_rw [integral_grInt_eq_phiPair ε p p' hab]
      rw [integral_const_mul, integral_const_mul]
      ring
  have hin : ∀ p ∈ c,
      Integrable (fun r => (c'.map fun p' => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r)).sum)
        circSq ∧
      (c'.map fun p' => p.1 * p'.1 * segCircCov ε p.2.1 p.2.2 p'.2.1 p'.2.2).sum =
        ∫ r, (c'.map fun p' => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r)).sum ∂circSq := by
    intro p hp
    obtain ⟨h1, h2⟩ := integral_list_sum_map (μ := circSq) c'
      (fun p' r => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r))
      (fun p' hp' => (hpair p hp p' hp').1)
    exact ⟨h1, (congrArg List.sum (List.map_congr_left fun p' hp' =>
      (hpair p hp p' hp').2)).trans h2.symm⟩
  obtain ⟨_, h2⟩ := integral_list_sum_map (μ := circSq) c
    (fun p r => (c'.map fun p' => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r)).sum)
    (fun p hp => (hin p hp).1)
  have hcirc : c.circCov ε c' = ∫ r, (c.map fun p =>
      (c'.map fun p' => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r)).sum).sum ∂circSq := by
    rw [h2]
    exact congrArg List.sum (List.map_congr_left fun p hp => (hin p hp).2)
  rw [hcirc, ← integral_const_mul]
  congr 1
  funext r
  have hsplit : ∀ p : ℝ × ℂ × ℂ,
      (c'.map fun p' => (2 * π)⁻¹ ^ 2 * (p.1 * p'.1 * phiPair ε p p' r)).sum =
      (2 * π)⁻¹ ^ 2 * (c'.map fun p' => p.1 * p'.1 * segLogPair (p.2.1 + cpt ε r.1)
        (p.2.2 + cpt ε r.1) (p'.2.1 + cpt ε r.2) (p'.2.2 + cpt ε r.2)).sum +
        (2 * π)⁻¹ ^ 2 * p.1 * lmInt p.2.1 p.2.2 ε r.1 * c'.mass +
        (2 * π)⁻¹ ^ 2 * p.1 * (c'.map fun p' => p'.1 * lmInt p'.2.1 p'.2.2 ε r.2).sum := by
    intro p
    exact inner_split c' ((2 * π)⁻¹ ^ 2) p.1 (lmInt p.2.1 p.2.2 ε r.1)
      (fun p' => segLogPair (p.2.1 + cpt ε r.1) (p.2.2 + cpt ε r.1)
        (p'.2.1 + cpt ε r.2) (p'.2.2 + cpt ε r.2)) (fun p' => lmInt p'.2.1 p'.2.2 ε r.2)
  simp only [hsplit]
  rw [outer_split c ((2 * π)⁻¹ ^ 2) c'.mass _ (fun p => lmInt p.2.1 p.2.2 ε r.1), hm, hm',
    logCov_trans]
  ring

/-- **The regularized bound**: averaging the bound for translates. -/
theorem circCov_twoScale_bound {μR νR μr νr : SegComb} {L R u v : ℝ}
    (hμR : μR.IsProb) (hνR : νR.IsProb) (hμr : μr.IsProb) (hνr : νr.IsProb)
    (hR : 0 < R) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hGμ : GrowthBound μR.toMeasure L R) (hGν : GrowthBound νR.toMeasure L R)
    (hcR : CoupledWithin μR.toMeasure νR.toMeasure u)
    (hcr : CoupledWithin μr.toMeasure νr.toMeasure v) (ε : ℝ) :
    |(μR.sub νR).circCov ε (μr.sub νr)| ≤ 256 * L * Real.sqrt (u * v) / R := by
  have hNd : (μR.sub νR).Nondeg := nondeg_sub μR νR hμR.1 hνR.1
    (nondeg_of_growth μR hR hGμ) (nondeg_of_growth νR hR hGν)
  have hm : (μR.sub νR).mass = 0 := by rw [mass_sub, hμR.2, hνR.2]; ring
  have hm' : (μr.sub νr).mass = 0 := by rw [mass_sub, hμr.2, hνr.2]; ring
  rw [circCov_eq_avg ε _ _ hNd hm hm']
  set B := 256 * L * Real.sqrt (u * v) / R with hB
  have hbd : ∀ᵐ r ∂circSq,
      ‖(trans (cpt ε r.1) (μR.sub νR)).logCov (trans (cpt ε r.2) (μr.sub νr))‖ ≤ B :=
    ae_of_all _ fun r => by
      rw [Real.norm_eq_abs]
      exact logCov_trans_bound hμR hνR hμr hνr hR hu hv hGμ hGν hcR hcr _ _
  have h := norm_integral_le_of_norm_le_const hbd
  rw [circSq_real_univ, Real.norm_eq_abs] at h
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹ ^ 2)]
  calc (2 * π)⁻¹ ^ 2 * |∫ r, (trans (cpt ε r.1) (μR.sub νR)).logCov
        (trans (cpt ε r.2) (μr.sub νr)) ∂circSq|
      ≤ (2 * π)⁻¹ ^ 2 * (B * (2 * π) ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = B := by
        rw [inv_pow, mul_comm B, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * π) ^ 2 ≠ 0),
          one_mul]

end LQGDimension.TwoScale
