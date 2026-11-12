/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.SimilarityCov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Node `SIM`: covariances under similarities

We prove `Blueprint.Draft.SimilarityCov`: for `α ≠ 0` and zero-mass combinations `c, c'`,

* `logCov (c.image T) (c'.image T) = logCov c c'` (needs `c'.Nondeg`), and
* `circCov ε (c.image T) (c'.image T) = circCov (ε / ‖α‖) c c'` for `ε > 0`,

where `T = simMap (α, β)`.

## Strategy

* `logCov`: `segDist` scales exactly by `‖α‖`, so, as an integral over `unitSq` (from
  `HeatKernel.segLogPair_eq`), `segLogPair` of the image segments is `segLogPair - log ‖α‖`
  whenever the second segment is nondegenerate.  The constant cancels by zero mass.
* `circCov`: the inner circle average of the singular term of `gffGreen` is computed in closed
  form by Jensen's formula (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`):
  it is `kerK ε (w - p) = log ε + log⁺ (ε⁻¹ ‖w - p‖)`, a *continuous* function.  Hence
  `gffCircleCov ε z ε w = -kerB ε (w - z) + kerA ε z + kerA ε w` with continuous `kerA`, `kerB`,
  no singular integrability is ever needed, and `kerB ε (α u) = log ‖α‖ + kerB (ε/‖α‖) u` by a
  rotation of the circle.  The one-point terms `kerA` and the constant `log ‖α‖` cancel by
  zero mass.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.SimCov

open Blueprint.Draft

/-! ## 1. Weighted double sums over zero-mass combinations -/

lemma inner_split (w : ℝ) (c' : SegComb) (G : ℝ × ℂ × ℂ → ℝ) (h : ℝ) (K : ℝ × ℂ × ℂ → ℝ) :
    (c'.map fun p' => w * p'.1 * (G p' + h + K p')).sum =
      (c'.map fun p' => w * p'.1 * G p').sum + w * h * (c'.map fun p' => p'.1).sum +
        w * (c'.map fun p' => p'.1 * K p').sum := by
  induction c' with
  | nil => simp
  | cons p' c' ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma outer_split (c c' : SegComb) (G : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ → ℝ) (H K : ℝ × ℂ × ℂ → ℝ) :
    (c.map fun p => (c'.map fun p' => p.1 * p'.1 * (G p p' + H p + K p')).sum).sum =
      (c.map fun p => (c'.map fun p' => p.1 * p'.1 * G p p').sum).sum +
        (c.map fun p => p.1 * H p).sum * (c'.map fun p' => p'.1).sum +
        (c.map fun p => p.1).sum * (c'.map fun p' => p'.1 * K p').sum := by
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, inner_split p.1 c' (G p) (H p) K]
    ring

/-- On zero-mass combinations, entries of the form `G p p' + H p + K p'` (for the pairs of
nonzero weight) contribute only through `G`. -/
lemma dsum_eq_of_mass_zero (c c' : SegComb) (hc : c.mass = 0) (hc' : c'.mass = 0)
    (F G : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ → ℝ) (H K : ℝ × ℂ × ℂ → ℝ)
    (h : ∀ p ∈ c, ∀ p' ∈ c', p.1 * p'.1 * F p p' = p.1 * p'.1 * (G p p' + H p + K p')) :
    (c.map fun p => (c'.map fun p' => p.1 * p'.1 * F p p').sum).sum =
      (c.map fun p => (c'.map fun p' => p.1 * p'.1 * G p p').sum).sum := by
  have e : (c.map fun p => (c'.map fun p' => p.1 * p'.1 * F p p').sum).sum =
      (c.map fun p => (c'.map fun p' => p.1 * p'.1 * (G p p' + H p + K p')).sum).sum :=
    congrArg List.sum (List.map_congr_left fun p hp =>
      congrArg List.sum (List.map_congr_left fun p' hp' => h p hp p' hp'))
  rw [e, outer_split]
  have hm : (c.map fun p => p.1).sum = 0 := hc
  have hm' : (c'.map fun p' => p'.1).sum = 0 := hc'
  rw [hm, hm']; ring

/-- Double sums over images. -/
lemma dsum_image (T : ℂ → ℂ) (c c' : SegComb) (f : ℂ → ℂ → ℂ → ℂ → ℝ) :
    ((c.image T).map fun p => ((c'.image T).map fun p' =>
        p.1 * p'.1 * f p.2.1 p.2.2 p'.2.1 p'.2.2).sum).sum =
      (c.map fun p => (c'.map fun p' =>
        p.1 * p'.1 * f (T p.2.1) (T p.2.2) (T p'.2.1) (T p'.2.2)).sum).sum := by
  simp only [SegComb.image, List.map_map, Function.comp_def]

/-! ## 2. The log kernel -/

lemma simMap_injective {α : ℂ} (hα : α ≠ 0) (β : ℂ) {a b : ℂ} (h : a ≠ b) :
    simMap (α, β) a ≠ simMap (α, β) b := by
  simp only [simMap]
  intro h'
  exact h (mul_left_cancel₀ hα (add_right_cancel h'))

lemma segDist_simMap (α β a b a' b' : ℂ) (q : ℝ × ℝ) :
    HeatKernel.segDist (simMap (α, β) a) (simMap (α, β) b) (simMap (α, β) a')
        (simMap (α, β) b') q = ‖α‖ * HeatKernel.segDist a b a' b' q := by
  simp only [HeatKernel.segDist, simMap]
  rw [← norm_mul]; congr 1; ring

/-- `segLogPair` of the image of a pair of segments, the second one nondegenerate. -/
lemma segLogPair_simMap {α : ℂ} (hα : α ≠ 0) (β a b a' b' : ℂ) (hb' : a' ≠ b') :
    segLogPair (simMap (α, β) a) (simMap (α, β) b) (simMap (α, β) a') (simMap (α, β) b') =
      segLogPair a b a' b' + -Real.log ‖α‖ := by
  rw [HeatKernel.segLogPair_eq _ _ _ _ (simMap_injective hα β hb'),
    HeatKernel.segLogPair_eq _ _ _ _ hb']
  have hint := HeatKernel.integrable_log_segDist a b a' b' hb'
  have hae : (fun q => Real.log (HeatKernel.segDist (simMap (α, β) a) (simMap (α, β) b)
      (simMap (α, β) a') (simMap (α, β) b') q)) =ᵐ[HeatKernel.unitSq]
      fun q => Real.log ‖α‖ + Real.log (HeatKernel.segDist a b a' b' q) := by
    filter_upwards [HeatKernel.segDist_pos_ae a b a' b' hb'] with q hq
    rw [segDist_simMap, Real.log_mul (norm_ne_zero_iff.2 hα) hq.ne']
  rw [integral_congr_ae hae, integral_add (integrable_const _) hint, integral_const,
    HeatKernel.unitSq_real_univ, one_smul]
  ring

/-- **`logCov` half of `SIM`.**  Only the second combination needs to be nondegenerate. -/
theorem similarityCov_logCov (α β : ℂ) (hα : α ≠ 0) (c c' : SegComb) (hc : c.mass = 0)
    (hc' : c'.mass = 0) (hnc' : c'.Nondeg) :
    (c.image (simMap (α, β))).logCov (c'.image (simMap (α, β))) = c.logCov c' := by
  unfold SegComb.logCov
  rw [dsum_image]
  refine dsum_eq_of_mass_zero c c' hc hc'
    (fun p p' => segLogPair (simMap (α, β) p.2.1) (simMap (α, β) p.2.2) (simMap (α, β) p'.2.1)
      (simMap (α, β) p'.2.2))
    (fun p p' => segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2) (fun _ => 0) (fun _ => -Real.log ‖α‖) ?_
  intro p _ p' hp'
  by_cases hw : p'.1 = 0
  · simp [hw]
  · rw [segLogPair_simMap hα β _ _ _ _ (hnc' p' hp' hw)]
    ring

/-! ## 3. Closed form of the inner circle average -/

/-- `log max(ε, ‖u‖)`, written as `log ε + log⁺ (ε⁻¹ ‖u‖)`: the circle average of
`q ↦ log ‖q - p‖` over `∂B(w, ε)`, with `u = w - p` (Jensen's formula). -/
def kerK (ε : ℝ) (u : ℂ) : ℝ := Real.log ε + log⁺ (ε⁻¹ * ‖u‖)

lemma continuous_kerK (ε : ℝ) : Continuous (kerK ε) := by
  unfold kerK; fun_prop

/-- The one-point part of `gffGreen`, averaged over `∂B(z, ε)`. -/
def kerA (ε : ℝ) (z : ℂ) : ℝ := circleAverage (fun v => Real.log (max ‖v‖ 1)) z ε

/-- The two-point part of `gffCircleCov`, as a function of `u = w - z`. -/
def kerB (ε : ℝ) (u : ℂ) : ℝ := circleAverage (fun v => kerK ε (u - v)) 0 ε

lemma continuous_logmax : Continuous (fun v : ℂ => Real.log (max ‖v‖ 1)) := by
  refine Continuous.log (by fun_prop) (fun v => ?_)
  exact (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

lemma continuous_circleAverage_center {g : ℂ → ℝ} (hg : Continuous g) (R : ℝ) :
    Continuous (fun z => circleAverage g z R) := by
  simp only [circleAverage_def]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun z θ => g (circleMap z R θ))
    (hg.comp (by unfold circleMap; fun_prop : Continuous fun p : ℂ × ℝ => circleMap p.1 R p.2))
    0 (2 * π)).const_smul ((2 * π)⁻¹ : ℝ)

lemma continuous_kerA (ε : ℝ) : Continuous (kerA ε) :=
  continuous_circleAverage_center continuous_logmax ε

lemma continuous_kerB (ε : ℝ) : Continuous (kerB ε) := by
  unfold kerB
  simp only [circleAverage_def]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun u θ => kerK ε (u - circleMap 0 ε θ))
    ((continuous_kerK ε).comp
      (by unfold circleMap; fun_prop : Continuous fun p : ℂ × ℝ => p.1 - circleMap 0 ε p.2))
    0 (2 * π)).const_smul ((2 * π)⁻¹ : ℝ)

lemma circleAverage_kerK (ε : ℝ) (w z : ℂ) :
    circleAverage (fun p => kerK ε (w - p)) z ε = kerB ε (w - z) := by
  rw [← circleAverage_map_add_const, kerB]
  congr 1; funext p; congr 1; ring

/-- The circle-average covariance in terms of the continuous kernels `kerA`, `kerB`. -/
lemma gffCircleCov_eq {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    gffCircleCov ε z ε w = -kerB ε (w - z) + kerA ε z + kerA ε w := by
  have h1 : gffCircleCov ε z ε w =
      circleAverage (fun p => circleAverage (fun q => gffGreen p q) w ε) z ε := by
    simp only [gffCircleCov, circleAverage_def, circleMap, smul_eq_mul,
      intervalIntegral.integral_const_mul]
    ring
  have h2 : ∀ p : ℂ, circleAverage (fun q => gffGreen p q) w ε =
      (Real.log (max ‖p‖ 1) + kerA ε w) - kerK ε (w - p) := by
    intro p
    have hfun : (fun q => gffGreen p q) =
        fun q => (Real.log (max ‖p‖ 1) + Real.log (max ‖q‖ 1)) - Real.log ‖q - p‖ := by
      funext q; simp only [gffGreen]; rw [norm_sub_rev]; ring
    have hA : CircleIntegrable (fun q => Real.log (max ‖q‖ 1)) w ε :=
      continuous_logmax.continuousOn.circleIntegrable'
    have hsum : CircleIntegrable (fun q => Real.log (max ‖p‖ 1) + Real.log (max ‖q‖ 1)) w ε :=
      (continuous_const.add continuous_logmax).continuousOn.circleIntegrable'
    rw [hfun, circleAverage_fun_sub hsum (circleIntegrable_log_norm_sub_const ε),
      circleAverage_fun_add (circleIntegrable_const _ _ _) hA, circleAverage_const,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hε.ne']
    rfl
  have hfun : (fun p => circleAverage (fun q => gffGreen p q) w ε) =
      fun p => (Real.log (max ‖p‖ 1) + kerA ε w) - kerK ε (w - p) := funext h2
  have hI1 : CircleIntegrable (fun p => Real.log (max ‖p‖ 1) + kerA ε w) z ε :=
    (continuous_logmax.add continuous_const).continuousOn.circleIntegrable'
  have hI2 : CircleIntegrable (fun p => kerK ε (w - p)) z ε :=
    ((continuous_kerK ε).comp (continuous_const.sub continuous_id)).continuousOn.circleIntegrable'
  have hI3 : CircleIntegrable (fun p => Real.log (max ‖p‖ 1)) z ε :=
    continuous_logmax.continuousOn.circleIntegrable'
  rw [h1, hfun, circleAverage_fun_sub hI1 hI2,
    circleAverage_fun_add hI3 (circleIntegrable_const _ _ _), circleAverage_const,
    circleAverage_kerK]
  simp only [kerA]
  ring

/-! ## 4. Scaling of `kerB` -/

lemma kerK_scale {ε : ℝ} (hε : 0 < ε) {α : ℂ} (hα : α ≠ 0) (u : ℂ) (θ : ℝ) :
    kerK ε (α * u - circleMap 0 ε θ) =
      Real.log ‖α‖ + kerK (ε / ‖α‖) (u - circleMap 0 (ε / ‖α‖) (θ + -Complex.arg α)) := by
  have hn : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hsplit : Complex.exp (((θ + -Complex.arg α : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((Complex.arg α : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hinv : α * Complex.exp (-((Complex.arg α : ℂ) * Complex.I)) = (‖α‖ : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I α
    calc α * Complex.exp (-((Complex.arg α : ℂ) * Complex.I))
        = (‖α‖ : ℂ) * Complex.exp ((Complex.arg α : ℂ) * Complex.I) *
            Complex.exp (-((Complex.arg α : ℂ) * Complex.I)) := by rw [h]
      _ = (‖α‖ : ℂ) := by
        rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hnc : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hrot : α * circleMap 0 (ε / ‖α‖) (θ + -Complex.arg α) = circleMap 0 ε θ := by
    simp only [circleMap, zero_add]
    rw [hsplit]
    calc α * (((ε / ‖α‖ : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) *
          Complex.exp (-((Complex.arg α : ℂ) * Complex.I))))
        = (α * Complex.exp (-((Complex.arg α : ℂ) * Complex.I))) * ((ε / ‖α‖ : ℝ) : ℂ) *
            Complex.exp ((θ : ℂ) * Complex.I) := by ring
      _ = (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [hinv]; push_cast; field_simp
  have key : α * u - circleMap 0 ε θ =
      α * (u - circleMap 0 (ε / ‖α‖) (θ + -Complex.arg α)) := by
    rw [mul_sub, hrot]
  rw [key, kerK, kerK, norm_mul]
  have e1 : ε⁻¹ * (‖α‖ * ‖u - circleMap 0 (ε / ‖α‖) (θ + -Complex.arg α)‖) =
      (ε / ‖α‖)⁻¹ * ‖u - circleMap 0 (ε / ‖α‖) (θ + -Complex.arg α)‖ := by
    field_simp
  rw [e1, Real.log_div hε.ne' hn.ne']
  ring

lemma kerB_scale {ε : ℝ} (hε : 0 < ε) {α : ℂ} (hα : α ≠ 0) (u : ℂ) :
    kerB ε (α * u) = Real.log ‖α‖ + kerB (ε / ‖α‖) u := by
  have hint : IntervalIntegrable
      (fun θ => kerK (ε / ‖α‖) (u - circleMap 0 (ε / ‖α‖) (θ + -Complex.arg α)))
      volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    exact (continuous_kerK _).comp (by unfold circleMap; fun_prop)
  have hπ : (2 * π) ≠ 0 := by positivity
  unfold kerB
  rw [circleAverage_eq_integral_add (-Complex.arg α) (f := fun v => kerK (ε / ‖α‖) (u - v))
    (c := 0) (R := ε / ‖α‖), circleAverage_def]
  simp only [smul_eq_mul]
  simp_rw [kerK_scale hε hα u]
  rw [intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero, mul_add, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

/-! ## 5. Segment level -/

lemma iter_integral_split {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G)) {H K : ℝ → ℝ}
    (hH : Continuous H) (hK : Continuous K) :
    ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1, (G s s' + H s + K s') =
      (∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1, G s s') + (∫ s in (0 : ℝ)..1, H s) +
        ∫ s' in (0 : ℝ)..1, K s' := by
  have hGs : ∀ s, Continuous (G s) := fun s =>
    hG.comp (continuous_const.prodMk continuous_id : Continuous fun s' : ℝ => (s, s'))
  have hin : ∀ s, ∫ s' in (0 : ℝ)..1, (G s s' + H s + K s') =
      (∫ s' in (0 : ℝ)..1, G s s') + H s + ∫ s' in (0 : ℝ)..1, K s' := by
    intro s
    rw [intervalIntegral.integral_add (((hGs s).intervalIntegrable _ _).add intervalIntegrable_const)
        (hK.intervalIntegrable _ _),
      intervalIntegral.integral_add ((hGs s).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  simp_rw [hin]
  have hcont : Continuous fun s => ∫ s' in (0 : ℝ)..1, G s s' :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 1
  rw [intervalIntegral.integral_add ((hcont.intervalIntegrable _ _).add (hH.intervalIntegrable _ _))
      intervalIntegrable_const,
    intervalIntegral.integral_add (hcont.intervalIntegrable _ _) (hH.intervalIntegrable _ _),
    intervalIntegral.integral_const]
  simp

/-- Two-point part of `segCircCov`. -/
def segS (ε : ℝ) (a b a' b' : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1,
    kerB ε ((a' + (s' : ℂ) * (b' - a')) - (a + (s : ℂ) * (b - a)))

/-- One-point part of `segCircCov`. -/
def segA (ε : ℝ) (a b : ℂ) : ℝ := ∫ s in (0 : ℝ)..1, kerA ε (a + (s : ℂ) * (b - a))

lemma segCircCov_eq {ε : ℝ} (hε : 0 < ε) (a b a' b' : ℂ) :
    segCircCov ε a b a' b' = -segS ε a b a' b' + segA ε a b + segA ε a' b' := by
  have h := iter_integral_split
    (G := fun s s' => -kerB ε ((a' + (s' : ℂ) * (b' - a')) - (a + (s : ℂ) * (b - a))))
    (H := fun s => kerA ε (a + (s : ℂ) * (b - a)))
    (K := fun s' => kerA ε (a' + (s' : ℂ) * (b' - a')))
    ((continuous_kerB ε).comp (by fun_prop :
      Continuous fun q : ℝ × ℝ => (a' + (q.2 : ℂ) * (b' - a')) - (a + (q.1 : ℂ) * (b - a)))).neg
    ((continuous_kerA ε).comp (by fun_prop))
    ((continuous_kerA ε).comp (by fun_prop))
  simp only [segCircCov, gffCircleCov_eq hε]
  rw [h]
  simp only [intervalIntegral.integral_neg, segS, segA]

lemma segS_simMap {ε : ℝ} (hε : 0 < ε) {α : ℂ} (hα : α ≠ 0) (β a b a' b' : ℂ) :
    segS ε (simMap (α, β) a) (simMap (α, β) b) (simMap (α, β) a') (simMap (α, β) b') =
      segS (ε / ‖α‖) a b a' b' + Real.log ‖α‖ := by
  have hpt : ∀ s s' : ℝ,
      kerB ε ((simMap (α, β) a' + (s' : ℂ) * (simMap (α, β) b' - simMap (α, β) a')) -
        (simMap (α, β) a + (s : ℂ) * (simMap (α, β) b - simMap (α, β) a))) =
      kerB (ε / ‖α‖) ((a' + (s' : ℂ) * (b' - a')) - (a + (s : ℂ) * (b - a))) +
        Real.log ‖α‖ + (fun _ : ℝ => (0 : ℝ)) s' := by
    intro s s'
    have e : (simMap (α, β) a' + (s' : ℂ) * (simMap (α, β) b' - simMap (α, β) a')) -
        (simMap (α, β) a + (s : ℂ) * (simMap (α, β) b - simMap (α, β) a)) =
        α * ((a' + (s' : ℂ) * (b' - a')) - (a + (s : ℂ) * (b - a))) := by
      simp only [simMap]; ring
    rw [e, kerB_scale hε hα]; ring
  have h := iter_integral_split
    (G := fun s s' => kerB (ε / ‖α‖) ((a' + (s' : ℂ) * (b' - a')) - (a + (s : ℂ) * (b - a))))
    (H := fun _ => Real.log ‖α‖) (K := fun _ => (0 : ℝ))
    ((continuous_kerB _).comp (by fun_prop :
      Continuous fun q : ℝ × ℝ => (a' + (q.2 : ℂ) * (b' - a')) - (a + (q.1 : ℂ) * (b - a))))
    continuous_const continuous_const
  unfold segS
  simp_rw [hpt]
  rw [h]
  simp

lemma segCircCov_simMap {ε : ℝ} (hε : 0 < ε) {α : ℂ} (hα : α ≠ 0) (β a b a' b' : ℂ) :
    segCircCov ε (simMap (α, β) a) (simMap (α, β) b) (simMap (α, β) a') (simMap (α, β) b') =
      -segS (ε / ‖α‖) a b a' b' + (-Real.log ‖α‖ + segA ε (simMap (α, β) a) (simMap (α, β) b)) +
        segA ε (simMap (α, β) a') (simMap (α, β) b') := by
  rw [segCircCov_eq hε, segS_simMap hε hα]; ring

/-- **`circCov` half of `SIM`.**  No nondegeneracy is needed. -/
theorem similarityCov_circCov (α β : ℂ) (hα : α ≠ 0) (c c' : SegComb) (hc : c.mass = 0)
    (hc' : c'.mass = 0) (ε : ℝ) (hε : 0 < ε) :
    (c.image (simMap (α, β))).circCov ε (c'.image (simMap (α, β))) = c.circCov (ε / ‖α‖) c' := by
  have hε' : 0 < ε / ‖α‖ := div_pos hε (norm_pos_iff.2 hα)
  unfold SegComb.circCov
  rw [dsum_image]
  rw [dsum_eq_of_mass_zero c c' hc hc'
    (fun p p' => segCircCov ε (simMap (α, β) p.2.1) (simMap (α, β) p.2.2) (simMap (α, β) p'.2.1)
      (simMap (α, β) p'.2.2))
    (fun p p' => -segS (ε / ‖α‖) p.2.1 p.2.2 p'.2.1 p'.2.2)
    (fun p => -Real.log ‖α‖ + segA ε (simMap (α, β) p.2.1) (simMap (α, β) p.2.2))
    (fun p' => segA ε (simMap (α, β) p'.2.1) (simMap (α, β) p'.2.2))
    (fun p _ p' _ => by rw [segCircCov_simMap hε hα])]
  exact (dsum_eq_of_mass_zero c c' hc hc'
    (fun p p' => segCircCov (ε / ‖α‖) p.2.1 p.2.2 p'.2.1 p'.2.2)
    (fun p p' => -segS (ε / ‖α‖) p.2.1 p.2.2 p'.2.1 p'.2.2)
    (fun p => segA (ε / ‖α‖) p.2.1 p.2.2) (fun p' => segA (ε / ‖α‖) p'.2.1 p'.2.2)
    (fun p _ p' _ => by rw [segCircCov_eq hε'])).symm

end LQGDimension.SimCov

namespace LQGDimension

/-- **Node `SIM`** (`Blueprint.Draft.SimilarityCov`). -/
theorem similarityCov : Blueprint.Draft.SimilarityCov := by
  intro α β hα c c' hc hc' _ hnc'
  exact ⟨SimCov.similarityCov_logCov α β hα c c' hc hc' hnc',
    fun ε hε => SimCov.similarityCov_circCov α β hα c c' hc hc' ε hε⟩

end LQGDimension
