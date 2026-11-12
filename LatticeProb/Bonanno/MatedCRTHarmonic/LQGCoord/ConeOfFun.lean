/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ConeOfFun at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPArea
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3

/-!
The γ-quantum cone field is `coneField X A = X − ofFunC (radialAvg X) + ofFunC
(A(−log|·|))` (`CellScaling.coneField`, `lateralPart`), i.e. a whole-plane GFF plus two functions that
are continuous off the cone point `0` and locally integrable. For such fields and circles avoiding
`0`:

* `tendsto_mollAvgS_ofCont`: the scale-`s` mollified circle averages of a continuous function
  converge to its classical circle average (LQGMetric's `tendsto_mollAvg_ofCont` along the
  continuum of scales);
* `tendsto_mollAvgS_ofFunC`: the same for `ofFunC g`, `g` locally integrable and continuous near
  the circle (locality of `ofFunC`, MoTPort's `exists_continuous_eqOn_thickening`);
* `hasScaleCircleAvgs_cone`: `X − ofFunC g₁ + ofFunC g₂` has circle averages along every
  mollifier scale whenever `X` has, and its circle averages are
  `X_ρ(w) − ⨍ g₁ + ⨍ g₂` on circles avoiding `0` (`circleAvg_cone`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling

/-! ## Pairings with the scale-`s` mollifiers -/

lemma ofFunC_apply_li {g : ℂ → ℝ} (hg : LocallyIntegrable g volume) (φ : TestC) :
    ofFunC g φ = ∫ x, φ x * g x := by
  rw [ofFunC, Distribution.ofFun_apply (hg.locallyIntegrableOn _)]
  rfl

lemma integrable_bumpS_mul {s : ℝ} (x : ℂ) {g : ℂ → ℝ} (hg : LocallyIntegrable g volume) :
    Integrable fun y => bumpS s x y * g y := by
  have h := (hg.integrableOn_isCompact (isCompact_closedBall x |s|)).mul_continuousOn
    (bumpS s x).continuous.continuousOn (isCompact_closedBall x |s|)
  refine (h.integrable_of_forall_notMem_eq_zero fun y hy => ?_).congr
    (Eventually.of_forall fun y => mul_comm _ _)
  rw [bumpS_eq_zero s (le_of_lt (by simpa using hy)), mul_zero]

/-- `|∫ ψ_{s,x} f − f(x)| ≤ sup_{B̄(x,s)} |f − f(x)|` -/
lemma abs_ofCont_bumpS_sub_le (f : C(ℂ, ℝ)) {s : ℝ} (hs : 0 < s) (x : ℂ) {η : ℝ}
    (hη : ∀ y ∈ closedBall x s, |f y - f x| ≤ η) :
    |ofCont f (bumpS s x) - f x| ≤ η := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη x (mem_closedBall_self hs.le))
  rw [ofCont_apply]
  have hi : Integrable fun y => bumpS s x y * f y :=
    integrable_bumpS_mul x f.continuous.locallyIntegrable
  have e : (∫ y, bumpS s x y * f y) - f x = ∫ y, bumpS s x y * (f y - f x) := by
    simp_rw [mul_sub]
    rw [integral_sub hi ((integrable_testC _).mul_const _), integral_mul_const,
      integral_bumpS hs, one_mul]
  rw [e, ← Real.norm_eq_abs]
  have hb : ∀ y, ‖bumpS s x y * (f y - f x)‖ ≤ bumpS s x y * η := by
    intro y
    rw [norm_mul, Real.norm_of_nonneg (bumpS_nonneg s x y)]
    by_cases hy : dist y x < s
    · exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hη y hy.le)
        (bumpS_nonneg s x y)
    · rw [bumpS_eq_zero s (by rw [abs_of_pos hs]; exact not_lt.mp hy), zero_mul, zero_mul]
  refine (norm_integral_le_of_norm_le ((integrable_testC _).mul_const _)
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_bumpS hs, one_mul]

lemma tendsto_ofCont_bumpS (f : C(ℂ, ℝ)) (x : ℂ) :
    Tendsto (fun s => ofCont f (bumpS s x)) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.1 f.continuous x (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs hsd => ?_⟩
  have hs0 : (0 : ℝ) < s := hs
  rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_ofCont_bumpS_sub_le f hs0 x fun y hy => ?_) (half_lt_self hε)
  have := hfδ y (lt_of_le_of_lt (mem_closedBall.1 hy) hsd)
  rw [Real.dist_eq] at this
  exact this.le

/-- the mollified field of a distribution at a fixed scale is continuous -/
lemma continuous_pair_bumpS (T : DistC) {s : ℝ} (hs : 0 < s) :
    Continuous fun x => T (bumpS s x) := by
  have := (continuous_pair_bumpS_exp T).comp
    (continuous_const.prodMk continuous_id : Continuous fun x : ℂ => (Real.log s, x))
  simpa [Function.comp_def, Real.exp_log hs] using this

/-- **the scale-`s` mollified circle averages of a continuous function converge** -/
theorem tendsto_mollAvgS_ofCont (f : C(ℂ, ℝ)) (w : ℂ) (ρ : ℝ) :
    Tendsto (fun s => mollAvgS (ofCont f) s w ρ) (𝓝[>] 0) (𝓝 (Real.circleAverage f w ρ)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall w (|ρ| + 1)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  have hM' : ∀ θ : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 →
      |ofCont f (bumpS s (circleMap w ρ θ))| ≤ 3 * M := by
    intro θ s hs hs1
    set x := circleMap w ρ θ
    have h2 : dist x w = |ρ| := by simp [x, dist_eq_norm, circleMap_sub_center]
    have hb : ∀ y ∈ closedBall x 1, |f y| ≤ M := fun y hy => by
      have hy1 : y ∈ closedBall w (|ρ| + 1) := by
        rw [mem_closedBall] at hy ⊢; linarith [dist_triangle y x w]
      simpa [Real.norm_eq_abs] using hM y hy1
    have hx := hb x (mem_closedBall_self zero_le_one)
    have h0 := abs_ofCont_bumpS_sub_le f hs x (η := 2 * M) fun y hy => by
      have := hb y (closedBall_subset_closedBall hs1 hy)
      calc |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
        _ ≤ 2 * M := by linarith
    calc |ofCont f (bumpS s x)| ≤ |ofCont f (bumpS s x) - f x| + |f x| := by
          have := abs_sub_abs_le_abs_sub (ofCont f (bumpS s x)) (f x); linarith
      _ ≤ 3 * M := by linarith
  simp only [mollAvgS, Real.circleAverage_def]
  refine Tendsto.const_smul ?_ _
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 3 * M) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((continuous_pair_bumpS (ofCont f) hs).comp
      (continuous_circleMap w ρ)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
    exact Eventually.of_forall fun θ _ => by rw [Real.norm_eq_abs]; exact hM' θ s hs.1 hs.2.le
  · exact Eventually.of_forall fun θ _ => tendsto_ofCont_bumpS f _

/-- **the scale-`s` mollified circle averages of `ofFunC g`** on a circle inside an open set where
`g` is continuous converge to the circle average of `g` -/
theorem tendsto_mollAvgS_ofFunC {g : ℂ → ℝ} (hgl : LocallyIntegrable g volume) {U : Set ℂ}
    (hU : IsOpen U) (hg : ContinuousOn g U) {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hwU : sphere w ρ ⊆ U) :
    Tendsto (fun s => mollAvgS (ofFunC g) s w ρ) (𝓝[>] 0) (𝓝 (Real.circleAverage g w ρ)) := by
  obtain ⟨δ, hδ, G, hG⟩ := MoTPort.ConeArea3.exists_continuous_eqOn_thickening hU hg
    (isCompact_sphere w ρ) hwU
  have habs : |ρ| = ρ := abs_of_pos hρ
  have hc : Real.circleAverage (⇑G) w ρ = Real.circleAverage g w ρ :=
    Real.circleAverage_congr_sphere fun x hx => by
      rw [habs] at hx; exact hG (self_subset_thickening hδ _ hx)
  rw [← hc]
  refine (tendsto_mollAvgS_ofCont G w ρ).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
  simp only [mollAvgS]
  apply Real.circleAverage_congr_sphere
  intro x hx
  rw [habs] at hx
  show ofCont G (bumpS s x) = ofFunC g (bumpS s x)
  rw [ofCont_apply, ofFunC_apply_li hgl]
  congr 1; funext y
  by_cases hy : dist y x < s
  · rw [hG (mem_thickening_iff.2 ⟨x, hx, lt_trans hy hs.2⟩)]
  · rw [bumpS_eq_zero s (by rw [abs_of_pos hs.1]; exact not_lt.mp hy), zero_mul, zero_mul]

/-! ## The cone-type fields -/

lemma mollAvgS_cone (X : DistC) (g₁ g₂ : ℂ → ℝ) (s : ℝ) (w : ℂ) (ρ : ℝ) :
    mollAvgS (X - ofFunC g₁ + ofFunC g₂) s w ρ =
      mollAvgS X s w ρ - mollAvgS (ofFunC g₁) s w ρ + mollAvgS (ofFunC g₂) s w ρ := by
  simp only [mollAvgS_eq, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]

/-- a continuum limit of the mollified circle averages is the circle average -/
lemma circleAvg_eq_of_tendsto_mollAvgS {T : DistC} {ρ : ℝ} {w : ℂ} {a : ℝ}
    (h : Tendsto (fun s => mollAvgS T s w ρ) (𝓝[>] 0) (𝓝 a)) : circleAvg T ρ w = a := by
  apply circleAvg_eq_of_tendsto
  have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity))
  exact (h.comp ht).congr fun n => mollAvgS_dyadic T n w ρ

lemma sphere_subset_compl_zero {w : ℂ} {ρ : ℝ} (hw : ‖w‖ ≠ ρ) : sphere w ρ ⊆ {0}ᶜ := by
  intro x hx h0
  rw [mem_singleton_iff] at h0
  subst h0
  rw [mem_sphere, dist_eq_norm, zero_sub, norm_neg] at hx
  exact hw hx

/-- **the mollified circle averages of the cone-type field** on circles avoiding `0` -/
theorem tendsto_mollAvgS_cone {X : DistC} {g₁ g₂ : ℂ → ℝ} (hl₁ : LocallyIntegrable g₁ volume)
    (hl₂ : LocallyIntegrable g₂ volume) (hc₁ : ContinuousOn g₁ {0}ᶜ) (hc₂ : ContinuousOn g₂ {0}ᶜ)
    {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hw : ‖w‖ ≠ ρ)
    (hX : Tendsto (fun s => mollAvgS X s w ρ) (𝓝[>] 0) (𝓝 (circleAvg X ρ w))) :
    Tendsto (fun s => mollAvgS (X - ofFunC g₁ + ofFunC g₂) s w ρ) (𝓝[>] 0)
      (𝓝 (circleAvg X ρ w - Real.circleAverage g₁ w ρ + Real.circleAverage g₂ w ρ)) := by
  have hU : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  simp_rw [mollAvgS_cone]
  exact (hX.sub (tendsto_mollAvgS_ofFunC hl₁ hU hc₁ hρ (sphere_subset_compl_zero hw))).add
    (tendsto_mollAvgS_ofFunC hl₂ hU hc₂ hρ (sphere_subset_compl_zero hw))

theorem circleAvg_cone {X : DistC} {g₁ g₂ : ℂ → ℝ} (hl₁ : LocallyIntegrable g₁ volume)
    (hl₂ : LocallyIntegrable g₂ volume) (hc₁ : ContinuousOn g₁ {0}ᶜ) (hc₂ : ContinuousOn g₂ {0}ᶜ)
    {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hw : ‖w‖ ≠ ρ)
    (hX : Tendsto (fun s => mollAvgS X s w ρ) (𝓝[>] 0) (𝓝 (circleAvg X ρ w))) :
    circleAvg (X - ofFunC g₁ + ofFunC g₂) ρ w =
      circleAvg X ρ w - Real.circleAverage g₁ w ρ + Real.circleAverage g₂ w ρ :=
  circleAvg_eq_of_tendsto_mollAvgS (tendsto_mollAvgS_cone hl₁ hl₂ hc₁ hc₂ hρ hw hX)

lemma ae_norm_ne (ρ : ℝ) : ∀ᵐ w : ℂ, ‖w‖ ≠ ρ := by
  have h : volume (sphere (0 : ℂ) ρ) = 0 := Measure.addHaar_sphere volume 0 ρ
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) h
  have hw' : ‖w‖ = ρ := not_not.1 hw
  rw [mem_sphere, dist_zero_right]; exact hw'

/-- **`HasScaleCircleAvgs` for the cone-type field** -/
theorem hasScaleCircleAvgs_cone {X : DistC} (hX : HasScaleCircleAvgs X) {g₁ g₂ : ℂ → ℝ}
    (hl₁ : LocallyIntegrable g₁ volume) (hl₂ : LocallyIntegrable g₂ volume)
    (hc₁ : ContinuousOn g₁ {0}ᶜ) (hc₂ : ContinuousOn g₂ {0}ᶜ) :
    HasScaleCircleAvgs (X - ofFunC g₁ + ofFunC g₂) := by
  intro ρ hρ
  filter_upwards [hX ρ hρ, ae_norm_ne ρ] with w hw hne
  rw [circleAvg_cone hl₁ hl₂ hc₁ hc₂ hρ hne hw]
  exact tendsto_mollAvgS_cone hl₁ hl₂ hc₁ hc₂ hρ hne hw

end MatedCRTHarmonic.LQGCoord
