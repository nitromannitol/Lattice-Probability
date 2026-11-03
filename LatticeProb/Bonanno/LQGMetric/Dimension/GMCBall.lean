/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCBall at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMass
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# DZZ Lemma 2.10 at the scale of the ball: `E μ(B̄(x, ρ)) ≤ C_γ π ρ²` (task P2-GMC, WP-24)

For a QZ zero-boundary GFF `X` on `𝕍 = (0,1)²`, `μ_ω = qAreaMeasureOn γ (X ω) openSquare`:

* `lintegral_qAreaMeasureOn_le_of_cut` : `E μ(K) ≤ C_γ ∫ f` for every continuous `0 ≤ f ≤ 1`
  with compact support in `𝕍` and `f = 1` on `K`;
* `lintegral_qAreaMeasureOn_closedBall_le` : `E μ(B̄(x, ρ)) ≤ C_γ Leb(B̄(x, ρ)) = C_γ π ρ²`
  for `B̄(x, ρ) ⊆ 𝕍`.

This is the `p = 1` case of DZZ (2.?) `eq-LQG-positive-moment` (`LBM_LGDarXiv.tex` l. 690–694:
`E (ξ^{-2} M̃(B))^p ≤ C_{γ,p}` for `B` a ball of diameter `ξ`), stated for the circle-average
measure `M_γ` itself; the first-moment computation of Rhodes–Vargas arXiv:1305.6221 §2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set QuantumZipper
open scoped ENNReal

namespace LQGMetric

/-- a compact subset of `𝕍` lies at positive distance from `∂𝕍` -/
lemma exists_sqIn_of_isCompact {T : Set ℂ} (hT : IsCompact T) (hTU : T ⊆ openSquare) :
    ∃ s : ℝ, 0 < s ∧ T ⊆ sqIn s := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, empty_subset _⟩
  set m : ℂ → ℝ := fun z => min (min z.re (1 - z.re)) (min z.im (1 - z.im))
  have hm : Continuous m := by fun_prop
  obtain ⟨z₀, hz₀, hmin⟩ := hT.exists_isMinOn hne hm.continuousOn
  obtain ⟨a, b, c, d⟩ := hTU hz₀
  have hpos : 0 < m z₀ := lt_min (lt_min a (by linarith)) (lt_min c (by linarith))
  refine ⟨m z₀, hpos, fun z hz => ?_⟩
  have h := hmin hz
  simp only [mem_ofPred_eq, m] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.trans ((min_le_left _ _).trans (min_le_left _ _))
  · linarith [h.trans ((min_le_left _ _).trans (min_le_right _ _))]
  · exact h.trans ((min_le_right _ _).trans (min_le_left _ _))
  · linarith [h.trans ((min_le_right _ _).trans (min_le_right _ _))]

/-- **pointwise bound through the vague limit**, for a general cut-off -/
theorem qAreaMeasureOn_le_liminf (γ : ℝ) (x : FieldSample) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {K : Set ℂ} (hK : ∀ z ∈ K, f z = 1) :
    qAreaMeasureOn γ x openSquare K ≤
      liminf (fun k => ∫⁻ z, ENNReal.ofReal (f z) ∂(areaApprox γ x k)) atTop := by
  unfold qAreaMeasureOn
  split_ifs with h
  swap; · simp
  obtain ⟨-, hfin, hlim⟩ := h.choose_spec
  set μ := h.choose
  set S := tsupport f
  have hint : Integrable f μ := by
    have hg : Integrable (S.indicator fun _ => (1 : ℝ)) μ :=
      (integrable_indicator_iff (isClosed_tsupport f).measurableSet).mpr
        (integrableOn_const (hfin S hfc hfU).ne)
    refine hg.mono' hf.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z
    · rw [image_eq_zero_of_notMem_tsupport hz, indicator_of_notMem hz, norm_zero]
  calc μ K ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂μ := by
        set L := {z | f z = 1}
        have hL : MeasurableSet L := (isClosed_eq hf continuous_const).measurableSet
        refine (measure_mono (show K ⊆ L from hK)).trans ?_
        rw [← lintegral_indicator_one hL]
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ L
        · rw [indicator_of_mem hz, Pi.one_apply, show f z = 1 from hz, ENNReal.ofReal_one]
        · rw [indicator_of_notMem hz]; exact zero_le
    _ = ENNReal.ofReal (∫ z, f z ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)).symm
    _ = liminf (fun k => ENNReal.ofReal (∫ z, f z ∂(areaApprox γ x k))) atTop :=
        (((ENNReal.continuous_ofReal.tendsto _).comp (hlim f hf hfc hfU)).liminf_eq).symm
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun k => ofReal_integral_le_lintegral h0)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Measure ℂ → ℝ}

/-- **expected approximate mass** against a general cut-off, at scale `2^{-k} < s/2` -/
theorem lintegral_areaApprox_cut_le (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ)
    {f : ℂ → ℝ} (hf : Continuous f) {s : ℝ} (hs : 0 < s)
    (hfs : ∀ z, f z ≠ 0 → z ∈ sqIn s) {k : ℕ} (hk : radius k < s / 2) :
    ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (f z) ∂(areaApprox γ (X ω) k) ∂P ≤
      gmcConst γ * ∫⁻ z, ENNReal.ofReal (f z) := by
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (f z) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp hf.measurable
  have hD := measurable_areaDens hX γ k
  have hrw : ∀ ω, ∫⁻ z, g z ∂(areaApprox γ (X ω) k) =
      ∫⁻ z, areaDens γ (X ω) k z * g z ∂volume.restrict H :=
    fun ω => lintegral_withDensity_eq_lintegral_mul _ (hD.comp measurable_prodMk_left) hgm
  simp_rw [hrw]
  rw [lintegral_lintegral_swap ((hD.mul (hgm.comp measurable_snd)).aemeasurable)]
  calc ∫⁻ z, ∫⁻ ω, areaDens γ (X ω) k z * g z ∂P ∂volume.restrict H
      ≤ ∫⁻ z, gmcConst γ * g z ∂volume.restrict H := by
        refine lintegral_mono fun z => ?_
        rw [lintegral_mul_const _ (measurable_areaDens_left hX γ k z)]
        by_cases h0 : f z = 0
        · simp [hg, h0]
        exact mul_le_mul_left (lintegral_areaDens_le hX γ hs hk (hfs z h0)) _
    _ = gmcConst γ * ∫⁻ z, g z ∂volume.restrict H := lintegral_const_mul _ hgm
    _ ≤ gmcConst γ * ∫⁻ z, g z := mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

/-- **`E μ(K) ≤ C_γ ∫ f`** for a cut-off `f` equal to `1` on `K` -/
theorem lintegral_qAreaMeasureOn_le_of_cut (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) {K : Set ℂ} (hK : ∀ z ∈ K, f z = 1) :
    ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare K ∂P ≤ gmcConst γ * ∫⁻ z, ENNReal.ofReal (f z) := by
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc hfU
  have hfs : ∀ z, f z ≠ 0 → z ∈ sqIn s := fun z hz => hTs (subset_tsupport f hz)
  have hmeas : ∀ k, Measurable fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(areaApprox γ (X ω) k) :=
    fun k => (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.measurable)).comp
      ((measurable_areaApprox γ k).comp (measurable_field hX))
  have hr : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k in atTop, radius k < s / 2 := hr.eventually (gt_mem_nhds (by positivity))
  calc ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare K ∂P
      ≤ ∫⁻ ω, liminf (fun k => ∫⁻ z, ENNReal.ofReal (f z) ∂(areaApprox γ (X ω) k)) atTop ∂P :=
        lintegral_mono fun ω => qAreaMeasureOn_le_liminf γ (X ω) hf hfc hfU h0 h1 hK
    _ ≤ liminf (fun k => ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (f z) ∂(areaApprox γ (X ω) k) ∂P) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ _ := liminf_le_of_frequently_le' (hev.mono fun k hk =>
        lintegral_areaApprox_cut_le hX γ hf hs hfs hk).frequently

/-- the cone cut-off around `B̄(x, ρ)` of width `ε` -/
def ballCut (x : ℂ) (ρ ε : ℝ) (z : ℂ) : ℝ := min 1 (max 0 ((ρ + ε - dist z x) / ε))

lemma ballCut_ne_zero {x : ℂ} {ρ ε : ℝ} (hε : 0 < ε) {z : ℂ} (h : ballCut x ρ ε z ≠ 0) :
    z ∈ Metric.closedBall x (ρ + ε) := by
  by_contra hz
  rw [Metric.mem_closedBall, not_le] at hz
  apply h
  have : (ρ + ε - dist z x) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp only [ballCut, max_eq_left this, min_eq_right zero_le_one]

/-- **DZZ Lemma 2.10 at the scale of the ball (`p = 1`)** : `E μ(B̄(x, ρ)) ≤ C_γ π ρ²` -/
theorem lintegral_qAreaMeasureOn_closedBall_le (hX : IsZeroBoundaryGFFOn openSquare X P)
    (γ : ℝ) {x : ℂ} {ρ : ℝ} (hB : Metric.closedBall x ρ ⊆ openSquare) :
    ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.closedBall x ρ) ∂P ≤
      gmcConst γ * volume (Metric.closedBall x ρ) := by
  rcases lt_or_ge ρ 0 with hρ | hρ
  · rw [Metric.closedBall_eq_empty.mpr hρ]; simp
  obtain ⟨ε₀, hε₀, hsub⟩ := (isCompact_closedBall x ρ).exists_cthickening_subset_open
    isOpen_openSquare hB
  rw [cthickening_closedBall hε₀.le hρ] at hsub
  -- the bound for each `ε = ε₀/(n+1)`
  set ε : ℕ → ℝ := fun n => ε₀ / (n + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεle : ∀ n, ε n ≤ ε₀ := fun n => div_le_self hε₀.le (by linarith [n.cast_nonneg (α := ℝ)])
  have hbound : ∀ n, ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.closedBall x ρ) ∂P ≤
      gmcConst γ * volume (Metric.closedBall x (ρ + ε n)) := by
    intro n
    have he := hεpos n
    have hf : Continuous (ballCut x ρ (ε n)) := by unfold ballCut; fun_prop
    have hsupp : tsupport (ballCut x ρ (ε n)) ⊆ Metric.closedBall x (ρ + ε n) :=
      closure_minimal (fun z hz => ballCut_ne_zero he hz) Metric.isClosed_closedBall
    have hsubU : Metric.closedBall x (ρ + ε n) ⊆ openSquare :=
      (Metric.closedBall_subset_closedBall (show ρ + ε n ≤ ε₀ + ρ by linarith [hεle n])).trans
        hsub
    refine (lintegral_qAreaMeasureOn_le_of_cut hX γ hf
      ((isCompact_closedBall x _).of_isClosed_subset (isClosed_tsupport _) hsupp)
      (hsupp.trans hsubU) (fun z => le_min zero_le_one (le_max_left _ _))
      (fun z => min_le_left _ _) (K := Metric.closedBall x ρ) ?_).trans ?_
    · intro z hz
      rw [Metric.mem_closedBall] at hz
      have : 1 ≤ (ρ + ε n - dist z x) / ε n := by rw [le_div_iff₀ he]; linarith
      simp only [ballCut, max_eq_right (zero_le_one.trans this), min_eq_left this]
    · refine mul_le_mul_right ?_ _
      calc ∫⁻ z, ENNReal.ofReal (ballCut x ρ (ε n) z)
          ≤ ∫⁻ z, (Metric.closedBall x (ρ + ε n)).indicator 1 z := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ Metric.closedBall x (ρ + ε n)
            · rw [indicator_of_mem hz, Pi.one_apply, ← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
            · have : ballCut x ρ (ε n) z = 0 := by
                by_contra h0; exact hz (ballCut_ne_zero he h0)
              rw [this, ENNReal.ofReal_zero]; exact zero_le
        _ = volume (Metric.closedBall x (ρ + ε n)) :=
            lintegral_indicator_one Metric.isClosed_closedBall.measurableSet
  -- continuity from above
  have hanti : Antitone fun n => Metric.closedBall x (ρ + ε n) := by
    intro m n hmn
    refine Metric.closedBall_subset_closedBall (add_le_add_right ?_ _)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact div_le_div_of_nonneg_left hε₀.le (by positivity) (by linarith)
  have hinter : ⋂ n, Metric.closedBall x (ρ + ε n) = Metric.closedBall x ρ := by
    ext y
    simp only [mem_iInter, Metric.mem_closedBall]
    refine ⟨fun h => ?_, fun h n => by linarith [hεpos n]⟩
    by_contra hlt; push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_gt (ε₀ / (dist y x - ρ))
    have hd : 0 < dist y x - ρ := by linarith
    have h1 := h n
    have h2 : ε n < dist y x - ρ := by
      rw [hεdef]; dsimp only
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hd] at hn; nlinarith
    linarith
  have htend : Tendsto (fun n => volume (Metric.closedBall x (ρ + ε n))) atTop
      (𝓝 (volume (Metric.closedBall x ρ))) := by
    rw [← hinter]
    exact tendsto_measure_iInter_atTop (fun n => measurableSet_closedBall.nullMeasurableSet)
      hanti ⟨0, measure_closedBall_lt_top.ne⟩
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul htend (Or.inr (gmcConst_lt_top γ).ne)) hbound

/-- the same for open balls: `E μ(B(x, ρ)) ≤ C_γ π ρ²` -/
theorem lintegral_qAreaMeasureOn_ball_le (hX : IsZeroBoundaryGFFOn openSquare X P)
    (γ : ℝ) {x : ℂ} {ρ : ℝ} (hB : Metric.closedBall x ρ ⊆ openSquare) :
    ∫⁻ ω, qAreaMeasureOn γ (X ω) openSquare (Metric.ball x ρ) ∂P ≤
      gmcConst γ * (ENNReal.ofReal ρ ^ 2 * NNReal.pi) := by
  rw [← Complex.volume_closedBall]
  exact (lintegral_mono fun ω => measure_mono Metric.ball_subset_closedBall).trans
    (lintegral_qAreaMeasureOn_closedBall_le hX γ hB)

end LQGMetric
