/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Ver at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_eq_lintegral_rpow_enorm_toReal and eLpNorm_one_eq_lintegral_enorm take the measurability hypothesis, now supplied. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Circ
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentAbs

/-!
# Identification for the white-noise field, part 2: `𝓖_∞`-measurable versions (P2-GMCID4, R1)

* `tendsto_norm_measKerL2_fine`: `‖K^{(0,4^{-n}]}_μ‖ → 0` (dominated convergence in `L²`);
* **`exists_iSup_version`** (R1): `W(K_μ)` has a `⨆ n, 𝓖_n`-measurable version. The truncations
  `W(K^{(4^{-n},∞)}_μ)` are `𝓖_n`-measurable and converge to `W(K_μ)` in `L¹`, so
  `W(K_μ) = E[W(K_μ) | 𝓖_∞]` (`GMCIdentAbs.ae_eq_condExp_of_tendsto_L1`);
* `wnFieldVer`: a field sample whose coordinates are `𝓖_∞`-measurable and which agrees a.s. with
  `wnField W` on the countable set `dyCircles` of dyadic circles (the only coordinates the
  circle-average approximations read), so that `areaApprox γ (wnFieldVer ω) k =
  areaApprox γ (wnField W ω) k` for all `k`, a.s. (`ae_areaApprox_wnFieldVer`).

This replaces the hypothesis `hXm` of `GMCIdent.ae_tendsto_wnGMC` (`𝓖_∞`-measurability of the
field), used there only for Lévy's upward theorem (Berestycki arXiv:1506.09113, §4, l. 695–700).
Own routine measure-theoretic argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent4

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3

variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-- the cut-offs `4^{-n}` -/
abbrev cutoff (n : ℕ) : ℝ := ((2 : ℝ)⁻¹ ^ n) ^ 2

lemma cutoff_pos (n : ℕ) : 0 < cutoff n := by positivity

lemma tendsto_cutoff : Tendsto cutoff atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 := h.pow 2
  rwa [zero_pow two_ne_zero] at h2

lemma measKer_le_of_subset (A : Set ℂ) {I J : Set ℝ} (hIJ : I ⊆ J) (μ : Measure ℂ) (p : ℝ × ℂ) :
    measKer A I μ p ≤ measKer A J μ p := by
  unfold measKer
  by_cases hp : p.1 ∈ I
  · have hJ : p.1 ∈ J := hIJ hp
    simp [wndKernel, hp, hJ]
  · have : (fun y => wndKernel A I y p) = fun _ => 0 := by
      funext y; simp [wndKernel, hp]
    rw [this, integral_zero]
    exact integral_nonneg fun _ => wndKernel_nonneg _ _ _ _

lemma memLp_measKer_of_subset {A : Set ℂ} (hA : IsOpen A) {I J : Set ℝ} (hI : MeasurableSet I)
    (hIJ : I ⊆ J) (μ : Measure ℂ) [IsFiniteMeasure μ] (h : MemLp (measKer A J μ) 2 volume) :
    MemLp (measKer A I μ) 2 volume :=
  h.mono (measurable_measKer hA hI μ).aestronglyMeasurable (Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (measKer_nonneg _ _ _ _),
      abs_of_nonneg (measKer_nonneg _ _ _ _)]
    exact measKer_le_of_subset A hIJ μ p)

/-- the fine part of the kernel vanishes in `L²` as the cut-off goes to `0` -/
lemma tendsto_norm_measKerL2_fine {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : MemLp (measKer openSquare (Ioi 0) μ) 2 volume) :
    Tendsto (fun n => ‖measKerL2 openSquare (Ioc 0 (cutoff n)) μ‖) atTop (𝓝 0) := by
  have hm : ∀ n, MemLp (measKer openSquare (Ioc 0 (cutoff n)) μ) 2 volume := fun n =>
    memLp_measKer_of_subset isOpen_openSquare measurableSet_Ioc Ioc_subset_Ioi_self μ hμ
  have e : ∀ n, ‖measKerL2 openSquare (Ioc 0 (cutoff n)) μ‖ =
      (eLpNorm (measKer openSquare (Ioc 0 (cutoff n)) μ) 2 volume).toReal := fun n => by
    rw [measKerL2, dite_eq_left_of_eq_true (eq_true (hm n)), Lp.norm_toLp]
  simp_rw [e]
  rw [← ENNReal.toReal_zero]
  refine (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ?_
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero : (2 : ℝ≥0∞) ≠ 0)
    ENNReal.ofNat_ne_top (measurable_measKer isOpen_openSquare measurableSet_Ioc μ).aestronglyMeasurable]
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (two_ne_zero : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top
    hμ.eLpNorm_lt_top
  have hL : Tendsto (fun n => ∫⁻ p : ℝ × ℂ, ‖measKer openSquare (Ioc 0 (cutoff n)) μ p‖ₑ ^
      (2 : ℝ≥0∞).toReal) atTop (𝓝 (∫⁻ _p : ℝ × ℂ, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_of_dominated_convergence _ (fun n => ?_) (fun n => ?_) hfin.ne ?_
    · exact ((measurable_measKer isOpen_openSquare measurableSet_Ioc μ).enorm).pow_const _
    · refine Eventually.of_forall fun p => ?_
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (measKer_nonneg _ _ _ _), abs_of_nonneg (measKer_nonneg _ _ _ _)]
      exact ENNReal.ofReal_le_ofReal (measKer_le_of_subset _ Ioc_subset_Ioi_self μ p)
    · refine Eventually.of_forall fun p => tendsto_const_nhds.congr' ?_
      have hev : ∀ᶠ n in atTop, p.1 ∉ Ioc 0 (cutoff n) := by
        by_cases hp : 0 < p.1
        · filter_upwards [tendsto_cutoff.eventually (gt_mem_nhds hp)] with n hn h
          exact absurd h.2 (not_le.2 hn)
        · exact Eventually.of_forall fun n h => hp h.1
      filter_upwards [hev] with n hn
      have : (fun y => wndKernel openSquare (Ioc 0 (cutoff n)) y p) = fun _ => 0 := by
        funext y; simp [wndKernel, hn]
      simp only [measKer, this, integral_zero, enorm_zero]
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [lintegral_zero] at hL
  have h2 := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
  exact h2.comp hL

/-- `E|W g| ≤ ‖g‖` -/
lemma eLpNorm_one_wn_le (hW : IsWhiteNoise P' W) (g : WNSpace) :
    eLpNorm (W g) 1 P' ≤ ENNReal.ofReal ‖g‖ := by
  have hP := hW.isProbabilityMeasure
  have hL := hW.hasLaw_single g
  have hi : Integrable (W g) P' :=
    memLp_one_iff_integrable.1 (hL.memLp (memLp_id_gaussianReal' 1 (by simp)))
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  refine ENNReal.ofReal_le_ofReal ((integral_abs_le_sqrt_of_hasLaw hL).trans (le_of_eq ?_))
  rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma integrable_wn (hW : IsWhiteNoise P' W) (g : WNSpace) : Integrable (W g) P' :=
  have := hW.isProbabilityMeasure
  memLp_one_iff_integrable.1 ((hW.hasLaw_single g).memLp (memLp_id_gaussianReal' 1 (by simp)))

/-- **(R1)** `W(K_μ)` has a `𝓖_∞`-measurable version -/
theorem exists_iSup_version (hW : IsWhiteNoise P' W) {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : MemLp (measKer openSquare (Ioi 0) μ) 2 volume) :
    ∃ Y : Ω' → ℝ, Measurable[⨆ n, wnFil hW n] Y ∧
      Y =ᵐ[P'] W (measKerL2 openSquare (Ioi 0) μ) := by
  have hP := hW.isProbabilityMeasure
  have hm : (⨆ n, wnFil hW n : MeasurableSpace Ω') ≤ mΩ' := iSup_le fun n => (wnFil hW).le n
  set K := measKerL2 openSquare (Ioi 0) μ
  set g : ℕ → WNSpace := fun n => measKerL2 openSquare (Ioi (cutoff n)) μ
  set Y : ℕ → Ω' → ℝ := fun n => W (g n)
  have hYm : ∀ n, StronglyMeasurable[⨆ n, wnFil hW n] (Y n) := fun n => by
    have h : Measurable[wnFil hW n] (Y n) :=
      measurable_wnSigma (supportedIn_measKerL2 _ measurableSet_Ioi μ)
    exact (h.mono (le_iSup (fun n => wnFil hW n) n) le_rfl).stronglyMeasurable
  have hsplit : ∀ n, K = measKerL2 openSquare (Ioc 0 (cutoff n)) μ + g n := fun n =>
    measKerL2_split isOpen_openSquare (cutoff_pos n) μ
      (memLp_measKer_of_subset isOpen_openSquare measurableSet_Ioc Ioc_subset_Ioi_self μ hμ)
      (memLp_measKer_of_subset isOpen_openSquare measurableSet_Ioi
        (Ioi_subset_Ioi (cutoff_pos n).le) μ hμ)
  have hbd : ∀ n, eLpNorm (Y n - W K) 1 P' ≤
      ENNReal.ofReal ‖measKerL2 openSquare (Ioc 0 (cutoff n)) μ‖ := by
    intro n
    have he : Y n - W K =ᵐ[P'] -W (measKerL2 openSquare (Ioc 0 (cutoff n)) μ) := by
      have := hW.add_ae (measKerL2 openSquare (Ioc 0 (cutoff n)) μ) (g n)
      rw [← hsplit n] at this
      filter_upwards [this] with ω h
      simp only [Pi.sub_apply, Pi.neg_apply, Y, h]; ring
    rw [eLpNorm_congr_ae he, eLpNorm_neg]
    exact eLpNorm_one_wn_le hW _
  have hY : Tendsto (fun n => eLpNorm (Y n - W K) 1 P') atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal ‖measKerL2 openSquare (Ioc 0 (cutoff n)) μ‖)
        atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_norm_measKerL2_fine hμ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hbd
  have hc : ∀ n, P'[W (g n) | ⨆ n, wnFil hW n] = W (g n) := fun n =>
    condExp_of_stronglyMeasurable hm (hYm n) (integrable_wn hW _)
  have h := ae_eq_condExp_of_tendsto_L1 (m := ⨆ n, wnFil hW n) (fun n => integrable_wn hW (g n))
    (integrable_wn hW K) hY (hW.measurable K).aestronglyMeasurable
    (by simp_rw [hc]; exact hY)
  exact ⟨P'[W K | ⨆ n, wnFil hW n], stronglyMeasurable_condExp.measurable, h.symm⟩

/-! ## a version of the white-noise field with `𝓖_∞`-measurable coordinates -/

/-- the dyadic circles `∂B(d, 2^{-k})`, `d ∈ 2^{-n}ℤ²`: the coordinates read by `avgReg` -/
def dyCircles : Set (Measure ℂ) :=
  range fun q : ℕ × ℕ × ℤ × ℤ =>
    foldedCircle ⟨(q.2.2.1 : ℝ) / 2 ^ q.1, (q.2.2.2 : ℝ) / 2 ^ q.1⟩ (radius q.2.1)

lemma countable_dyCircles : dyCircles.Countable := countable_range _

lemma foldedCircle_mem_dyCircles (n k : ℕ) (z : ℂ) :
    foldedCircle (dyadicRoundC n z) (radius k) ∈ dyCircles :=
  ⟨(n, k, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩

lemma avgReg_congr_dy {x x' : FieldSample} (h : ∀ μ ∈ dyCircles, x μ = x' μ) (k : ℕ) (z : ℂ) :
    avgReg x k z = avgReg x' k z := by
  have e : (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) =
      fun n => x' (foldedCircle (dyadicRoundC n z) (radius k)) :=
    funext fun n => h _ (foldedCircle_mem_dyCircles n k z)
  unfold avgReg
  rw [e]

lemma areaApprox_congr_dy {x x' : FieldSample} (h : ∀ μ ∈ dyCircles, x μ = x' μ) (γ : ℝ)
    (k : ℕ) : areaApprox γ x k = areaApprox γ x' k := by
  unfold areaApprox
  simp_rw [avgReg_congr_dy h]

/-- every coordinate of the white-noise field has a `𝓖_∞`-measurable version -/
lemma exists_version_wnField (hW : IsWhiteNoise P' W) (μ : Measure ℂ) :
    ∃ Y : Ω' → ℝ, Measurable[⨆ n, wnFil hW n] Y ∧ Y =ᵐ[P'] fun ω => wnField W ω μ := by
  by_cases h : ∃ j : CircIdx, foldedCircle j.1.1 j.1.2 = μ
  · obtain ⟨Y, hY, hYe⟩ := exists_iSup_version hW (μ := circleUnif h.choose.1.1 h.choose.1.2)
      (memLp_measKer_circle h.choose.2.1 h.choose.2.2)
    refine ⟨fun ω => Real.sqrt Real.pi * Y ω, hY.const_mul _, ?_⟩
    filter_upwards [hYe] with ω hω
    simp only [GMCIdent3.wnField, circExt, dif_pos h, wnCircVec]
    rw [hω]
  · exact ⟨fun _ => 0, measurable_const, Eventually.of_forall fun ω => by
      simp only [GMCIdent3.wnField, circExt, dif_neg h]⟩

/-- a version of the white-noise field with `𝓖_∞`-measurable coordinates -/
def wnFieldVer (hW : IsWhiteNoise P' W) (ω : Ω') : FieldSample := fun μ =>
  (exists_version_wnField hW μ).choose ω

lemma measurable_wnFieldVer (hW : IsWhiteNoise P' W) (μ : Measure ℂ) :
    Measurable[⨆ n, wnFil hW n] fun ω => wnFieldVer hW ω μ :=
  (exists_version_wnField hW μ).choose_spec.1

/-- a.s. the version has the same circle-average approximations as the white-noise field -/
lemma ae_areaApprox_wnFieldVer (hW : IsWhiteNoise P' W) :
    ∀ᵐ ω ∂P', ∀ γ k, areaApprox γ (wnFieldVer hW ω) k = areaApprox γ (wnField W ω) k := by
  have : Countable dyCircles := countable_dyCircles.to_subtype
  have h : ∀ᵐ ω ∂P', ∀ μ : dyCircles, wnFieldVer hW ω μ = wnField W ω μ :=
    ae_all_iff.2 fun μ => (exists_version_wnField hW μ).choose_spec.2
  filter_upwards [h] with ω hω γ k
  exact areaApprox_congr_dy (fun μ hμ => hω ⟨μ, hμ⟩) γ k

end GMCIdent4
end LQGMetric
