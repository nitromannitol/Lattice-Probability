/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.SmoothingConvergence at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Almost sure convergence of smoothed pairings of the free GFF

For a measure `ν = volume.withDensity g` with bounded density supported on a compact set
`K ⊆ {δ < Im z}`, let `νk = ν.bind (fun w => foldedCircle w (radius k))` be its smoothing by
folded circle averages at radius `2^{-k}`. For a free-boundary GFF modulo constants `X` and two
such measures `ν, ν'` of equal mass, `X νk - X ν'k → X ν - X ν'` almost surely.

Proof: the variance of `(X νk - X ν'k) - (X ν - X ν')` is `O(4^{-k})` (energy estimate, from
the mean value property of `log` on circles), and a variance series argument.
-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper

namespace SmoothConv

/-! ## Circle averages of `log` (local copies of the MV-LOG lemmas) -/

theorem circleUnif_eq_circMeas_sc (z : ℂ) (r : ℝ) :
    circleUnif z r = LQGDimension.Coupling.circMeas z r := by
  unfold circleUnif LQGDimension.Coupling.circMeas LQGDimension.Coupling.angMeas
  rw [Measure.map_smul, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  all_goals exact (measurable_circleMap z r).aemeasurable

theorem ae_circleUnif_sc (z : ℂ) (r : ℝ) : ∀ᵐ w ∂circleUnif z r, ‖w - z‖ = |r| := by
  rw [circleUnif_eq_circMeas_sc]; exact LQGDimension.Coupling.ae_circMeas z r

theorem integrable_log_norm_sub_circleUnif_sc (z y : ℂ) (r : ℝ) :
    Integrable (fun w => Real.log ‖w - y‖) (circleUnif z r) := by
  rw [circleUnif_eq_circMeas_sc]
  simpa [norm_sub_rev] using LQGDimension.Coupling.integrable_log_norm_sub_circ y z r

theorem log_add_posLog_eq_sc {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    Real.log r + Real.posLog (r⁻¹ * a) = Real.log (max r a) := by
  rw [Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hr.ne'
    (by positivity : (0:ℝ) < max 1 (r⁻¹ * a)).ne', mul_max_of_nonneg _ _ hr.le, mul_one,
    ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

theorem integral_log_norm_sub_circleUnif_sc (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ w, Real.log ‖w - y‖ ∂(circleUnif z r) = Real.log (max r ‖z - y‖) := by
  rw [circleUnif_eq_circMeas_sc]
  have h := LQGDimension.Coupling.integral_log_norm_sub_circ y z hr
  simp only [norm_sub_rev y] at h
  rw [h, log_add_posLog_eq_sc hr (norm_nonneg _)]

theorem neumannH_foldH_sc (x y : ℂ) : neumannH (foldH x) y = neumannH x y := by
  unfold foldH neumannH
  split_ifs
  · rfl
  · have h1 : ‖conj x - y‖ = ‖x - conj y‖ := by
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
    have h2 : ‖conj x - conj y‖ = ‖x - y‖ := by
      rw [← map_sub, Complex.norm_conj]
    rw [h1, h2]; ring

theorem integral_neumannH_foldedCircle_sc (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ x, neumannH x y ∂(foldedCircle z r) =
      -Real.log (max r ‖z - y‖) - Real.log (max r ‖z - conj y‖) := by
  have hm : Measurable fun x => neumannH x y :=
    measurable_neumannH.comp (measurable_id.prodMk measurable_const)
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable hm.aestronglyMeasurable]
  simp only [neumannH_foldH_sc]
  unfold neumannH
  have h1 : Integrable (fun x => -Real.log ‖x - y‖) (circleUnif z r) :=
    (integrable_log_norm_sub_circleUnif_sc z y r).neg
  rw [integral_sub h1 (integrable_log_norm_sub_circleUnif_sc z (conj y) r), integral_neg,
    integral_log_norm_sub_circleUnif_sc z y hr, integral_log_norm_sub_circleUnif_sc z _ hr]

theorem foldedCircle_eq_circleUnif_sc {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hrz : r ≤ z.im) :
    foldedCircle z r = circleUnif z r := by
  unfold foldedCircle
  conv_rhs => rw [← Measure.map_id (μ := circleUnif z r)]
  refine Measure.map_congr ?_
  filter_upwards [ae_circleUnif_sc z r] with w hw
  have him : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  rw [hw, abs_of_nonneg hr, Complex.sub_im] at him
  have : 0 ≤ w.im := by linarith [neg_abs_le (w.im - z.im)]
  simp [foldH, this]

/-! ## The planar logarithmic potential -/

/-- `∫ log⁻(|z|/r) dz ≤ 2π r²` (the exact value is `π r² / 2`). -/
theorem lintegral_neg_log_div_le (r : ℝ) (hr : 0 < r) :
    ∫⁻ z : ℂ, ENNReal.ofReal (-Real.log (‖z‖ / r)) ≤ ENNReal.ofReal (2 * π * r ^ 2) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  simp only [Complex.norm_polarCoord_symm]
  have hmeas : MeasurableSet (Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  calc ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • ENNReal.ofReal (-Real.log (|p.1| / r))
      ≤ ∫⁻ p in Complex.polarCoord.target,
          (Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ)).indicator (fun _ => ENNReal.ofReal r) p := by
        refine lintegral_mono fun p => ?_
        rw [smul_eq_mul]
        rcases le_or_gt p.1 0 with h0 | h0
        · simp [ENNReal.ofReal_of_nonpos h0]
        rcases le_or_gt r p.1 with h1 | h1
        · have : -Real.log (|p.1| / r) ≤ 0 := by
            rw [abs_of_pos h0, neg_nonpos]
            exact Real.log_nonneg ((one_le_div hr).2 h1)
          simp [ENNReal.ofReal_of_nonpos this]
        · have hmem : p ∈ Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ) := ⟨⟨h0, h1⟩, trivial⟩
          rw [Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul h0.le]
          apply ENNReal.ofReal_le_ofReal
          rw [abs_of_pos h0]
          have hl : Real.log (r / p.1) ≤ r / p.1 - 1 := Real.log_le_sub_one_of_pos (by positivity)
          have h2 : -Real.log (p.1 / r) = Real.log (r / p.1) := by rw [← Real.log_inv, inv_div]
          have h3 : p.1 * (r / p.1 - 1) = r - p.1 := by field_simp
          rw [h2]
          nlinarith [mul_le_mul_of_nonneg_left hl h0.le]
    _ = ENNReal.ofReal r *
          volume ((Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ)) ∩ Complex.polarCoord.target) := by
        rw [lintegral_indicator_const hmeas, Measure.restrict_apply hmeas]
    _ ≤ ENNReal.ofReal r * volume (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (-π) π) := by
        gcongr
        rintro p ⟨⟨h1, -⟩, h2⟩
        rw [Complex.polarCoord_target] at h2
        exact ⟨h1, h2.2⟩
    _ = ENNReal.ofReal (2 * π * r ^ 2) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
          ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hr.le]
        congr 1; ring

/-- Logarithmic potential of a measure with density bounded by `M`. -/
theorem lintegral_neg_log_norm_sub_div_le {η : Measure ℂ} {M : ℝ≥0}
    (hη : η ≤ (M : ℝ≥0∞) • volume) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ w, ENNReal.ofReal (-Real.log (‖w - c‖ / r)) ∂η ≤
      (M : ℝ≥0∞) * ENNReal.ofReal (2 * π * r ^ 2) := by
  calc ∫⁻ w, ENNReal.ofReal (-Real.log (‖w - c‖ / r)) ∂η
      ≤ ∫⁻ w, ENNReal.ofReal (-Real.log (‖w - c‖ / r)) ∂((M : ℝ≥0∞) • volume) :=
        lintegral_mono' hη le_rfl
    _ = (M : ℝ≥0∞) * ∫⁻ w, ENNReal.ofReal (-Real.log (‖w - c‖ / r)) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ = (M : ℝ≥0∞) * ∫⁻ w : ℂ, ENNReal.ofReal (-Real.log (‖w‖ / r)) := by
        rw [lintegral_sub_right_eq_self (fun w : ℂ => ENNReal.ofReal (-Real.log (‖w‖ / r))) c]
    _ ≤ _ := by gcongr; exact lintegral_neg_log_div_le r hr

/-! ## Good measures: bounded density, bounded support in `Hbar` -/

/-- `μ` has density at most `M` and is supported in `closedBall 0 R ∩ Hbar`. -/
def IsGoodSC (M : ℝ≥0) (R : ℝ) (μ : Measure ℂ) : Prop :=
  μ ≤ (M : ℝ≥0∞) • volume ∧ μ (Metric.closedBall (0 : ℂ) R ∩ Hbar)ᶜ = 0

theorem IsGoodSC.mono {M : ℝ≥0} {R R' : ℝ} {μ : Measure ℂ} (h : IsGoodSC M R μ)
    (hR : R ≤ R') : IsGoodSC M R' μ :=
  ⟨h.1, measure_mono_null (Set.compl_subset_compl.2
    (Set.inter_subset_inter_left _ (Metric.closedBall_subset_closedBall hR))) h.2⟩

theorem IsGoodSC.ae_mem {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ} (h : IsGoodSC M R μ) :
    ∀ᵐ w ∂μ, w ∈ Metric.closedBall (0 : ℂ) R ∩ Hbar := ae_iff.2 h.2

theorem IsGoodSC.isFiniteMeasure {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ} (h : IsGoodSC M R μ) :
    IsFiniteMeasure μ := by
  refine ⟨?_⟩
  set S := Metric.closedBall (0 : ℂ) R ∩ Hbar
  calc μ Set.univ ≤ μ S + μ Sᶜ := by
        rw [← Set.union_compl_self S]; exact measure_union_le _ _
    _ = μ S := by rw [h.2, add_zero]
    _ ≤ ((M : ℝ≥0∞) • volume) S := Measure.le_iff'.1 h.1 S
    _ ≤ (M : ℝ≥0∞) * volume (Metric.closedBall (0 : ℂ) R) := by
        rw [Measure.smul_apply, smul_eq_mul]; gcongr; exact Set.inter_subset_left
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top measure_closedBall_lt_top

theorem IsGoodSC.measure_singleton {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ} (h : IsGoodSC M R μ)
    (x : ℂ) : μ {x} = 0 :=
  le_antisymm ((Measure.le_iff'.1 h.1 {x}).trans (by simp)) zero_le

theorem IsGoodSC.isAdmissibleH {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ} (h : IsGoodSC M R μ) :
    IsAdmissibleH μ := by
  refine ⟨h.isFiniteMeasure, ⟨_, (isCompact_closedBall 0 R).inter_right isClosed_Hbar,
    Set.inter_subset_right, h.2⟩, (M : ℝ≥0∞) * ENNReal.ofReal (2 * π * 1 ^ 2),
    ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top, fun y => ?_⟩
  simpa using lintegral_neg_log_norm_sub_div_le h.1 y one_pos

/-- `|log t| ≤ log⁻ t + log (2R+1)` for `0 ≤ t ≤ 2R`. -/
theorem enorm_log_le_sc {t R : ℝ} (ht : 0 ≤ t) (htR : t ≤ 2 * R) :
    ‖Real.log t‖ₑ ≤ ENNReal.ofReal (-Real.log t) + ENNReal.ofReal (Real.log (2 * R + 1)) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_or_gt (Real.log t) 0 with h | h
  · rw [abs_of_nonpos h]; exact le_self_add
  · rw [abs_of_pos h]
    refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
    have ht1 : 1 < t := by
      by_contra hc; push Not at hc; linarith [Real.log_nonpos ht hc]
    exact Real.log_le_log (by linarith) (by linarith)

theorem lintegral_enorm_log_norm_sub_le {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ}
    (h : IsGoodSC M R μ) {c : ℂ} (hc : ‖c‖ ≤ R) :
    ∫⁻ w, ‖Real.log ‖w - c‖‖ₑ ∂μ ≤
      (M : ℝ≥0∞) * ENNReal.ofReal (2 * π * 1 ^ 2) +
        ENNReal.ofReal (Real.log (2 * R + 1)) * μ Set.univ := by
  calc ∫⁻ w, ‖Real.log ‖w - c‖‖ₑ ∂μ
      ≤ ∫⁻ w, (ENNReal.ofReal (-Real.log (‖w - c‖ / 1)) +
          ENNReal.ofReal (Real.log (2 * R + 1))) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [h.ae_mem] with w hw
        rw [div_one]
        refine enorm_log_le_sc (norm_nonneg _) ?_
        have hw' : ‖w‖ ≤ R := by simpa using hw.1
        linarith [norm_sub_le w c]
    _ = ∫⁻ w, ENNReal.ofReal (-Real.log (‖w - c‖ / 1)) ∂μ +
          ENNReal.ofReal (Real.log (2 * R + 1)) * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ _ := by gcongr; exact lintegral_neg_log_norm_sub_div_le h.1 c one_pos

theorem lintegral_enorm_log_norm_sub_lt_top {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ}
    (h : IsGoodSC M R μ) (c : ℂ) : ∫⁻ w, ‖Real.log ‖w - c‖‖ₑ ∂μ < ⊤ := by
  have h' := h.mono (le_max_left R ‖c‖)
  have := h.isFiniteMeasure
  refine (lintegral_enorm_log_norm_sub_le h' (le_max_right _ _)).trans_lt ?_
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem integrable_log_norm_sub_sc {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ}
    (h : IsGoodSC M R μ) (c : ℂ) : Integrable (fun w => Real.log ‖w - c‖) μ :=
  ⟨(Real.measurable_log.comp (measurable_id.sub_const c).norm).aestronglyMeasurable,
    lintegral_enorm_log_norm_sub_lt_top h c⟩

theorem neumannH_eq_sc (x w : ℂ) :
    neumannH x w = -Real.log ‖w - x‖ - Real.log ‖w - conj x‖ := by
  rw [neumannH_symm]; rfl

theorem integrable_neumannH_right_sc {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ}
    (h : IsGoodSC M R μ) (x : ℂ) : Integrable (fun w => neumannH x w) μ := by
  simp only [neumannH_eq_sc]
  exact (integrable_log_norm_sub_sc h x).neg.sub (integrable_log_norm_sub_sc h (conj x))

theorem integrable_neumannH_left_sc {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ}
    (h : IsGoodSC M R μ) (x : ℂ) : Integrable (fun w => neumannH w x) μ := by
  simp only [neumannH_symm _ x]; exact integrable_neumannH_right_sc h x

theorem lintegral_enorm_neumannH_le {M : ℝ≥0} {R : ℝ} {μ : Measure ℂ}
    (h : IsGoodSC M R μ) {x : ℂ} (hx : ‖x‖ ≤ R) :
    ∫⁻ w, ‖neumannH x w‖ₑ ∂μ ≤
      2 * ((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * 1 ^ 2) +
        ENNReal.ofReal (Real.log (2 * R + 1)) * μ Set.univ) := by
  calc ∫⁻ w, ‖neumannH x w‖ₑ ∂μ
      ≤ ∫⁻ w, (‖Real.log ‖w - x‖‖ₑ + ‖Real.log ‖w - conj x‖‖ₑ) ∂μ := by
        refine lintegral_mono fun w => ?_
        rw [neumannH_eq_sc]
        refine (enorm_sub_le).trans ?_
        rw [enorm_neg]
    _ = ∫⁻ w, ‖Real.log ‖w - x‖‖ₑ ∂μ + ∫⁻ w, ‖Real.log ‖w - conj x‖‖ₑ ∂μ :=
        lintegral_add_left
          (Real.measurable_log.comp (measurable_id.sub_const x).norm).enorm _
    _ ≤ _ := by
        rw [two_mul]
        gcongr
        · exact lintegral_enorm_log_norm_sub_le h hx
        · exact lintegral_enorm_log_norm_sub_le h (by rwa [Complex.norm_conj])

theorem integrable_neumannH_prod_sc {M : ℝ≥0} {R : ℝ} {p η : Measure ℂ}
    (hp : IsGoodSC M R p) (hη : IsGoodSC M R η) :
    Integrable (fun q : ℂ × ℂ => neumannH q.1 q.2) (p.prod η) := by
  have := hp.isFiniteMeasure
  have := hη.isFiniteMeasure
  refine ⟨measurable_neumannH.aestronglyMeasurable, ?_⟩
  show ∫⁻ q, ‖neumannH q.1 q.2‖ₑ ∂(p.prod η) < ⊤
  rw [lintegral_prod _ measurable_neumannH.enorm.aemeasurable]
  refine (lintegral_mono_ae (g := fun _ => 2 * ((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * 1 ^ 2) +
        ENNReal.ofReal (Real.log (2 * R + 1)) * η Set.univ)) ?_).trans_lt ?_
  · filter_upwards [hp.ae_mem] with x hx
    exact lintegral_enorm_neumannH_le hη (by simpa using hx.1)
  · rw [lintegral_const]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩)) (measure_lt_top _ _)

/-! ## The folded-circle kernel -/

theorem measurable_circleMap_joint (r : ℝ) :
    Measurable (fun q : ℂ × ℝ => circleMap q.1 r q.2) := by
  have : (fun q : ℂ × ℝ => circleMap q.1 r q.2) =
      fun q => q.1 + (r : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) := rfl
  rw [this]
  exact (continuous_fst.add (continuous_const.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))).measurable

theorem foldedCircle_apply_eq (w : ℂ) (r : ℝ) {s : Set ℂ} (hs : MeasurableSet s) :
    foldedCircle w r s = (ENNReal.ofReal (2 * π))⁻¹ *
      (volume.restrict (Set.Ico 0 (2 * π)))
        (Prod.mk w ⁻¹' {q : ℂ × ℝ | foldH (circleMap q.1 r q.2) ∈ s}) := by
  rw [foldedCircle, Measure.map_apply measurable_foldH hs, circleUnif, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_circleMap w r) (measurable_foldH hs)]
  rfl

theorem measurable_foldedCircle (r : ℝ) : Measurable (fun w => foldedCircle w r) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [foldedCircle_apply_eq _ r hs]
  exact (measurable_measure_prodMk_left
    ((measurable_foldH.comp (measurable_circleMap_joint r)) hs)).const_mul _

/-- The folded-circle averaging kernel at radius `r`. -/
def fcKernel (r : ℝ) : Kernel ℂ ℂ := ⟨fun w => foldedCircle w r, measurable_foldedCircle r⟩

instance isMarkovKernel_fcKernel (r : ℝ) : IsMarkovKernel (fcKernel r) :=
  ⟨fun w => isProbabilityMeasure_foldedCircle w r⟩

theorem integral_bind_fc {η : Measure ℂ} [SFinite η] (r : ℝ) {f : ℂ → ℝ}
    (hf : Integrable f (η.bind (fun w => foldedCircle w r))) :
    ∫ y, f y ∂(η.bind (fun w => foldedCircle w r)) =
      ∫ w, ∫ y, f y ∂(foldedCircle w r) ∂η := by
  have hb : η.bind (fun w => foldedCircle w r) = fcKernel r ∘ₘ η := rfl
  rw [hb] at hf ⊢
  rw [← Measure.snd_compProd] at hf ⊢
  rw [Measure.snd, integral_map measurable_snd.aemeasurable hf.1]
  exact Measure.integral_compProd ((integrable_map_measure hf.1 measurable_snd.aemeasurable).1 hf)

/-- The circle-averaged kernel: `∫ neumannH x y d(foldedCircle w r)(y) = Nr r w x`. -/
def Nr (r : ℝ) (w x : ℂ) : ℝ := -Real.log (max r ‖w - x‖) - Real.log (max r ‖w - conj x‖)

/-- The smoothing defect of the kernel. -/
def Lr (r : ℝ) (w x : ℂ) : ℝ := neumannH w x - Nr r w x

theorem continuous_Nr {r : ℝ} (hr : 0 < r) : Continuous (fun q : ℂ × ℂ => Nr r q.1 q.2) := by
  unfold Nr
  have h1 : Continuous fun q : ℂ × ℂ => max r ‖q.1 - q.2‖ :=
    continuous_const.max (continuous_fst.sub continuous_snd).norm
  have h2 : Continuous fun q : ℂ × ℂ => max r ‖q.1 - conj q.2‖ :=
    continuous_const.max (continuous_fst.sub (Complex.continuous_conj.comp continuous_snd)).norm
  exact (h1.log fun q => (lt_of_lt_of_le hr (le_max_left _ _)).ne').neg.sub
    (h2.log fun q => (lt_of_lt_of_le hr (le_max_left _ _)).ne')

theorem measurable_Lr {r : ℝ} (hr : 0 < r) : Measurable (fun q : ℂ × ℂ => Lr r q.1 q.2) :=
  measurable_neumannH.sub (continuous_Nr hr).measurable

theorem integral_bind_neumannH {η : Measure ℂ} [SFinite η] {r : ℝ} (hr : 0 < r) (x : ℂ)
    (hint : Integrable (fun y => neumannH x y) (η.bind (fun w => foldedCircle w r))) :
    ∫ y, neumannH x y ∂(η.bind (fun w => foldedCircle w r)) = ∫ w, Nr r w x ∂η := by
  rw [integral_bind_fc r hint]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  show ∫ y, neumannH x y ∂foldedCircle w r = Nr r w x
  rw [show (∫ y, neumannH x y ∂foldedCircle w r) = ∫ y, neumannH y x ∂foldedCircle w r from
    integral_congr_ae (ae_of_all _ fun y => neumannH_symm x y)]
  exact integral_neumannH_foldedCircle_sc w x hr

theorem integrable_Nr_left {M : ℝ≥0} {R r : ℝ} {η : Measure ℂ} (hr : 0 < r)
    (h : IsGoodSC M R η) (x : ℂ) : Integrable (fun w => Nr r w x) η := by
  have := h.isFiniteMeasure
  have hc : Continuous fun w => Nr r w x :=
    (continuous_Nr hr).comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) R).inter_right
    isClosed_Hbar).exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound hc.aestronglyMeasurable C (h.ae_mem.mono fun w hw => hC w hw)

theorem integrable_Lr_left {M : ℝ≥0} {R r : ℝ} {η : Measure ℂ} (hr : 0 < r)
    (h : IsGoodSC M R η) (x : ℂ) : Integrable (fun w => Lr r w x) η :=
  (integrable_neumannH_left_sc h x).sub (integrable_Nr_left hr h x)

theorem Lr_eq_of {r : ℝ} (hr : 0 < r) {w x : ℂ} (hw : w ≠ x) (hwr : r ≤ w.im) (hx : x ∈ Hbar) :
    Lr r w x = (ENNReal.ofReal (-Real.log (‖w - x‖ / r))).toReal := by
  have hs : r ≤ ‖w - conj x‖ := by
    have h1 := Complex.abs_im_le_norm (w - conj x)
    simp only [Complex.sub_im, Complex.conj_im] at h1
    have hx' : 0 ≤ x.im := hx
    rw [abs_of_nonneg (by linarith)] at h1; linarith
  have ht : 0 < ‖w - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  rw [ENNReal.toReal_ofReal', Real.log_div ht.ne' hr.ne']
  unfold Lr Nr neumannH
  rw [max_eq_right hs]
  rcases le_total ‖w - x‖ r with h | h
  · rw [max_eq_left h, max_eq_left (by linarith [Real.log_le_log ht h])]; ring
  · rw [max_eq_right h, max_eq_right (by linarith [Real.log_le_log hr h])]; ring

theorem abs_integral_Lr_le {M : ℝ≥0} {R r : ℝ} {η : Measure ℂ} (hr : 0 < r)
    (h : IsGoodSC M R η) (him : ∀ᵐ w ∂η, r ≤ w.im) {x : ℂ} (hx : x ∈ Hbar) :
    |∫ w, Lr r w x ∂η| ≤ ((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * r ^ 2)).toReal := by
  have hne : ∀ᵐ w ∂η, w ≠ x := ae_iff.2 (by simpa using h.measure_singleton x)
  have hae : ∀ᵐ w ∂η, Lr r w x = (ENNReal.ofReal (-Real.log (‖w - x‖ / r))).toReal := by
    filter_upwards [hne, him] with w hw hwr
    exact Lr_eq_of hr hw hwr hx
  have hm : AEMeasurable (fun w => ENNReal.ofReal (-Real.log (‖w - x‖ / r))) η :=
    (ENNReal.measurable_ofReal.comp
      ((Real.measurable_log.comp ((measurable_id.sub_const x).norm.div_const r)).neg)).aemeasurable
  rw [integral_congr_ae hae, integral_toReal hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
    (lintegral_neg_log_norm_sub_div_le h.1 x hr)

theorem abs_Lam_le {M : ℝ≥0} {R r : ℝ} {p η : Measure ℂ} (hr : 0 < r)
    (hp : IsGoodSC M R p) (hη : IsGoodSC M R η) (him : ∀ᵐ w ∂η, r ≤ w.im) :
    |∫ x, ∫ w, Lr r w x ∂η ∂p| ≤
      ((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * r ^ 2)).toReal * (p Set.univ).toReal := by
  have := hp.isFiniteMeasure
  have := norm_integral_le_of_norm_le_const (μ := p) (f := fun x => ∫ w, Lr r w x ∂η)
    (C := ((M : ℝ≥0∞) * ENNReal.ofReal (2 * π * r ^ 2)).toReal)
    (hp.ae_mem.mono fun x hx => by rw [Real.norm_eq_abs]; exact abs_integral_Lr_le hr hη him hx.2)
  rw [← Real.norm_eq_abs]
  exact this

/-- Smoothing the second argument of `kernelCov neumannH` by folded circles subtracts the
defect term. -/
theorem kernelCov_bind_eq {M : ℝ≥0} {R r : ℝ} {p η : Measure ℂ} (hr : 0 < r)
    (hp : IsGoodSC M R p) (hη : IsGoodSC M R η)
    (hηk : IsGoodSC M R (η.bind fun w => foldedCircle w r)) (him : ∀ᵐ w ∂η, r ≤ w.im) :
    kernelCov neumannH p (η.bind fun w => foldedCircle w r) =
      kernelCov neumannH p η - ∫ x, ∫ w, Lr r w x ∂η ∂p := by
  have := hp.isFiniteMeasure
  have := hη.isFiniteMeasure
  unfold kernelCov
  have h1 : ∀ x, ∫ y, neumannH x y ∂(η.bind fun w => foldedCircle w r) =
      ∫ w, neumannH x w ∂η - ∫ w, Lr r w x ∂η := by
    intro x
    rw [integral_bind_neumannH hr x (integrable_neumannH_right_sc hηk x),
      ← integral_sub (integrable_neumannH_right_sc hη x) (integrable_Lr_left hr hη x)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Lr, neumannH_symm w x]; ring
  simp only [h1]
  have hF : Integrable (fun x => ∫ w, neumannH x w ∂η) p :=
    (integrable_neumannH_prod_sc hp hη).integral_prod_left
  have hGm : AEStronglyMeasurable (fun x => ∫ w, Lr r w x ∂η) p :=
    (((measurable_Lr hr).comp measurable_swap).aestronglyMeasurable
      (μ := p.prod η)).integral_prod_right'
  have hG : Integrable (fun x => ∫ w, Lr r w x ∂η) p :=
    Integrable.of_bound hGm _ (hp.ae_mem.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact abs_integral_Lr_le hr hη him hx.2)
  exact integral_sub hF hG

/-! ## The smoothed measure is again good -/

theorem lintegral_circleUnif_apply (r : ℝ) {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ w, circleUnif w r A = volume A := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have key : ∀ w, circleUnif w r A = (ENNReal.ofReal (2 * π))⁻¹ *
      ∫⁻ θ in Set.Ico 0 (2 * π), A.indicator (1 : ℂ → ℝ≥0∞) (circleMap w r θ) := by
    intro w
    rw [circleUnif, Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hA,
      lintegral_map (measurable_one.indicator hA) (measurable_circleMap w r)]
  simp_rw [key]
  have hm : Measurable (Function.uncurry fun (w : ℂ) (θ : ℝ) =>
      A.indicator (1 : ℂ → ℝ≥0∞) (circleMap w r θ)) :=
    (measurable_one.indicator hA).comp (measurable_circleMap_joint r)
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 h2π).ne'),
    lintegral_lintegral_swap (f := fun (w : ℂ) (θ : ℝ) =>
      A.indicator (1 : ℂ → ℝ≥0∞) (circleMap w r θ)) hm.aemeasurable]
  have hinner : ∀ θ : ℝ, ∫⁻ w, A.indicator (1 : ℂ → ℝ≥0∞) (circleMap w r θ) = volume A := by
    intro θ
    have : (fun w => A.indicator (1 : ℂ → ℝ≥0∞) (circleMap w r θ)) =
        fun w => A.indicator (1 : ℂ → ℝ≥0∞) (w + circleMap 0 r θ) := by
      funext w; simp [circleMap]
    rw [this, lintegral_add_right_eq_self (fun w => A.indicator (1 : ℂ → ℝ≥0∞) w),
      lintegral_indicator_one hA]
  simp_rw [hinner]
  rw [setLIntegral_const, Real.volume_Ico, sub_zero, mul_comm (volume A), ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 h2π).ne' ENNReal.ofReal_ne_top, one_mul]

theorem bind_fc_le {M : ℝ≥0} {r : ℝ} {η : Measure ℂ} (hr : 0 ≤ r)
    (hη : η ≤ (M : ℝ≥0∞) • volume) (him : ∀ᵐ w ∂η, r ≤ w.im) :
    η.bind (fun w => foldedCircle w r) ≤ (M : ℝ≥0∞) • volume := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.bind_apply hA (measurable_foldedCircle r).aemeasurable, Measure.smul_apply,
    smul_eq_mul]
  calc ∫⁻ w, foldedCircle w r A ∂η = ∫⁻ w, circleUnif w r A ∂η :=
        lintegral_congr_ae (him.mono fun w hw => by
          show foldedCircle w r A = circleUnif w r A
          rw [foldedCircle_eq_circleUnif_sc hr hw])
    _ ≤ ∫⁻ w, circleUnif w r A ∂((M : ℝ≥0∞) • volume) := lintegral_mono' hη le_rfl
    _ = (M : ℝ≥0∞) * volume A := by
        rw [lintegral_smul_measure, smul_eq_mul, lintegral_circleUnif_apply r hA]

theorem norm_foldH_sc (y : ℂ) : ‖foldH y‖ = ‖y‖ := by
  unfold foldH; split_ifs <;> simp

theorem foldH_mem_Hbar_sc (y : ℂ) : foldH y ∈ Hbar := by
  show 0 ≤ (foldH y).im
  unfold foldH
  split_ifs with h
  · exact h
  · push Not at h; simp only [Complex.conj_im]; linarith

theorem bind_fc_support {M : ℝ≥0} {R r : ℝ} {η : Measure ℂ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h : IsGoodSC M R η) :
    (η.bind fun w => foldedCircle w r) (Metric.closedBall (0 : ℂ) (R + 1) ∩ Hbar)ᶜ = 0 := by
  have hS : MeasurableSet (Metric.closedBall (0 : ℂ) (R + 1) ∩ Hbar) :=
    measurableSet_closedBall.inter isClosed_Hbar.measurableSet
  rw [Measure.bind_apply hS.compl (measurable_foldedCircle r).aemeasurable,
    lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
  filter_upwards [h.ae_mem] with w hw
  have hae : ∀ᵐ y ∂foldedCircle w r, y ∈ Metric.closedBall (0 : ℂ) (R + 1) ∩ Hbar := by
    rw [foldedCircle]
    refine (ae_map_iff (p := fun y => y ∈ Metric.closedBall (0 : ℂ) (R + 1) ∩ Hbar)
      measurable_foldH.aemeasurable hS).2 ?_
    filter_upwards [ae_circleUnif_sc w r] with y hy
    refine ⟨?_, foldH_mem_Hbar_sc y⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_foldH_sc]
    have hw' : ‖w‖ ≤ R := by simpa using hw.1
    calc ‖y‖ = ‖w + (y - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖y - w‖ := norm_add_le _ _
      _ ≤ R + 1 := by rw [hy, abs_of_nonneg hr0]; linarith
  exact ae_iff.1 hae

theorem bind_fc_univ (η : Measure ℂ) (r : ℝ) :
    (η.bind fun w => foldedCircle w r) Set.univ = η Set.univ := by
  rw [Measure.bind_apply MeasurableSet.univ (measurable_foldedCircle r).aemeasurable]
  simp

theorem IsGoodSC.bind_fc {M : ℝ≥0} {R r : ℝ} {η : Measure ℂ} (h : IsGoodSC M R η)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (him : ∀ᵐ w ∂η, r ≤ w.im) :
    IsGoodSC M (R + 1) (η.bind fun w => foldedCircle w r) :=
  ⟨bind_fc_le hr0 h.1 him, bind_fc_support hr0 hr1 h⟩

/-! ## The energy estimate -/

/-- A measure with bounded density supported on a compact subset of `{δ < Im z}` is good. -/
theorem isGoodSC_withDensity {g : ℂ → ℝ≥0∞} {M : ℝ≥0} (hgM : ∀ z, g z ≤ M) {K : Set ℂ}
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) (hKδ : K ⊆ {z | δ < z.im})
    (hgK : ∀ z ∉ K, g z = 0) {R : ℝ} (hKR : K ⊆ Metric.closedBall 0 R) :
    IsGoodSC M R (volume.withDensity g) ∧ ∀ᵐ w ∂(volume.withDensity g), δ < w.im := by
  have hKm : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hKc : volume.withDensity g Kᶜ = 0 := by
    rw [withDensity_apply _ hKm]
    exact (setLIntegral_congr_fun hKm (g := fun _ => (0 : ℝ≥0∞))
      (fun z hz => hgK z hz)).trans lintegral_zero
  refine ⟨⟨Measure.le_iff.2 fun A hA => ?_, measure_mono_null (Set.compl_subset_compl.2
    (Set.subset_inter hKR fun z hz => (hδ.trans (hKδ hz)).le)) hKc⟩,
    ae_iff.2 (measure_mono_null (fun z hz hzK => hz (hKδ hzK)) hKc)⟩
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ a in A, g a ≤ ∫⁻ _ in A, (M : ℝ≥0∞) := lintegral_mono fun z => hgM z
    _ = (M : ℝ≥0∞) * volume A := by rw [setLIntegral_const]

/-! ## Second moments and almost sure convergence -/

variable {Ω : Type*} [MeasurableSpace Ω]

theorem memLp_pair_sc {X : Ω → Measure ℂ → ℝ} {P : Measure Ω} (hX : IsFreeGFFModConstH X P)
    {p₁ p₂ : Measure ℂ} (h₁ : IsAdmissibleH p₁) (h₂ : IsAdmissibleH p₂)
    (hm : p₁ Set.univ = p₂ Set.univ) : MemLp (fun ω => X ω p₁ - X ω p₂) 2 P :=
  (hX.gaussian.hasGaussianLaw_eval ⟨(p₁, p₂), h₁, h₂, hm⟩).memLp_two

end SmoothConv

end QuantumZipper
