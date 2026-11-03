/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenLower1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# GFF-K3, node H4 (part 1): radial mollifiers and circle mixtures

* `lintegral_mul_ηε`: polar decomposition of `b ↦ g b * ηε ε (b - c)` into circle averages,
  for the smooth radial bump `ηε ε` (support `closedBall 0 ε`, integral `1`).
* `Kε ε p c = ∫⁻ ofReal (greenH p b) ηε ε (b - c) db`: two-sided bounds from the circle mean-value
  formula (`Kε_ge`, `Kε_le`).
* `contDiff_integral_comp_sub`: `x ↦ ∫ F (x - g y) dν` is smooth for smooth compactly supported `F`.
-/

noncomputable section

open MeasureTheory Filter Set Topology Real
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper.K3

/-! ## Periodic lintegrals and circles -/

lemma lintegral_Ioo_neg_pi_eq_Ico {F : ℝ → ℝ≥0∞} (hF : Function.Periodic F (2 * π)) :
    ∫⁻ θ in Ioo (-π) π, F θ = ∫⁻ θ in Ico 0 (2 * π), F θ := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (T := 2 * π) (-π) hF.lift
  have h2 := AddCircle.lintegral_preimage (T := 2 * π) 0 hF.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ico_ae_eq_Ioc]
  have e : -π + 2 * π = π := by ring
  rw [e] at h1
  rw [zero_add] at h2
  rw [h1, h2]

lemma lintegral_circleUnif_eq' {g : ℂ → ℝ≥0∞} (hg : Measurable g) (c : ℂ) (r : ℝ) :
    ∫⁻ w, g w ∂(circleUnif c r) =
      (ENNReal.ofReal (2 * π))⁻¹ * ∫⁻ θ in Ioo (-π) π, g (circleMap c r θ) := by
  unfold circleUnif
  rw [lintegral_smul_measure, lintegral_map hg (measurable_circleMap c r),
    ← lintegral_Ioo_neg_pi_eq_Ico (F := fun θ => g (circleMap c r θ))
      ((periodic_circleMap c r).comp g), smul_eq_mul]

lemma countable_circleMap_preimage (c p : ℂ) {r : ℝ} (hr : 0 < r) :
    ({θ : ℝ | circleMap c r θ = p}).Countable := by
  by_cases hne : ∃ θ₀, circleMap c r θ₀ = p
  · obtain ⟨θ₀, h0⟩ := hne
    refine (Set.countable_range (fun k : ℤ => θ₀ + k * (2 * π))).mono ?_
    intro θ hθ
    have h1 : circleMap c r θ = circleMap c r θ₀ := hθ.trans h0.symm
    simp only [circleMap] at h1
    have h2 : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) := by
      have h3 := add_left_cancel h1
      exact mul_left_cancel₀ (by exact_mod_cast hr.ne') h3
    rw [Complex.exp_eq_exp_iff_exists_int] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    have h4 := congrArg Complex.im hk
    simp at h4
    simp only
    linarith
  · have : {θ : ℝ | circleMap c r θ = p} = ∅ := by
      ext θ; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨θ, h⟩
    rw [this]; exact countable_empty

lemma circleUnif_singleton (c p : ℂ) {r : ℝ} (hr : 0 < r) : circleUnif c r {p} = 0 := by
  unfold circleUnif
  rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap c r) (measurableSet_singleton p)]
  have h0 : volume (circleMap c r ⁻¹' {p}) = 0 :=
    (countable_circleMap_preimage c p hr).measure_zero volume
  have h1 : (volume.restrict (Ico 0 (2 * π))) (circleMap c r ⁻¹' {p}) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_le_self (μ := volume) (s := Ico 0 (2 * π)) _).trans
      h0.le)
  rw [h1, smul_zero]

/-! ## The radial bump -/

/-- The unnormalized radial bump of radius `ε`. -/
def bη (ε : ℝ) (v : ℂ) : ℝ := Real.smoothTransition (1 - ‖v‖ ^ 2 / ε ^ 2)

lemma contDiff_bη (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bη ε) := by
  unfold bη
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

lemma bη_nonneg (ε : ℝ) (v : ℂ) : 0 ≤ bη ε v := Real.smoothTransition.nonneg _

lemma bη_eq_zero {ε : ℝ} (hε : 0 < ε) {v : ℂ} (hv : ε ≤ ‖v‖) : bη ε v = 0 := by
  unfold bη
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [sub_nonpos, one_le_div (by positivity)]
  exact pow_le_pow_left₀ hε.le hv 2

lemma bη_zero (ε : ℝ) : bη ε 0 = 1 := by
  simp [bη, Real.smoothTransition.one]

lemma bη_radial (ε : ℝ) {v w : ℂ} (h : ‖v‖ = ‖w‖) : bη ε v = bη ε w := by
  simp only [bη, h]

lemma hasCompactSupport_bη {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (bη ε) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ε) fun v hv => by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    exact bη_eq_zero hε hv.le

/-- The normalizing constant. -/
def Zη (ε : ℝ) : ℝ := ∫ v, bη ε v

lemma Zη_pos {ε : ℝ} (hε : 0 < ε) : 0 < Zη ε :=
  (contDiff_bη ε).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_bη hε) (fun v => bη_nonneg ε v) (x := 0) (by rw [bη_zero]; exact one_ne_zero)

/-- The normalized radial bump `ηε ε` (integral `1`, support `closedBall 0 ε`). -/
def ηε (ε : ℝ) (v : ℂ) : ℝ := bη ε v / Zη ε

lemma contDiff_ηε (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ηε ε) :=
  (contDiff_bη ε).div_const _

lemma ηε_nonneg {ε : ℝ} (hε : 0 < ε) (v : ℂ) : 0 ≤ ηε ε v :=
  div_nonneg (bη_nonneg ε v) (Zη_pos hε).le

lemma ηε_eq_zero {ε : ℝ} (hε : 0 < ε) {v : ℂ} (hv : ε ≤ ‖v‖) : ηε ε v = 0 := by
  simp [ηε, bη_eq_zero hε hv]

lemma hasCompactSupport_ηε {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ηε ε) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ε) fun v hv => by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    exact ηε_eq_zero hε hv.le

lemma integral_ηε {ε : ℝ} (hε : 0 < ε) : ∫ v, ηε ε v = 1 := by
  unfold ηε
  rw [integral_div]
  exact div_self (Zη_pos hε).ne'

/-- The radial weight: `W ε r = 2π r ηε ε r`. -/
def Wη (ε r : ℝ) : ℝ := 2 * π * r * ηε ε r

/-- **Polar decomposition** of a radial mollification into circle averages. -/
theorem lintegral_mul_ηε {ε : ℝ} (g : ℂ → ℝ≥0∞) (hg : Measurable g) (c : ℂ) :
    ∫⁻ b, g b * ENNReal.ofReal (ηε ε (b - c)) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Wη ε r) * ∫⁻ w, g w ∂circleUnif c r := by
  have h1 : ∫⁻ b, g b * ENNReal.ofReal (ηε ε (b - c)) =
      ∫⁻ v, g (v + c) * ENNReal.ofReal (ηε ε v) := by
    rw [← lintegral_add_right_eq_self _ c]; simp only [add_sub_cancel_right]
  have hmeas : Measurable fun v => g (v + c) * ENNReal.ofReal (ηε ε v) :=
    (hg.comp (measurable_id.add_const c)).mul
      (ENNReal.measurable_ofReal.comp (contDiff_ηε ε).continuous.measurable)
  have hpt : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm, hpt,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have hrad : ∀ θ, ηε ε (Complex.polarCoord.symm (r, θ)) = ηε ε r := by
      intro θ
      unfold ηε
      rw [bη_radial ε (w := (r : ℂ))]
      rw [polarCoord_symm_eq_circleMap, norm_circleMap_zero, Complex.norm_real]
      exact (Real.norm_eq_abs r).symm
    have hcm : ∀ θ, Complex.polarCoord.symm (r, θ) + c = circleMap c r θ := by
      intro θ; rw [polarCoord_symm_eq_circleMap]; simp [circleMap]; ring
    simp only [hrad, hcm, smul_eq_mul]
    rw [lintegral_circleUnif_eq' hg c r]
    have e : ∀ θ, ENNReal.ofReal r * (g (circleMap c r θ) * ENNReal.ofReal (ηε ε r)) =
        (ENNReal.ofReal r * ENNReal.ofReal (ηε ε r)) * g (circleMap c r θ) := fun θ => by ring
    simp_rw [e]
    rw [lintegral_const_mul (f := fun θ => g (circleMap c r θ)) _
      (by exact hg.comp (measurable_circleMap c r))]
    have h2π : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hW : ENNReal.ofReal (Wη ε r) =
        ENNReal.ofReal (2 * π) * (ENNReal.ofReal r * ENNReal.ofReal (ηε ε r)) := by
      unfold Wη
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ring
    rw [hW]
    calc _ = ENNReal.ofReal r * ENNReal.ofReal (ηε ε r) *
          (ENNReal.ofReal (2 * π) * (ENNReal.ofReal (2 * π))⁻¹) *
          ∫⁻ θ in Ioo (-π) π, g (circleMap c r θ) := by
          rw [ENNReal.mul_inv_cancel h2π ENNReal.ofReal_ne_top]; ring
      _ = _ := by ring
  · have hps : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) = fun p => circleMap 0 p.1 p.2 :=
        funext polarCoord_symm_eq_circleMap
      rw [this]; exact (continuous_circleMap_uncurry 0).measurable
    exact ((ENNReal.measurable_ofReal.comp measurable_fst).smul (hmeas.comp hps)).aemeasurable

lemma integrable_ηε_comp {ε : ℝ} (hε : 0 < ε) (c : ℂ) : Integrable (fun b => ηε ε (b - c)) :=
  ((contDiff_ηε ε).continuous.integrable_of_hasCompactSupport (hasCompactSupport_ηε hε)).comp_sub_right c

lemma lintegral_Wη {ε : ℝ} (hε : 0 < ε) : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Wη ε r) = 1 := by
  have h := lintegral_mul_ηε (ε := ε) (fun _ => 1) measurable_const 0
  simp only [one_mul, sub_zero, lintegral_const, measure_univ, mul_one] at h
  rw [← h, ← ofReal_integral_eq_lintegral_ofReal (by simpa using integrable_ηε_comp hε 0)
    (ae_of_all _ (ηε_nonneg hε)), integral_ηε hε, ENNReal.ofReal_one]

lemma Wη_eq_zero {ε r : ℝ} (hε : 0 < ε) (hr : ε < r) : Wη ε r = 0 := by
  unfold Wη
  rw [ηε_eq_zero hε (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hr.le.trans (le_abs_self r)),
    mul_zero]

/-- The circle mean of `greenH p` (`Real.log` of `max`). -/
def mvG (r : ℝ) (c p : ℂ) : ℝ := Real.log (max r ‖c - conj p‖) - Real.log (max r ‖c - p‖)

lemma two_eps_le_norm {ε : ℝ} {p c : ℂ} (hp : p ∈ Hbar) (hc : 2 * ε ≤ c.im) :
    2 * ε ≤ ‖c - conj p‖ := by
  have h1 : (c - conj p).im ≤ ‖c - conj p‖ := Complex.im_le_norm _
  have h2 : (c - conj p).im = c.im + p.im := by simp
  have hp' : 0 ≤ p.im := hp
  linarith

lemma lintegral_greenH_circle {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) {p c : ℂ}
    (hp : p ∈ Hbar) (hc : 2 * ε ≤ c.im) :
    ∫⁻ w, ENNReal.ofReal (greenH p w) ∂circleUnif c r = ENNReal.ofReal (mvG r c p) := by
  have hint : Integrable (fun w => greenH w p) (circleUnif c r) :=
    (CircleMV.integrable_log_norm_sub_circleUnif c (conj p) r).sub
      (CircleMV.integrable_log_norm_sub_circleUnif c p r)
  have hnn : 0 ≤ᵐ[circleUnif c r] fun w => greenH w p := by
    have hs : ∀ᵐ w ∂circleUnif c r, w ≠ p := by
      rw [ae_iff]
      have : {a | ¬a ≠ p} = {p} := by ext a; simp
      rw [this]; exact circleUnif_singleton c p hr
    filter_upwards [CircleMV.ae_circleUnif c r, hs] with w hw hwp
    refine greenH_nonneg ?_ hp hwp
    have him : |(w - c).im| ≤ ‖w - c‖ := Complex.abs_im_le_norm _
    rw [hw, abs_of_pos hr, Complex.sub_im] at him
    show 0 ≤ w.im
    linarith [neg_abs_le (w.im - c.im)]
  have hl : ∫⁻ w, ENNReal.ofReal (greenH p w) ∂circleUnif c r =
      ∫⁻ w, ENNReal.ofReal (greenH w p) ∂circleUnif c r :=
    lintegral_congr fun w => by rw [greenH_symm]
  rw [hl, ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_greenH_circleUnif c p hr]
  rfl

/-- The radially mollified Green kernel. -/
def Kε (ε : ℝ) (p c : ℂ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal (greenH p b) * ENNReal.ofReal (ηε ε (b - c))

lemma measurable_greenH_left (p : ℂ) : Measurable fun b => greenH p b :=
  measurable_greenH.comp (measurable_const.prodMk measurable_id)

lemma Kε_eq (ε : ℝ) (p c : ℂ) : Kε ε p c =
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Wη ε r) *
      ∫⁻ w, ENNReal.ofReal (greenH p w) ∂circleUnif c r :=
  lintegral_mul_ηε _ (ENNReal.measurable_ofReal.comp (measurable_greenH_left p)) c

lemma Kε_ge {ε : ℝ} (hε : 0 < ε) {p c : ℂ} (hp : p ∈ Hbar) (hc : 2 * ε ≤ c.im) :
    ENNReal.ofReal (Real.log ‖c - conj p‖ - Real.log (max ε ‖c - p‖)) ≤ Kε ε p c := by
  rw [Kε_eq]
  have hpos : 0 < ‖c - conj p‖ := by linarith [two_eps_le_norm hp hc]
  calc ENNReal.ofReal (Real.log ‖c - conj p‖ - Real.log (max ε ‖c - p‖))
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Wη ε r) *
          ENNReal.ofReal (Real.log ‖c - conj p‖ - Real.log (max ε ‖c - p‖)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Wη hε, one_mul]
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
        have hr0 : 0 < r := hr
        by_cases hrε : r ≤ ε
        · rw [lintegral_greenH_circle hε hr0 hrε hp hc]
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          unfold mvG
          have h1 : Real.log ‖c - conj p‖ ≤ Real.log (max r ‖c - conj p‖) :=
            Real.log_le_log hpos (le_max_right _ _)
          have h2 : Real.log (max r ‖c - p‖) ≤ Real.log (max ε ‖c - p‖) :=
            Real.log_le_log (lt_max_of_lt_left hr0) (max_le_max hrε le_rfl)
          linarith
        · rw [Wη_eq_zero hε (lt_of_not_ge hrε)]; simp

lemma Kε_le {ε : ℝ} (hε : 0 < ε) {p c : ℂ} (hp : p ∈ Hbar) (hc : 2 * ε ≤ c.im) (hpc : p ≠ c) :
    Kε ε p c ≤ ENNReal.ofReal (greenH c p) := by
  rw [Kε_eq]
  have hn := two_eps_le_norm hp hc
  have hpos : 0 < ‖c - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpc.symm)
  calc _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Wη ε r) * ENNReal.ofReal (greenH c p) := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
        have hr0 : 0 < r := hr
        by_cases hrε : r ≤ ε
        · rw [lintegral_greenH_circle hε hr0 hrε hp hc]
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          unfold mvG greenH
          rw [max_eq_right (by linarith)]
          have h2 : Real.log ‖c - p‖ ≤ Real.log (max r ‖c - p‖) :=
            Real.log_le_log hpos (le_max_right _ _)
          linarith
        · rw [Wη_eq_zero hε (lt_of_not_ge hrε)]; simp
    _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Wη hε, one_mul]

/-! ## Smoothness of mollified measures -/

section Smooth

lemma hasFDerivAt_integral_comp_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ν : Measure ℂ) [IsFiniteMeasure ν] {g : ℂ → ℂ} (hg : Continuous g)
    {F : ℂ → E} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (x₀ : ℂ) :
    HasFDerivAt (fun x => ∫ y, F (x - g y) ∂ν) (∫ y, fderiv ℝ F (x₀ - g y) ∂ν) x₀ := by
  obtain ⟨C, hC⟩ := (hF.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨C0, hC0⟩ := hF.continuous.bounded_above_of_compact_support hFc
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := univ)
    (F := fun x y => F (x - g y)) (F' := fun x y => fderiv ℝ F (x - g y)) (bound := fun _ => C)
    Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · exact Eventually.of_forall fun x =>
      (hF.continuous.comp (continuous_const.sub hg)).aestronglyMeasurable
  · exact (integrable_const C0).mono'
      (hF.continuous.comp (continuous_const.sub hg)).aestronglyMeasurable
      (ae_of_all _ fun y => hC0 _)
  · exact ((hF.continuous_fderiv one_ne_zero).comp (continuous_const.sub hg)).aestronglyMeasurable
  · exact ae_of_all _ fun y x _ => hC _
  · refine ae_of_all _ fun y x _ => ?_
    have h1 : HasFDerivAt F (fderiv ℝ F (x - g y)) (x - g y) :=
      (hF.differentiable one_ne_zero _).hasFDerivAt
    have h2 := h1.comp x ((hasFDerivAt_id x).sub_const (g y))
    simp only [ContinuousLinearMap.comp_id] at h2
    exact h2

theorem contDiff_integral_comp_sub (ν : Measure ℂ) [IsFiniteMeasure ν] {g : ℂ → ℂ}
    (hg : Continuous g) (n : ℕ) : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : ℂ → E}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F → HasCompactSupport F →
      ContDiff ℝ n (fun x => ∫ y, F (x - g y) ∂ν) := by
  induction n with
  | zero =>
    intro E _ _ _ F hF hFc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_integral_comp_sub ν hg (hF.of_le (by exact_mod_cast le_top)) hFc x).continuousAt
  | succ n ih =>
    intro E _ _ _ F hF hFc
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
    have hd := hasFDerivAt_integral_comp_sub ν hg hF1 hFc
    have hfd : fderiv ℝ (fun x => ∫ y, F (x - g y) ∂ν) =
        fun x => ∫ y, fderiv ℝ F (x - g y) ∂ν := funext fun x => (hd x).fderiv
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (hF.fderiv_right (by exact_mod_cast le_top)) (hFc.fderiv (𝕜 := ℝ))

end Smooth

end QuantumZipper.K3
