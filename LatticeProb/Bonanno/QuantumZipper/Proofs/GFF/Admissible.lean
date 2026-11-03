/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.Admissible at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Basic facts about admissible measures (`IsAdmissibleH`)

* bounded compactly supported densities are admissible;
* admissible measures have no atoms;
* `greenH`, `neumannH` are integrable against `μ.prod ν` for admissible `μ, ν`;
* closure under sums, finite scalings, restrictions, bi-Lipschitz pushforwards, mixtures.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ComplexConjugate

namespace QuantumZipper

theorem admissible_measurable_logNeg_sub (y : ℂ) :
    Measurable fun x : ℂ => ENNReal.ofReal (-Real.log ‖x - y‖) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_log.comp (continuous_norm.comp (continuous_id.sub continuous_const)).measurable).neg

theorem admissible_measurable_logNeg_prod :
    Measurable fun p : ℂ × ℂ => ENNReal.ofReal (-Real.log ‖p.1 - p.2‖) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_log.comp (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable).neg

theorem admissible_ofReal_max_zero (t : ℝ) : ENNReal.ofReal (max 0 t) = ENNReal.ofReal t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

/-- `∫ log⁻ ‖x‖ dx < ∞` over `ℂ`. -/
theorem admissible_lintegral_logNeg_lt_top :
    ∫⁻ x : ℂ, ENNReal.ofReal (-Real.log ‖x‖) < ⊤ := by
  have hind : (fun x : ℂ => ENNReal.ofReal (-Real.log ‖x‖)) =
      (ball (0 : ℂ) 1).indicator (fun x => ENNReal.ofReal (-Real.log ‖x‖)) := by
    funext x
    by_cases hx : x ∈ ball (0 : ℂ) 1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      have : 1 ≤ ‖x‖ := by simpa using hx
      exact ENNReal.ofReal_of_nonpos (by linarith [Real.log_nonneg this])
  have hmeas : Measurable fun x : ℂ => -Real.log ‖x‖ :=
    (Real.measurable_log.comp continuous_norm.measurable).neg
  have hint : IntegrableOn (fun x : ℂ => -Real.log ‖x‖) (ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)
      (by rw [Complex.finrank_real_complex]; norm_num)
      (by rw [Complex.finrank_real_complex]; norm_num) ?_ hmeas.aestronglyMeasurable
    refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : ‖x‖ < 1 := by simpa using hx
    rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
    · rw [← h0, Real.log_zero, neg_zero, norm_zero]
      exact mul_nonneg zero_le_one (Real.rpow_nonneg le_rfl _)
    · rw [Real.rpow_neg_one, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hx1.le)), ← Real.log_inv]
      linarith [Real.log_le_sub_one_of_pos (inv_pos.2 hpos)]
  rw [hind, lintegral_indicator measurableSet_ball]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.2
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

theorem admissible_lintegral_logNeg_sub (y : ℂ) :
    ∫⁻ x : ℂ, ENNReal.ofReal (-Real.log ‖x - y‖) = ∫⁻ x : ℂ, ENNReal.ofReal (-Real.log ‖x‖) :=
  lintegral_sub_right_eq_self (fun x : ℂ => ENNReal.ofReal (-Real.log ‖x‖)) y

/-! ## 1. Bounded densities -/

theorem isAdmissibleH_withDensity {g : ℂ → ℝ≥0∞} (hg : Measurable g) {M : ℝ≥0∞} (hM : M < ⊤)
    (hgM : ∀ x, g x ≤ M) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hgK : ∀ x ∉ K, g x = 0) : IsAdmissibleH (volume.withDensity g) := by
  have hle : ∀ x, g x ≤ K.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]; exact hgM x
    · rw [indicator_of_notMem hx, hgK x hx]
  refine ⟨⟨?_⟩, ⟨K, hK, hKH, ?_⟩, ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ x, g x ≤ ∫⁻ x, K.indicator (fun _ => M) x := lintegral_mono hle
      _ = M * volume K := lintegral_indicator_const hK.measurableSet M
      _ < ⊤ := ENNReal.mul_lt_top hM hK.measure_lt_top
  · rw [withDensity_apply _ hK.measurableSet.compl]
    refine le_antisymm ?_ bot_le
    calc ∫⁻ x in Kᶜ, g x ≤ ∫⁻ x in Kᶜ, K.indicator (fun _ => M) x := lintegral_mono hle
      _ = 0 := by
        rw [lintegral_indicator_const hK.measurableSet, Measure.restrict_apply hK.measurableSet,
          inter_compl_self, measure_empty, mul_zero]
  · refine ⟨M * ∫⁻ x : ℂ, ENNReal.ofReal (-Real.log ‖x‖),
      ENNReal.mul_lt_top hM admissible_lintegral_logNeg_lt_top, fun y => ?_⟩
    rw [lintegral_withDensity_eq_lintegral_mul _ hg (admissible_measurable_logNeg_sub y)]
    calc ∫⁻ x, (g * fun x => ENNReal.ofReal (-Real.log ‖x - y‖)) x
        ≤ ∫⁻ x, M * ENNReal.ofReal (-Real.log ‖x - y‖) := lintegral_mono fun x => by
          simp only [Pi.mul_apply]; gcongr; exact hgM x
      _ = M * ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) :=
          lintegral_const_mul M (admissible_measurable_logNeg_sub y)
      _ = _ := by rw [admissible_lintegral_logNeg_sub]

/-! ## 2. No atoms -/

theorem noAtoms_of_isAdmissibleH {μ : Measure ℂ} (h : IsAdmissibleH μ) (a : ℂ) : μ {a} = 0 := by
  obtain ⟨hfin, -, C, hC, hbd⟩ := h
  have := hfin
  by_contra hne
  have hfin' : μ {a} ≠ ⊤ := measure_ne_top μ _
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hC.ne hne).ne
  set y : ℂ := a - ((Real.exp (-(n : ℝ)) : ℝ) : ℂ) with hy
  have hay : ‖a - y‖ = Real.exp (-(n : ℝ)) := by
    rw [hy, sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have key : (n : ℝ≥0∞) * μ {a} ≤ C := by
    calc (n : ℝ≥0∞) * μ {a} = ∫⁻ x in {a}, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ := by
          rw [lintegral_singleton, hay, Real.log_exp, neg_neg, ENNReal.ofReal_natCast]
      _ ≤ ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ C := hbd y
  have : (n : ℝ≥0∞) ≤ C / μ {a} := (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hfin')).2 key
  exact absurd hn (not_lt.2 this)

/-! ## 3. Integrability of the Green's functions -/

theorem admissible_integrable_of_bound {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) {G : ℂ → ℂ → ℝ} (hG : Measurable fun p : ℂ × ℂ => G p.1 p.2)
    (hbound : ∀ R : ℝ, ∀ x y : ℂ, x ∈ Hbar → y ∈ Hbar → ‖x‖ ≤ R → ‖y‖ ≤ R → x ≠ y →
      |G x y| ≤ 2 * Real.log (max (2 * R) 1) + 2 * max 0 (-Real.log ‖x - y‖)) :
    Integrable (fun p : ℂ × ℂ => G p.1 p.2) (μ.prod ν) := by
  have hatom := noAtoms_of_isAdmissibleH hν
  obtain ⟨hμf, ⟨K1, hK1, hK1H, hK1c⟩, C1, hC1, hbd1⟩ := hμ
  obtain ⟨hνf, ⟨K2, hK2, hK2H, hK2c⟩, C2, hC2, hbd2⟩ := hν
  have := hμf; have := hνf
  obtain ⟨R, hR⟩ := (hK1.union hK2).isBounded.subset_closedBall 0
  set B := Real.log (max (2 * R) 1)
  have hdiag : (μ.prod ν) {p : ℂ × ℂ | p.1 = p.2} = 0 := by
    have hmd : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} := measurableSet_diagonal
    rw [Measure.prod_apply hmd]
    have : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := fun x => by
      ext y; simp [eq_comm]
    simp [this, hatom]
  have h1 : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ K1 := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬ p.1 ∈ K1} = K1ᶜ ×ˢ univ := by ext p; simp
    rw [this, Measure.prod_prod, hK1c, zero_mul]
  have h2 : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ K2 := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬ p.2 ∈ K2} = univ ×ˢ K2ᶜ := by ext p; simp
    rw [this, Measure.prod_prod, hK2c, mul_zero]
  have h3 : ∀ᵐ p ∂(μ.prod ν), p.1 ≠ p.2 := by
    rw [ae_iff]; simp only [ne_eq, not_not]; exact hdiag
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  have hpt : ∀ᵐ p ∂(μ.prod ν), ‖G p.1 p.2‖ₑ ≤
      ENNReal.ofReal (2 * B) + 2 * ENNReal.ofReal (-Real.log ‖p.1 - p.2‖) := by
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    have hxR : ‖p.1‖ ≤ R := mem_closedBall_zero_iff.1 (hR (mem_union_left _ hp1))
    have hyR : ‖p.2‖ ≤ R := mem_closedBall_zero_iff.1 (hR (mem_union_right _ hp2))
    have hb := hbound R p.1 p.2 (hK1H hp1) (hK2H hp2) hxR hyR hp3
    rw [Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |G p.1 p.2|
        ≤ ENNReal.ofReal (2 * B + 2 * max 0 (-Real.log ‖p.1 - p.2‖)) := ENNReal.ofReal_le_ofReal hb
      _ ≤ ENNReal.ofReal (2 * B) + ENNReal.ofReal (2 * max 0 (-Real.log ‖p.1 - p.2‖)) :=
          ENNReal.ofReal_add_le
      _ = _ := by
          congr 1
          rw [ENNReal.ofReal_mul zero_le_two, admissible_ofReal_max_zero, ENNReal.ofReal_ofNat]
  have htonelli : ∫⁻ p, ENNReal.ofReal (-Real.log ‖p.1 - p.2‖) ∂(μ.prod ν) ≤ C2 * μ univ := by
    rw [lintegral_prod _ admissible_measurable_logNeg_prod.aemeasurable]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (-Real.log ‖(x, y).1 - (x, y).2‖) ∂ν ∂μ
        ≤ ∫⁻ _, C2 ∂μ := lintegral_mono fun x => by
          simp only
          simp_rw [norm_sub_rev x]
          exact hbd2 x
      _ = C2 * μ univ := lintegral_const C2
  calc ∫⁻ p, ‖G p.1 p.2‖ₑ ∂(μ.prod ν)
      ≤ ∫⁻ p, (ENNReal.ofReal (2 * B) + 2 * ENNReal.ofReal (-Real.log ‖p.1 - p.2‖)) ∂(μ.prod ν) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * B) * (μ.prod ν) univ +
          2 * ∫⁻ p, ENNReal.ofReal (-Real.log ‖p.1 - p.2‖) ∂(μ.prod ν) := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_const_mul _ admissible_measurable_logNeg_prod]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
        ENNReal.mul_lt_top ENNReal.ofNat_lt_top
          (lt_of_le_of_lt htonelli (ENNReal.mul_lt_top hC2 (measure_lt_top _ _)))⟩

private theorem admissible_log_facts {R : ℝ} {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar)
    (hxR : ‖x‖ ≤ R) (hyR : ‖y‖ ≤ R) (hxy : x ≠ y) :
    Real.log ‖x - y‖ ≤ Real.log ‖x - conj y‖ ∧
      Real.log ‖x - conj y‖ ≤ Real.log (max (2 * R) 1) ∧ 0 ≤ Real.log (max (2 * R) 1) :=
  ⟨le_log_norm_sub_conj_of_ne hx hy hxy,
    log_norm_sub_conj_le_of_compact (K := closedBall 0 R) subset_rfl
      (mem_closedBall_zero_iff.2 hxR) (mem_closedBall_zero_iff.2 hyR),
    Real.log_nonneg (le_max_right _ _)⟩

theorem integrable_greenH_prod {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    Integrable (fun p : ℂ × ℂ => greenH p.1 p.2) (μ.prod ν) := by
  refine admissible_integrable_of_bound hμ hν measurable_greenH ?_
  intro R x y hx hy hxR hyR hxy
  obtain ⟨hab, hb, hB⟩ := admissible_log_facts hx hy hxR hyR hxy
  have m1 := le_max_left 0 (-Real.log ‖x - y‖)
  have m2 := le_max_right 0 (-Real.log ‖x - y‖)
  unfold greenH
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem integrable_neumannH_prod {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) :
    Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2) (μ.prod ν) := by
  refine admissible_integrable_of_bound hμ hν measurable_neumannH ?_
  intro R x y hx hy hxR hyR hxy
  obtain ⟨hab, hb, hB⟩ := admissible_log_facts hx hy hxR hyR hxy
  have m1 := le_max_left 0 (-Real.log ‖x - y‖)
  have m2 := le_max_right 0 (-Real.log ‖x - y‖)
  unfold neumannH
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ## 4. Closure properties -/

theorem isAdmissibleH_add {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    IsAdmissibleH (μ + ν) := by
  obtain ⟨hμf, ⟨K1, hK1, hK1H, hK1c⟩, C1, hC1, hbd1⟩ := hμ
  obtain ⟨hνf, ⟨K2, hK2, hK2H, hK2c⟩, C2, hC2, hbd2⟩ := hν
  have := hμf; have := hνf
  refine ⟨inferInstance, ⟨K1 ∪ K2, hK1.union hK2, union_subset hK1H hK2H, ?_⟩, C1 + C2,
    ENNReal.add_lt_top.2 ⟨hC1, hC2⟩, fun y => ?_⟩
  · rw [Measure.add_apply, compl_union]
    exact add_eq_zero.2 ⟨measure_mono_null inter_subset_left hK1c,
      measure_mono_null inter_subset_right hK2c⟩
  · rw [lintegral_add_measure]; exact add_le_add (hbd1 y) (hbd2 y)

theorem isAdmissibleH_smul {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {c : ℝ≥0∞} (hc : c < ⊤) :
    IsAdmissibleH (c • μ) := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, C, hC, hbd⟩ := hμ
  have := hμf
  refine ⟨⟨?_⟩, ⟨K, hK, hKH, by rw [Measure.smul_apply, hKc, smul_zero]⟩, c * C,
    ENNReal.mul_lt_top hc hC, fun y => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top hc (measure_lt_top μ _)
  · rw [lintegral_smul_measure, smul_eq_mul]; gcongr; exact hbd y

theorem isAdmissibleH_restrict {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (s : Set ℂ) :
    IsAdmissibleH (μ.restrict s) := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, C, hC, hbd⟩ := hμ
  have := hμf
  refine ⟨inferInstance, ⟨K, hK, hKH, ?_⟩, C, hC, fun y =>
    (setLIntegral_le_lintegral _ _).trans (hbd y)⟩
  rw [Measure.restrict_apply hK.measurableSet.compl]
  exact measure_mono_null inter_subset_left hKc

/-! ## 5. Bi-Lipschitz pushforwards -/

theorem isAdmissibleH_map {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {K : Set ℂ} (hK : IsCompact K)
    (hKc : μ Kᶜ = 0) {f : ℂ → ℂ} (hf : Measurable f) (hfc : ContinuousOn f K)
    (hfH : f '' K ⊆ Hbar) {c : ℝ} (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ y ∈ K, c * ‖x - y‖ ≤ ‖f x - f y‖) :
    IsAdmissibleH (μ.map f) := by
  have hatom := noAtoms_of_isAdmissibleH hμ
  obtain ⟨hμf, -, C, hC, hbd⟩ := hμ
  have := hμf
  have hK' : IsCompact (f '' K) := hK.image_of_continuousOn hfc
  refine ⟨inferInstance, ⟨f '' K, hK', hfH, ?_⟩,
    ENNReal.ofReal (-Real.log (c / 2)) * μ univ + C,
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _), hC⟩,
    fun y => ?_⟩
  · rw [Measure.map_apply hf hK'.measurableSet.compl]
    exact measure_mono_null (fun x hx hxK => hx ⟨x, hxK, rfl⟩) hKc
  · rw [lintegral_map (admissible_measurable_logNeg_sub y) hf]
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · rw [hKe, compl_empty] at hKc
      have : μ = 0 := Measure.measure_univ_eq_zero.1 hKc
      simp [this]
    obtain ⟨z, hzK, hzmin⟩ :=
      hK.exists_isMinOn hKne ((hfc.sub continuousOn_const).norm :
        ContinuousOn (fun x => ‖f x - y‖) K)
    have hae : ∀ᵐ x ∂μ, x ∈ K ∧ x ≠ z := by
      have h1 : ∀ᵐ x ∂μ, x ∈ K := ae_iff.2 hKc
      have h2 : ∀ᵐ x ∂μ, x ≠ z := by rw [ae_iff]; simpa using hatom z
      filter_upwards [h1, h2] with x h1 h2 using ⟨h1, h2⟩
    calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖f x - y‖) ∂μ
        ≤ ∫⁻ x, (ENNReal.ofReal (-Real.log (c / 2)) + ENNReal.ofReal (-Real.log ‖x - z‖)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with x hx
          obtain ⟨hxK, hxz⟩ := hx
          by_cases h0 : f x - y = 0
          · rw [h0, norm_zero, Real.log_zero, neg_zero, ENNReal.ofReal_zero]; exact bot_le
          have hmin : ‖f z - y‖ ≤ ‖f x - y‖ := isMinOn_iff.1 hzmin x hxK
          have htri : ‖f x - f z‖ ≤ 2 * ‖f x - y‖ := by
            calc ‖f x - f z‖ = ‖(f x - y) - (f z - y)‖ := by congr 1; ring
              _ ≤ ‖f x - y‖ + ‖f z - y‖ := norm_sub_le _ _
              _ ≤ 2 * ‖f x - y‖ := by linarith
          have hpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
          have hl := hlip x hxK z hzK
          have hlow : c / 2 * ‖x - z‖ ≤ ‖f x - y‖ := by nlinarith
          have hlog : -Real.log ‖f x - y‖ ≤ -Real.log (c / 2) + -Real.log ‖x - z‖ := by
            have := Real.log_le_log (mul_pos (half_pos hc) hpos) hlow
            rw [Real.log_mul (half_pos hc).ne' hpos.ne'] at this
            linarith
          exact (ENNReal.ofReal_le_ofReal hlog).trans ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (-Real.log (c / 2)) * μ univ +
            ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - z‖) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const]
      _ ≤ _ := by gcongr; exact hbd z

/-! ## 6. Mixtures -/

/-- Mixtures of admissible measures with uniform bounds are admissible. (Admissibility of
`ν` itself and of each `κ w` is not needed beyond the listed uniform bounds.) -/
theorem isAdmissibleH_bind {ν : Measure ℂ} [IsFiniteMeasure ν] {K0 : Set ℂ} (hK0c : ν K0ᶜ = 0)
    {κ : ℂ → Measure ℂ} (hκ : ∀ A, MeasurableSet A → Measurable fun w => κ w A)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) {M C : ℝ≥0∞} (hM : M < ⊤) (hC : C < ⊤)
    (hmass : ∀ w ∈ K0, κ w univ ≤ M) (hsupp : ∀ w ∈ K0, κ w Kᶜ = 0)
    (hpot : ∀ w ∈ K0, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂κ w ≤ C) :
    IsAdmissibleH (ν.bind κ) := by
  have hκm : Measurable κ := Measure.measurable_of_measurable_coe κ hκ
  have hae : ∀ᵐ w ∂ν, w ∈ K0 := ae_iff.2 hK0c
  refine ⟨⟨?_⟩, ⟨K, hK, hKH, ?_⟩, C * ν univ, ENNReal.mul_lt_top hC (measure_lt_top _ _),
    fun y => ?_⟩
  · rw [Measure.bind_apply MeasurableSet.univ hκm.aemeasurable]
    calc ∫⁻ w, κ w univ ∂ν ≤ ∫⁻ _, M ∂ν :=
          lintegral_mono_ae (by filter_upwards [hae] with w hw using hmass w hw)
      _ = M * ν univ := lintegral_const M
      _ < ⊤ := ENNReal.mul_lt_top hM (measure_lt_top _ _)
  · rw [Measure.bind_apply hK.measurableSet.compl hκm.aemeasurable]
    refine le_antisymm ?_ bot_le
    calc ∫⁻ w, κ w Kᶜ ∂ν ≤ ∫⁻ _, 0 ∂ν :=
          lintegral_mono_ae (by filter_upwards [hae] with w hw using (hsupp w hw).le)
      _ = 0 := lintegral_zero
  · rw [Measure.lintegral_bind hκm.aemeasurable (admissible_measurable_logNeg_sub y).aemeasurable]
    calc ∫⁻ w, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂κ w ∂ν ≤ ∫⁻ _, C ∂ν :=
          lintegral_mono_ae (by filter_upwards [hae] with w hw using hpot w hw y)
      _ = C * ν univ := lintegral_const C

end QuantumZipper
