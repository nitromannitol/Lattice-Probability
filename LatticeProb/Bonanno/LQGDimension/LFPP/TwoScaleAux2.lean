/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TwoScaleAux2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScaleAux1
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lemma 3.1, auxiliary file 2: segment measures, growth and double integrals

* `integral_toMeasure`: integrals against `SegComb.toMeasure` of a nonnegative combination
  are finite weighted sums of segment integrals.
* `integral_gauss_le_of_growth`: under `GrowthBound α L R`,
  `∫ exp(-|w - z|²/a) dα(z) ≤ 2 L √a / R` (layer cake).
* `nondeg_of_growth`: a growth bound excludes atoms, so every positively weighted segment is
  nondegenerate.
* `pairing`: the generic weighted double sum behind `gaussPair`, `logCov` and `circCov`, with
  its bilinearity under `SegComb.sub`.
* `gaussPair_eq_dbl`: `gaussPair t c c' = ∫∫ kt t (w - z) dc'(z) dc(w)` for nonnegative `c, c'`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.TwoScale

open Blueprint.Draft

/-! ## Segment measures -/

/-- The point with parameter `s` on the segment of `p`. -/
def segPt (p : ℝ × ℂ × ℂ) (s : ℝ) : ℂ := p.2.1 + (s : ℂ) * (p.2.2 - p.2.1)

lemma continuous_segPt (p : ℝ × ℂ × ℂ) : Continuous (segPt p) := by
  unfold segPt; fun_prop

/-- The uniform probability measure on the segment of `p`. -/
def segMeas (p : ℝ × ℂ × ℂ) : Measure ℂ := (volume.restrict (Icc (0 : ℝ) 1)).map (segPt p)

instance isProbabilityMeasure_restrict_Icc01 :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

instance (p : ℝ × ℂ × ℂ) : IsProbabilityMeasure (segMeas p) := by
  unfold segMeas; infer_instance

lemma toMeasure_nil : SegComb.toMeasure [] = 0 := by
  simp [SegComb.toMeasure]

lemma toMeasure_cons (p : ℝ × ℂ × ℂ) (c : SegComb) :
    SegComb.toMeasure (p :: c) = ENNReal.ofReal p.1 • segMeas p + SegComb.toMeasure c := by
  simp only [SegComb.toMeasure, List.map_cons, List.sum_cons]
  rfl

instance isFiniteMeasure_toMeasure (c : SegComb) : IsFiniteMeasure c.toMeasure := by
  induction c with
  | nil => rw [toMeasure_nil]; infer_instance
  | cons p c ih =>
    rw [toMeasure_cons]
    constructor
    rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ (μ := segMeas p), mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, measure_lt_top _ _⟩

lemma mass_cons (p : ℝ × ℂ × ℂ) (c : SegComb) : SegComb.mass (p :: c) = p.1 + c.mass := by
  simp [SegComb.mass]

lemma toMeasure_real_univ (c : SegComb) (hc : ∀ p ∈ c, 0 ≤ p.1) :
    c.toMeasure.real univ = c.mass := by
  induction c with
  | nil => simp [toMeasure_nil, SegComb.mass]
  | cons p c ih =>
    have hp := hc p (by simp)
    have ih' := ih (fun q hq => hc q (by simp [hq]))
    rw [toMeasure_cons, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ (μ := segMeas p), mul_one, ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),
      ENNReal.toReal_ofReal hp, ← measureReal_def, ih', mass_cons]

lemma integral_segMeas (p : ℝ × ℂ × ℂ) (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (segMeas p) ∧ ∫ z, f z ∂segMeas p = ∫ s in Ioc (0 : ℝ) 1, f (segPt p s) := by
  have hm : AEMeasurable (segPt p) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (continuous_segPt p).aemeasurable
  have hcomp : Continuous (fun s => f (segPt p s)) := hf.comp (continuous_segPt p)
  refine ⟨?_, ?_⟩
  · unfold segMeas
    rw [integrable_map_measure hf.aestronglyMeasurable hm]
    exact hcomp.integrableOn_Icc
  · unfold segMeas
    rw [integral_map hm hf.aestronglyMeasurable, integral_Icc_eq_integral_Ioc]

/-- Integrals against a nonnegative segment combination. -/
lemma integral_toMeasure (c : SegComb) (hc : ∀ p ∈ c, 0 ≤ p.1) (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f c.toMeasure ∧ ∫ z, f z ∂c.toMeasure =
      (c.map fun p => p.1 * ∫ s in Ioc (0 : ℝ) 1, f (segPt p s)).sum := by
  induction c with
  | nil => simp [toMeasure_nil]
  | cons p c ih =>
    have hp := hc p (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun q hq => hc q (by simp [hq]))
    obtain ⟨h1, h2⟩ := integral_segMeas p f hf
    have h1' : Integrable f (ENNReal.ofReal p.1 • segMeas p) :=
      h1.smul_measure ENNReal.ofReal_ne_top
    rw [toMeasure_cons]
    refine ⟨h1'.add_measure ih1, ?_⟩
    rw [integral_add_measure h1' ih1, integral_smul_measure, ih2, h2, ENNReal.toReal_ofReal hp,
      smul_eq_mul]
    simp

/-! ## The Gaussian kernel against finite measures -/

lemma kt_le_one (t : ℝ) (x : ℂ) : kt t x ≤ 1 := by
  unfold kt; rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

lemma continuous_kt (t : ℝ) : Continuous (kt t) := by
  unfold kt; fun_prop

lemma continuous_et (t : ℝ) : Continuous (et t) := by
  unfold et; fun_prop

lemma continuous_integral_kt (t : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Continuous fun w => ∫ z, kt t (w - z) ∂μ :=
  continuous_of_dominated (bound := fun _ => 1)
    (fun _ => ((continuous_kt t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun _ => ae_of_all _ fun _ => by
      rw [Real.norm_eq_abs, abs_of_pos (kt_pos t _)]; exact kt_le_one t _)
    (integrable_const 1)
    (ae_of_all _ fun _ => (continuous_kt t).comp (continuous_id.sub continuous_const))

/-- The double integral `∫∫ kt(w - z) dα(z) dβ(w)`. -/
def dbl (t : ℝ) (β α : Measure ℂ) : ℝ := ∫ w, ∫ z, kt t (w - z) ∂α ∂β

/-! ## Weighted double sums -/

/-- The weighted double sum `Σ_{p ∈ c} Σ_{p' ∈ c'} w_p w_{p'} F(seg p, seg p')`. -/
def pairing (F : ℂ × ℂ → ℂ × ℂ → ℝ) (c c' : SegComb) : ℝ :=
  (c.map fun p => (c'.map fun p' => p.1 * p'.1 * F p.2 p'.2).sum).sum

lemma list_sum_map_neg' {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_sum_map_sub' {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_sum_map_add' {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma list_sum_map_mul_left' {α : Type*} (l : List α) (f : α → ℝ) (r : ℝ) :
    (l.map fun x => r * f x).sum = r * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma pairing_sub_left (F : ℂ × ℂ → ℂ × ℂ → ℝ) (a b c : SegComb) :
    pairing F (a.sub b) c = pairing F a c - pairing F b c := by
  unfold pairing SegComb.sub
  rw [List.map_append, List.sum_append, List.map_map]
  have : ((fun p : ℝ × ℂ × ℂ => (c.map fun p' => p.1 * p'.1 * F p.2 p'.2).sum) ∘
      fun p : ℝ × ℂ × ℂ => (-p.1, p.2)) =
      fun p => -(c.map fun p' => p.1 * p'.1 * F p.2 p'.2).sum := by
    funext p
    simp only [Function.comp_apply, neg_mul]
    exact list_sum_map_neg' c _
  rw [this, list_sum_map_neg']
  ring

lemma pairing_sub_right (F : ℂ × ℂ → ℂ × ℂ → ℝ) (a c d : SegComb) :
    pairing F a (c.sub d) = pairing F a c - pairing F a d := by
  unfold pairing SegComb.sub
  rw [← list_sum_map_sub']
  congr 1
  apply List.map_congr_left
  intro p _
  rw [List.map_append, List.sum_append, List.map_map]
  have : ((fun p' : ℝ × ℂ × ℂ => p.1 * p'.1 * F p.2 p'.2) ∘
      fun p' : ℝ × ℂ × ℂ => (-p'.1, p'.2)) =
      fun p' => -(p.1 * p'.1 * F p.2 p'.2) := by
    funext p'
    simp only [Function.comp_apply]
    ring
  rw [this, list_sum_map_neg']
  ring

lemma pairing_sub_sub (F : ℂ × ℂ → ℂ × ℂ → ℝ) (a b c d : SegComb) :
    pairing F (a.sub b) (c.sub d) =
      pairing F a c - pairing F a d - pairing F b c + pairing F b d := by
  rw [pairing_sub_left, pairing_sub_right, pairing_sub_right]; ring

lemma mass_sub (a b : SegComb) : (a.sub b).mass = a.mass - b.mass := by
  unfold SegComb.mass SegComb.sub
  rw [List.map_append, List.sum_append, List.map_map]
  have : ((fun p : ℝ × ℂ × ℂ => p.1) ∘ fun p : ℝ × ℂ × ℂ => (-p.1, p.2)) = fun p => -p.1 := by
    funext p; rfl
  rw [this, list_sum_map_neg']
  ring

/-- `gaussPair` as a `pairing`. -/
lemma gaussPair_eq_pairing (t : ℝ) (c c' : SegComb) :
    gaussPair t c c' = pairing (fun x y => ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1,
      Real.exp (-‖(x.1 + (s : ℂ) * (x.2 - x.1)) - (y.1 + (s' : ℂ) * (y.2 - y.1))‖ ^ 2
        / (4 * t ^ 2))) c c' := rfl

/-- `logCov` as a `pairing`. -/
lemma logCov_eq_pairing (c c' : SegComb) :
    c.logCov c' = pairing (fun x y => segLogPair x.1 x.2 y.1 y.2) c c' := rfl

lemma gaussPair_sub_sub (t : ℝ) (a b c d : SegComb) :
    gaussPair t (a.sub b) (c.sub d) =
      gaussPair t a c - gaussPair t a d - gaussPair t b c + gaussPair t b d := by
  simp only [gaussPair_eq_pairing]; exact pairing_sub_sub _ a b c d

/-! ## `gaussPair` as a double integral -/

lemma continuous_segInt (t : ℝ) (p' : ℝ × ℂ × ℂ) :
    Continuous fun y => ∫ s' in Ioc (0 : ℝ) 1, kt t (y - segPt p' s') := by
  have h : (fun y => ∫ s' in Ioc (0 : ℝ) 1, kt t (y - segPt p' s')) =
      fun y => ∫ z, kt t (y - z) ∂segMeas p' := by
    funext y
    exact ((integral_segMeas p' _ ((continuous_kt t).comp
      (continuous_const.sub continuous_id))).2).symm
  rw [h]
  exact continuous_integral_kt t (segMeas p')

/-- For nonnegative combinations, `gaussPair t c c' = ∫∫ kt(w - z) dc'(z) dc(w)`. -/
lemma gaussPair_eq_dbl (t : ℝ) (c c' : SegComb) (hc : ∀ p ∈ c, 0 ≤ p.1)
    (hc' : ∀ p ∈ c', 0 ≤ p.1) :
    gaussPair t c c' = dbl t c.toMeasure c'.toMeasure := by
  have hH : ∀ w, ∫ z, kt t (w - z) ∂c'.toMeasure =
      (c'.map fun p' => p'.1 * ∫ s' in Ioc (0 : ℝ) 1, kt t (w - segPt p' s')).sum :=
    fun w => (integral_toMeasure c' hc' _ ((continuous_kt t).comp
      (continuous_const.sub continuous_id))).2
  unfold dbl
  rw [(integral_toMeasure c hc _ (continuous_integral_kt t c'.toMeasure)).2]
  unfold gaussPair
  simp only [intervalIntegral.integral_of_le zero_le_one]
  congr 1
  apply List.map_congr_left
  intro p _
  simp_rw [hH]
  have hint : ∀ p' ∈ c', Integrable (fun s => p'.1 *
      ∫ s' in Ioc (0 : ℝ) 1, kt t (segPt p s - segPt p' s')) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro p' _
    have hcont : Continuous fun s => p'.1 *
        ∫ s' in Ioc (0 : ℝ) 1, kt t (segPt p s - segPt p' s') :=
      continuous_const.mul ((continuous_segInt t p').comp (continuous_segPt p))
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [(HeatKernel.integral_list_sum_map c' _ hint).2, ← list_sum_map_mul_left']
  congr 1
  apply List.map_congr_left
  intro p' _
  rw [integral_const_mul]
  simp only [kt, segPt]
  ring

/-! ## The growth integral -/

lemma growth_L_nonneg {α : Measure ℂ} {L R : ℝ} (hR : 0 < R) (hG : GrowthBound α L R) :
    0 ≤ L := by
  have h := hG 0 R hR
  rw [div_self hR.ne', min_self, mul_one] at h
  exact le_trans ENNReal.toReal_nonneg h

/-- **Growth integral** (layer cake): under `GrowthBound α L R`,
`∫ exp(-|w - z|²/a) dα(z) ≤ 2 L √a / R`. -/
theorem integral_gauss_le_of_growth (α : Measure ℂ) [IsFiniteMeasure α] {L R : ℝ} (hR : 0 < R)
    (hG : GrowthBound α L R) {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ∫ z, Real.exp (-‖w - z‖ ^ 2 / a) ∂α ≤ 2 * L * Real.sqrt a / R := by
  have hL := growth_L_nonneg hR hG
  set f : ℂ → ℝ := fun z => Real.exp (-‖w - z‖ ^ 2 / a) with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  have hf1 : ∀ z, f z ≤ 1 := fun z => by
    rw [hf]; simp only; rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) ha.le
  have hint : Integrable f α := Integrable.of_bound hfc.aestronglyMeasurable 1
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hf1 z)
  rw [hint.integral_eq_integral_meas_lt (ae_of_all _ fun z => (Real.exp_pos _).le)]
  set C := L * Real.sqrt a / R with hC
  set g : ℝ → ℝ := Set.indicator (Ioc 0 1) (fun l => C * l ^ (-(1 / 2 : ℝ))) with hg
  have hgi : Integrable g (volume.restrict (Ioi 0)) := by
    rw [hg, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self]
    exact ((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 2))).1).const_mul C
  have hbound : ∀ᵐ l ∂(volume.restrict (Ioi (0 : ℝ))), α.real {z | l < f z} ≤ g l := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    have hl0 : 0 < l := hl
    rcases le_or_gt l 1 with hl1 | hl1
    · rw [hg, Set.indicator_of_mem (show l ∈ Ioc (0 : ℝ) 1 from ⟨hl0, hl1⟩)]
      have hsub : {z | l < f z} ⊆ Metric.ball w (Real.sqrt (a / l)) := by
        intro z hz
        simp only [mem_ofPred_eq, hf] at hz
        rw [Metric.mem_ball, dist_comm, dist_eq_norm]
        have hd := norm_nonneg (w - z)
        have h1 := Real.add_one_le_exp (‖w - z‖ ^ 2 / a)
        have h2 : Real.exp (-‖w - z‖ ^ 2 / a) * Real.exp (‖w - z‖ ^ 2 / a) = 1 := by
          rw [← Real.exp_add, ← Real.exp_zero]; congr 1; ring
        have h3 : l * Real.exp (‖w - z‖ ^ 2 / a) < 1 := by
          calc l * Real.exp (‖w - z‖ ^ 2 / a)
              < Real.exp (-‖w - z‖ ^ 2 / a) * Real.exp (‖w - z‖ ^ 2 / a) :=
                mul_lt_mul_of_pos_right hz (Real.exp_pos _)
            _ = 1 := h2
        have h4 : l * (‖w - z‖ ^ 2 / a + 1) ≤ l * Real.exp (‖w - z‖ ^ 2 / a) :=
          mul_le_mul_of_nonneg_left h1 hl0.le
        have h5 : l * (‖w - z‖ ^ 2 / a) < 1 := by nlinarith
        rw [← mul_div_assoc, div_lt_one ha] at h5
        rw [Real.lt_sqrt hd, lt_div_iff₀ hl0]
        linarith
      have hr : 0 < Real.sqrt (a / l) := Real.sqrt_pos.2 (div_pos ha hl0)
      calc α.real {z | l < f z} ≤ α.real (Metric.ball w (Real.sqrt (a / l))) :=
            measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ L * min 1 (Real.sqrt (a / l) / R) := hG w _ hr
        _ ≤ L * (Real.sqrt (a / l) / R) := mul_le_mul_of_nonneg_left (min_le_right _ _) hL
        _ = C * l ^ (-(1 / 2 : ℝ)) := by
            rw [hC, Real.sqrt_div' a hl0.le, Real.rpow_neg hl0.le, Real.sqrt_eq_rpow l]
            ring
    · rw [hg, Set.indicator_of_notMem (show l ∉ Ioc (0 : ℝ) 1 from fun h => by linarith [h.2])]
      have : {z | l < f z} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hf1 z).trans hl1.le
      rw [this, measureReal_empty]
  calc ∫ l in Ioi 0, α.real {z | l < f z} ≤ ∫ l in Ioi 0, g l :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => measureReal_nonneg) hgi hbound
    _ = 2 * L * Real.sqrt a / R := by
        rw [hg, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self,
          ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
          integral_rpow (r := -(1 / 2)) (Or.inl (by norm_num)),
          show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, Real.one_rpow,
          Real.zero_rpow (one_div_ne_zero two_ne_zero), hC]
        ring

/-! ## Growth excludes atoms -/

lemma segMeas_le_toMeasure (c : SegComb) (p : ℝ × ℂ × ℂ) (hp : p ∈ c) (S : Set ℂ) :
    ENNReal.ofReal p.1 * segMeas p S ≤ c.toMeasure S := by
  induction c with
  | nil => simp at hp
  | cons q c ih =>
    rw [toMeasure_cons, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact le_self_add
    · exact le_add_left (ih hp')

/-- A growth bound excludes atoms: positively weighted segments are nondegenerate. -/
lemma nondeg_of_growth (c : SegComb) {L R : ℝ} (hR : 0 < R) (hG : GrowthBound c.toMeasure L R) :
    ∀ p ∈ c, 0 < p.1 → p.2.1 ≠ p.2.2 := by
  intro p hp hpos heq
  have hL := growth_L_nonneg hR hG
  have hball : ∀ r > 0, p.1 ≤ L * (r / R) := by
    intro r hr
    have h1 : segMeas p (Metric.ball p.2.1 r) = 1 := by
      unfold segMeas
      rw [Measure.map_apply (continuous_segPt p).measurable Metric.isOpen_ball.measurableSet]
      have : segPt p ⁻¹' Metric.ball p.2.1 r = univ := by
        ext s
        simp [segPt, heq, hr]
      rw [this, Measure.restrict_apply_univ, Real.volume_Icc]
      simp
    have h2 := segMeas_le_toMeasure c p hp (Metric.ball p.2.1 r)
    rw [h1, mul_one] at h2
    have h3 : p.1 ≤ (c.toMeasure (Metric.ball p.2.1 r)).toReal := by
      rw [← ENNReal.toReal_ofReal hpos.le]
      exact ENNReal.toReal_mono (measure_ne_top _ _) h2
    exact h3.trans ((hG _ r hr).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hL))
  have h := hball (p.1 * R / (2 * (L + 1))) (by positivity)
  have hRne : R ≠ 0 := hR.ne'
  have hL1 : 2 * (L + 1) ≠ 0 := by positivity
  have h4 : L * (p.1 * R / (2 * (L + 1)) / R) = p.1 * (L / (2 * (L + 1))) := by
    field_simp
  have h5 : L / (2 * (L + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  rw [h4] at h
  nlinarith

/-- Nondegeneracy of a difference of nonnegative combinations. -/
lemma nondeg_sub (a b : SegComb) (ha : ∀ p ∈ a, 0 ≤ p.1) (hb : ∀ p ∈ b, 0 ≤ p.1)
    (ha' : ∀ p ∈ a, 0 < p.1 → p.2.1 ≠ p.2.2) (hb' : ∀ p ∈ b, 0 < p.1 → p.2.1 ≠ p.2.2) :
    (a.sub b).Nondeg := by
  intro p hp hp0
  simp only [SegComb.sub, List.mem_append, List.mem_map] at hp
  rcases hp with hp | ⟨q, hq, rfl⟩
  · exact ha' p hp (lt_of_le_of_ne (ha p hp) (Ne.symm hp0))
  · refine hb' q hq (lt_of_le_of_ne (hb q hq) (fun h => hp0 ?_))
    simp [← h]

end LQGDimension.TwoScale
