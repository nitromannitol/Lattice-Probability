/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29WN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Third
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

/-!
# DDDF Proposition 29: the white-noise kernel of the zero-boundary GFF on a square (R2, part 1)

DDDF = arXiv:1904.08021, `tightness.tex`, §"White noise representation" (DD:1514–1525):
`h(ρ) = √π ∫_0^∞ ∫_D (∫ ρ(y') p^D_{s/2}(y', y) dy') W(dy, ds)`. Here `D = (a, a+L)²` and
`p^D = HeatSq.sqDirKernel`. This file builds the kernel

  `zbKerFun a L ρ (s, y) = 1_{s>0} 1_D(y) ∫ ρ(y') p^D_{s/2}(y', y) dy'`

and shows it is in `L²(ℝ × ℂ)` (`memLp_zbKerFun`) for `ρ` bounded measurable vanishing off `D`:
`|∫ ρ p^D_{s/2}| ≤ 4C` (`HeatSq.lintegral_abs_sqDirKernel_le`) and `≤ C L² K² e^{−c s}` for
`s ≥ 2` (`HeatSq.abs_intervalDirKernel_le_exp`). Own elementary bookkeeping (the paper takes
the representation for granted).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq

variable {a L : ℝ}

lemma measurable_gauss1_joint : Measurable fun p : ℝ × ℝ => gauss1 p.1 p.2 := by
  unfold gauss1; fun_prop

lemma measurable_tsum_gauss1_joint {α : Type*} [MeasurableSpace α] (L : ℝ) {s c : α → ℝ}
    (hs : Measurable s) (hc : Measurable c) :
    Measurable (fun u => ∑' n : ℤ, gauss1 (s u) (c u + 2 * n * L)) := by
  have e : (fun u => ∑' n : ℤ, gauss1 (s u) (c u + 2 * n * L)) =
      fun u => (∑' n : ℤ, ENNReal.ofReal (gauss1 (s u) (c u + 2 * n * L))).toReal := by
    funext u
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp [ENNReal.toReal_ofReal (gauss1_nonneg _ _)]
  rw [e]
  refine (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp ?_).ennreal_toReal
  exact measurable_gauss1_joint.comp (hs.prodMk (hc.add_const _))

/-- joint measurability of `(s, y', y) ↦ 1_{s>0} p^D_s(y', y)` -/
lemma measurable_sqDirKernel_joint (hL : 0 < L) {α : Type*} [MeasurableSpace α] {s : α → ℝ}
    {f g : α → ℂ} (hs : Measurable s) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => if 0 < s p then sqDirKernel a L (s p) (f p) (g p) else 0) := by
  have e : (fun p => if 0 < s p then sqDirKernel a L (s p) (f p) (g p) else 0) = fun p =>
      if 0 < s p then
        ((∑' n : ℤ, gauss1 (s p) ((f p).re - (g p).re + 2 * n * L)) -
          ∑' n : ℤ, gauss1 (s p) ((f p).re + (g p).re - 2 * a + 2 * n * L)) *
        ((∑' n : ℤ, gauss1 (s p) ((f p).im - (g p).im + 2 * n * L)) -
          ∑' n : ℤ, gauss1 (s p) ((f p).im + (g p).im - 2 * a + 2 * n * L))
      else 0 := by
    funext p
    split_ifs with h
    · rw [sqDirKernel, intervalDirKernel_eq_sub h hL, intervalDirKernel_eq_sub h hL]
    · rfl
  rw [e]
  have hr := Complex.measurable_re.comp hf
  have hr' := Complex.measurable_re.comp hg
  have hi := Complex.measurable_im.comp hf
  have hi' := Complex.measurable_im.comp hg
  refine Measurable.ite (measurableSet_lt measurable_const hs) ?_ measurable_const
  exact ((measurable_tsum_gauss1_joint L hs (hr.sub hr')).sub
    (measurable_tsum_gauss1_joint L hs ((hr.add hr').sub_const _))).mul
    ((measurable_tsum_gauss1_joint L hs (hi.sub hi')).sub
    (measurable_tsum_gauss1_joint L hs ((hi.add hi').sub_const _)))

/-- DDDF's white-noise kernel of the zero-boundary GFF on `D = (a, a+L)²` (DD:1514):
`(s, y) ↦ 1_{s>0} 1_D(y) ∫ ρ(y') p^D_{s/2}(y', y) dy'` -/
def zbKerFun (a L : ℝ) (ρ : ℂ → ℝ) (q : ℝ × ℂ) : ℝ :=
  (Ioi 0 ×ˢ sqOpen a L).indicator (fun q => ∫ y', ρ y' * sqDirKernel a L (q.1 / 2) y' q.2) q

lemma measurable_zbKerFun (hL : 0 < L) {ρ : ℂ → ℝ} (hρ : Measurable ρ) :
    Measurable (zbKerFun a L ρ) := by
  have hF : StronglyMeasurable (Function.uncurry fun (q : ℝ × ℂ) (y' : ℂ) =>
      ρ y' * (if 0 < q.1 / 2 then sqDirKernel a L (q.1 / 2) y' q.2 else 0)) := by
    refine Measurable.stronglyMeasurable ?_
    exact (hρ.comp measurable_snd).mul (measurable_sqDirKernel_joint (a := a) hL
      ((measurable_fst.comp measurable_fst).div_const 2) measurable_snd
      (measurable_snd.comp measurable_fst))
  have hG := (hF.integral_prod_right (ν := (volume : Measure ℂ))).measurable
  have e : zbKerFun a L ρ = (Ioi 0 ×ˢ sqOpen a L).indicator (fun q : ℝ × ℂ =>
      ∫ y', ρ y' * (if 0 < q.1 / 2 then sqDirKernel a L (q.1 / 2) y' q.2 else 0)) := by
    funext q
    unfold zbKerFun
    by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
    · have h2 : 0 < q.1 / 2 := half_pos hq.1
      simp only [indicator_of_mem hq, if_pos h2]
    · simp only [indicator_of_notMem hq]
  rw [e]
  exact hG.indicator ((measurableSet_Ioi).prod (measurableSet_sqOpen a L))

lemma nonneg_of_abs_le {ρ : ℂ → ℝ} {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) : 0 ≤ C :=
  (abs_nonneg _).trans (hC 0)

/-- `|∫ ρ(y') p^D_s(y', y) dy'| ≤ 4C` -/
lemma abs_integral_mul_sqDirKernel_le (hL : 0 < L) {ρ : ℂ → ℝ} {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) {s : ℝ} (hs : 0 < s) (y : ℂ) :
    |∫ y', ρ y' * sqDirKernel a L s y' y| ≤ 4 * C := by
  have hC0 := nonneg_of_abs_le hC
  have hl : ∫⁻ y', ENNReal.ofReal ‖ρ y' * sqDirKernel a L s y' y‖ ≤ ENNReal.ofReal C * 4 := by
    calc ∫⁻ y', ENNReal.ofReal ‖ρ y' * sqDirKernel a L s y' y‖
        ≤ ∫⁻ y', (sqOpen a L).indicator
            (fun y' => ENNReal.ofReal C * ENNReal.ofReal |sqDirKernel a L s y y'|) y' := by
          refine lintegral_mono fun y' => ?_
          by_cases hy : y' ∈ sqOpen a L
          · rw [indicator_of_mem hy, ← ENNReal.ofReal_mul hC0, Real.norm_eq_abs, abs_mul,
              sqDirKernel_symm hs hL]
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (hC y') (abs_nonneg _))
          · rw [h0 y' hy]; simp
      _ = ENNReal.ofReal C * ∫⁻ y' in sqOpen a L, ENNReal.ofReal |sqDirKernel a L s y y'| := by
          rw [lintegral_indicator (measurableSet_sqOpen a L), lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp (measurable_sqDirKernel_right' hs hL y))
      _ ≤ ENNReal.ofReal C * 4 := by gcongr; exact lintegral_abs_sqDirKernel_le hs hL y
  calc |∫ y', ρ y' * sqDirKernel a L s y' y| ≤ _ :=
      (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_lintegral_norm _)
    _ ≤ (ENNReal.ofReal C * 4).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)) hl
    _ = 4 * C := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0]; simp; ring

/-- the decay rate `c = π²/(2L²)` of the first Dirichlet mode -/
def rateC (L : ℝ) : ℝ := π ^ 2 / (2 * L ^ 2)

lemma abs_sqDirKernel_le_exp (hL : 0 < L) {s : ℝ} (hs : 1 ≤ s) (y' y : ℂ) :
    |sqDirKernel a L s y' y| ≤ decayConst L 1 ^ 2 * Real.exp (-(2 * rateC L) * s) := by
  rw [sqDirKernel, abs_mul]
  have h1 := abs_intervalDirKernel_le_exp (a := a) hL one_pos hs y'.re y.re
  have h2 := abs_intervalDirKernel_le_exp (a := a) hL one_pos hs y'.im y.im
  calc _ ≤ (decayConst L 1 * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s)) *
        (decayConst L 1 * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s)) :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = _ := by
      rw [rateC, show -(2 * (π ^ 2 / (2 * L ^ 2))) * s =
        -(π ^ 2 / (2 * L ^ 2)) * s + -(π ^ 2 / (2 * L ^ 2)) * s by ring, Real.exp_add]; ring

/-- `|∫ ρ(y') p^D_s(y', y) dy'| ≤ C L² K² e^{−2cs}` for `s ≥ 1` -/
lemma abs_integral_mul_sqDirKernel_le_exp (hL : 0 < L) {ρ : ℂ → ℝ} {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) {s : ℝ} (hs : 1 ≤ s) (y : ℂ) :
    |∫ y', ρ y' * sqDirKernel a L s y' y| ≤
      C * L ^ 2 * (decayConst L 1 ^ 2 * Real.exp (-(2 * rateC L) * s)) := by
  have hC0 := nonneg_of_abs_le hC
  set B := decayConst L 1 ^ 2 * Real.exp (-(2 * rateC L) * s) with hB
  have hB0 : 0 ≤ B := by positivity
  have hl : ∫⁻ y', ENNReal.ofReal ‖ρ y' * sqDirKernel a L s y' y‖ ≤
      ENNReal.ofReal (C * B) * ENNReal.ofReal (L ^ 2) := by
    calc ∫⁻ y', ENNReal.ofReal ‖ρ y' * sqDirKernel a L s y' y‖
        ≤ ∫⁻ y', (sqOpen a L).indicator (fun _ => ENNReal.ofReal (C * B)) y' := by
          refine lintegral_mono fun y' => ?_
          by_cases hy : y' ∈ sqOpen a L
          · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul (hC y')
              (abs_sqDirKernel_le_exp hL hs y' y) (abs_nonneg _) hC0)
          · rw [h0 y' hy]; simp
      _ = _ := by
          rw [lintegral_indicator (measurableSet_sqOpen a L), setLIntegral_const,
            volume_sqOpen a L hL.le]
  calc |∫ y', ρ y' * sqDirKernel a L s y' y| ≤ _ :=
      (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_lintegral_norm _)
    _ ≤ (ENNReal.ofReal (C * B) * ENNReal.ofReal (L ^ 2)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hl
    _ = C * L ^ 2 * B := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity)]; ring

/-- the constant of the bound `|zbKerFun ρ (s, y)| ≤ M e^{−cs/2}` -/
def kerConst (L C : ℝ) : ℝ := 4 * C * Real.exp (rateC L) + C * L ^ 2 * decayConst L 1 ^ 2

lemma abs_zbKerFun_le (hL : 0 < L) {ρ : ℂ → ℝ} {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) (q : ℝ × ℂ) :
    |zbKerFun a L ρ q| ≤ (Ioi 0 ×ˢ sqOpen a L).indicator
      (fun q => kerConst L C * Real.exp (-rateC L * (q.1 / 2))) q := by
  have hC0 := nonneg_of_abs_le hC
  have hc0 : 0 < rateC L := by unfold rateC; positivity
  unfold zbKerFun
  by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
  · rw [indicator_of_mem hq, indicator_of_mem hq]
    have hs : 0 < q.1 / 2 := half_pos hq.1
    have hK1 : 0 ≤ C * L ^ 2 * decayConst L 1 ^ 2 := by positivity
    have hE : 0 ≤ 4 * C * Real.exp (rateC L) := by positivity
    rcases le_or_gt (q.1 / 2) 1 with h1 | h1
    · calc _ ≤ 4 * C := abs_integral_mul_sqDirKernel_le hL hC h0 hs q.2
        _ ≤ 4 * C * Real.exp (rateC L) * Real.exp (-rateC L * (q.1 / 2)) := by
          rw [mul_assoc, ← Real.exp_add]
          have : 1 ≤ Real.exp (rateC L + -rateC L * (q.1 / 2)) :=
            Real.one_le_exp (by nlinarith)
          nlinarith
        _ ≤ _ := by unfold kerConst; nlinarith [Real.exp_pos (-rateC L * (q.1 / 2))]
    · calc _ ≤ C * L ^ 2 * (decayConst L 1 ^ 2 * Real.exp (-(2 * rateC L) * (q.1 / 2))) :=
            abs_integral_mul_sqDirKernel_le_exp hL hC h0 h1.le q.2
        _ ≤ C * L ^ 2 * decayConst L 1 ^ 2 * Real.exp (-rateC L * (q.1 / 2)) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hK1
        _ ≤ _ := by unfold kerConst; nlinarith [Real.exp_pos (-rateC L * (q.1 / 2))]
  · rw [indicator_of_notMem hq, indicator_of_notMem hq, abs_zero]

/-- **The kernel is in `L²(ℝ × ℂ)`.** -/
theorem memLp_zbKerFun (hL : 0 < L) {ρ : ℂ → ℝ} (hρm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) :
    MemLp (zbKerFun a L ρ) 2 (volume : Measure (ℝ × ℂ)) := by
  have hm := (measurable_zbKerFun (a := a) hL hρm).aestronglyMeasurable (μ := volume)
  have hc0 : 0 < rateC L := by unfold rateC; positivity
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  set g : ℝ × ℂ → ℝ := fun q => (Ioi (0 : ℝ)).indicator
    (fun s => kerConst L C ^ 2 * Real.exp (-rateC L * s)) q.1 *
      (sqOpen a L).indicator (fun _ => (1 : ℝ)) q.2 with hg
  have hgi : Integrable g (volume : Measure (ℝ × ℂ)) := by
    rw [Measure.volume_eq_prod]
    refine Integrable.mul_prod ?_ ?_
    · exact IntegrableOn.integrable_indicator ((exp_neg_integrableOn_Ioi 0 hc0).const_mul _)
        measurableSet_Ioi
    · exact (integrableOn_const (volume_sqOpen_ne_top a L)).integrable_indicator
        (measurableSet_sqOpen a L)
  refine hgi.mono' (hm.pow 2) (Filter.Eventually.of_forall fun q => ?_)
  have hb := abs_zbKerFun_le (a := a) hL hC h0 q
  rw [Real.norm_eq_abs, abs_pow]
  by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
  · rw [indicator_of_mem hq] at hb
    simp only [hg, indicator_of_mem hq.1, indicator_of_mem hq.2, mul_one]
    calc |zbKerFun a L ρ q| ^ 2 ≤ (kerConst L C * Real.exp (-rateC L * (q.1 / 2))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  · rw [indicator_of_notMem hq] at hb
    have : |zbKerFun a L ρ q| = 0 := le_antisymm hb (abs_nonneg _)
    rw [this, zero_pow two_ne_zero]
    exact mul_nonneg (indicator_nonneg (fun s _ => by positivity) _)
      (indicator_nonneg (fun _ _ => zero_le_one) _)

end P29WN
end DDDF
end LQGMetric
