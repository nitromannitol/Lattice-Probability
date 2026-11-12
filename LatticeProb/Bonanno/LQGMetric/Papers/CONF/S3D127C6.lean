/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4(c) replaced, part 2: continuity of `P^U_h f` and of the Green potential on `U`
(packet P-127C)

* `integral_killedHeat_add_mul` (semigroup property against bounded `f`, Chapman–Kolmogorov and
  Fubini);
* `abs_killedConv_sub_heatConv_le`: `|∫ p_U(ε; x, ·) g − ∫ p_ε(x, ·) g| ≤ M · err(d, ε)` when
  `B(x, d) ⊆ U`, `|g| ≤ M`;
* `continuousOn_killedConv`: `x ↦ ∫ p_U(h; x, w) f(w) dw` is continuous on `U` (open `U`,
  bounded measurable `f`): it is a locally uniform limit, as `ε → 0`, of the continuous heat
  convolutions `x ↦ ∫ p_ε(x, v) (P^U_{h−ε} f)(v) dv` (the classical argument that interior
  continuity of the killed semigroup needs no boundary regularity; own elementary
  implementation, DV-P127C-2);
* `continuousOn_greenPot`: `x ↦ ∫ G_U(x, y) ρ(y) dy` is continuous on `U` for bounded open `U` and
  bounded measurable `ρ` (dominated convergence in `s`, with `|P^U_s ρ| ≤ M min(1, R⁴ s⁻²)`).

These give directly the continuity statements D127 N4(c) was meant to provide (no bridge
touching estimate is needed for them; see the report).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

lemma integrable_killedHeat_right_nn {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (x : ℂ) :
    Integrable fun w ↦ killedHeat U t x w := by
  refine (integrable_heatKernel _ (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)) x).mono'
    (measurable_killedHeat_right hU ht x).aestronglyMeasurable (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
  exact killedHeat_le_heatKernel _ _ _ _

lemma integrable_killedHeat_mul {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (x : ℂ)
    {f : ℂ → ℝ} (hf : AEStronglyMeasurable f) {M : ℝ} (hM : ∀ w, |f w| ≤ M) :
    Integrable fun w ↦ killedHeat U t x w * f w := by
  refine ((integrable_killedHeat_right_nn hU ht x).const_mul M).mono'
    ((measurable_killedHeat_right hU ht x).aestronglyMeasurable.mul hf)
    (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM w) (killedHeat_nonneg _ _ _ _)

lemma integral_killedHeat_eq_toReal {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (x : ℂ) :
    ∫ w, killedHeat U t x w = (killedSurv U t x).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w ↦ killedHeat_nonneg _ _ _ _)
    (measurable_killedHeat_right hU ht x).aestronglyMeasurable]
  rfl

lemma abs_integral_killedHeat_mul_le {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (x : ℂ)
    {f : ℂ → ℝ} {M : ℝ} (hM : ∀ w, |f w| ≤ M) :
    |∫ w, killedHeat U t x w * f w| ≤ M * (killedSurv U t x).toReal := by
  rw [← integral_killedHeat_eq_toReal hU ht x, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrable_killedHeat_right_nn hU ht x).const_mul M)
    (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM w) (killedHeat_nonneg _ _ _ _)

/-- **Semigroup property against bounded `f`**:
`∫ p_U(ε + τ; x, w) f(w) dw = ∫ p_U(ε; x, v) ∫ p_U(τ; v, w) f(w) dw dv`. -/
theorem integral_killedHeat_add_mul {U : Set ℂ} (hU : IsOpen U) {ε τ : ℝ≥0} (hε : ε ≠ 0)
    (hτ : τ ≠ 0) (x : ℂ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ w, |f w| ≤ M) :
    ∫ w, killedHeat U (ε + τ) x w * f w =
      ∫ v, killedHeat U ε x v * ∫ w, killedHeat U τ v w * f w := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hm1 : Measurable fun q : ℂ × ℂ ↦ killedHeat U ε x q.2 :=
    (measurable_killedHeat_right hU hε x).comp measurable_snd
  have hm2 : Measurable fun q : ℂ × ℂ ↦ killedHeat U τ q.2 q.1 := by
    have := (measurable_killedHeat_uncurry hU τ).comp measurable_swap
    exact this
  have hmk : Measurable fun q : ℂ × ℂ ↦ killedHeat U ε x q.2 * killedHeat U τ q.2 q.1 :=
    hm1.mul hm2
  have he : ∀ w, ∫⁻ v, ENNReal.ofReal (killedHeat U ε x v * killedHeat U τ v w) =
      ENNReal.ofReal (killedHeat U (ε + τ) x w) := fun w ↦ by
    rw [ofReal_killedHeat_add hU hε hτ]
    refine lintegral_congr fun v ↦ ?_
    rw [ENNReal.ofReal_mul (killedHeat_nonneg _ _ _ _)]
  have hint0 : Integrable (fun q : ℂ × ℂ ↦ killedHeat U ε x q.2 * killedHeat U τ q.2 q.1)
      (volume.prod volume) := by
    refine ⟨hmk.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun q ↦
      mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _)),
      lintegral_prod _ hmk.ennreal_ofReal.aemeasurable]
    have : ∫⁻ w, ∫⁻ v, ENNReal.ofReal (killedHeat U ε x v * killedHeat U τ v w) =
        killedSurv U (ε + τ) x := lintegral_congr he
    refine lt_of_eq_of_lt this ?_
    exact (killedSurv_le_one U (add_ne_zero.mpr (Or.inl hε)) x).trans_lt ENNReal.one_lt_top
  have hint : Integrable (fun q : ℂ × ℂ ↦ killedHeat U ε x q.2 * killedHeat U τ q.2 q.1 * f q.1)
      (volume.prod volume) := by
    refine (hint0.const_mul M).mono' (hmk.mul (hf.comp measurable_fst)).aestronglyMeasurable
      (Eventually.of_forall fun q ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _)
      (killedHeat_nonneg _ _ _ _)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (mul_nonneg (killedHeat_nonneg _ _ _ _)
      (killedHeat_nonneg _ _ _ _))
  have hL : ∀ w, killedHeat U (ε + τ) x w * f w =
      ∫ v, killedHeat U ε x v * killedHeat U τ v w * f w := fun w ↦ by
    rw [killedHeat_chapmanKolmogorov hU hε hτ x, integral_mul_const]
  have hR : ∀ v, killedHeat U ε x v * ∫ w, killedHeat U τ v w * f w =
      ∫ w, killedHeat U ε x v * killedHeat U τ v w * f w := fun v ↦ by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
    simp only
    ring
  rw [integral_congr_ae (Eventually.of_forall hL), integral_congr_ae (Eventually.of_forall hR)]
  exact integral_integral_swap (f := fun w v ↦ killedHeat U ε x v * killedHeat U τ v w * f w) hint

lemma exp_neg_le_inv_heatC {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ y⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hy (by linarith [Real.add_one_le_exp y])

lemma exitErr_le {d t : ℝ} (hd : 0 < d) (ht : 0 < t) : exitErr d t ≤ 104 * t / d ^ 2 := by
  unfold exitErr
  have h1 := exp_neg_le_inv_heatC (y := 2 * (d / 4) ^ 2 / t) (by positivity)
  have h2 := exp_neg_le_inv_heatC (y := (d / 3) ^ 2 / (4 * t)) (by positivity)
  rw [show -(d / 3) ^ 2 / (4 * t) = -((d / 3) ^ 2 / (4 * t)) by ring]
  have e1 : (2 * (d / 4) ^ 2 / t)⁻¹ = 8 * t / d ^ 2 := by field_simp; ring
  have e2 : ((d / 3) ^ 2 / (4 * t))⁻¹ = 36 * t / d ^ 2 := by field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have : 104 * t / d ^ 2 = 4 * (8 * t / d ^ 2) + 2 * (36 * t / d ^ 2) := by ring
  rw [this]
  linarith

/-- `|∫ p_U(ε; x, ·) g − ∫ p_ε(x, ·) g| ≤ M · err(d, ε)` when `B(x, d) ⊆ U` and `|g| ≤ M`. -/
theorem abs_killedConv_sub_heatConv_le {U : Set ℂ} (hU : IsOpen U) {ε : ℝ≥0} (hε : ε ≠ 0)
    {g : ℂ → ℝ} (hg : AEStronglyMeasurable g) {M : ℝ} (hM : ∀ v, |g v| ≤ M) {x : ℂ} {d : ℝ}
    (hd : 0 < d) (hball : ball x d ⊆ U) :
    |(∫ v, killedHeat U ε x v * g v) - ∫ v, heatKernel ε x v * g v| ≤ M * exitErr d ε := by
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hε)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hi1 := integrable_killedHeat_mul hU hε x hg hM
  have hh := integrable_heatKernel _ hε' x
  have hi2 : Integrable fun v ↦ heatKernel ε x v * g v := by
    refine (hh.const_mul M).mono' ((measurable_heatKernel_right _ x).aestronglyMeasurable.mul hg)
      (Eventually.of_forall fun v ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg' ε x v), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM v) (heatKernel_nonneg' ε x v)
  have hsub : ∫ v, (killedHeat U ε x v * g v - heatKernel ε x v * g v) =
      (∫ v, killedHeat U ε x v * g v) - ∫ v, heatKernel ε x v * g v := integral_sub hi1 hi2
  rw [← hsub, ← Real.norm_eq_abs]
  have hk := integrable_killedHeat_right_nn hU hε x
  have hbound : Integrable fun v ↦ M * (heatKernel ε x v - killedHeat U ε x v) :=
    (hh.sub hk).const_mul M
  refine (norm_integral_le_of_norm_le hbound (Eventually.of_forall fun v ↦ ?_)).trans ?_
  · rw [← sub_mul, Real.norm_eq_abs, abs_mul, mul_comm, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (killedHeat_le_heatKernel _ _ _ _))]
    exact mul_le_mul_of_nonneg_right (hM v) (sub_nonneg.mpr (killedHeat_le_heatKernel _ _ _ _))
  · rw [integral_const_mul, integral_sub hh hk, integral_heatKernel _ hε' x,
      integral_killedHeat_eq_toReal hU hε x]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have h1 := one_le_killedSurv_add hε hd hball
    have hfin : killedSurv U ε x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (killedSurv_le_one U hε x)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) h1
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (exitErr_nonneg _ _),
      ENNReal.toReal_one] at h2
    linarith

end ZBM
end CONF
end LQGMetric
