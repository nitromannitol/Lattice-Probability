/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatCK
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSupp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 (L2), part 1: the coarse kernel increment is controlled by an `L¹` heat-kernel increment
(packet P-127G, task P2-HEATG)

For a bounded open `U ⊆ B(c, R)`, `t > 0` and `0 < τ ≤ t/4`, with
`g = p_U(τ; x, ·) − p_U(τ; x', ·)`:
```
‖K^{(t,∞)}_x − K^{(t,∞)}_{x'}‖² ≤ 4R²/(π t) · (∫ |g|)²      (sq_norm_wndKernelL2_sub_le)
```
Proof: `‖K_x − K_{x'}‖² = ∫_{(t,∞)} (p(s;x,x) − 2p(s;x,x') + p(s;x',x')) ds` (DZZ (eq-cov-tildeh),
`inner_wndKernelL2`); by Chapman–Kolmogorov twice (`killedHeat_chapmanKolmogorov`) and symmetry the
integrand is `∫ g(y) ∫ p_U(s − 2τ; y, y') g(y') dy' dy`, bounded by
`sup p_U(s − 2τ) (∫|g|)² ≤ (R²/π)(s − 2τ)⁻² (∫|g|)²` (`killedHeat_le_rpow`).

This is the semigroup (smoothing) step of the standard proof that `x ↦ K_x` is Hölder up to the
boundary (CONF l. 725–727 only says "easily checked using Kolmogorov"); own elementary
implementation (DV-P127G-1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat DZZ

lemma integrableOn_killedHeat_Ioi_G {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) (u v : ℂ) :
    IntegrableOn (fun s : ℝ => killedHeat U s.toNNReal u v) (Ioi t) := by
  have hb : IntegrableOn (fun s : ℝ => R ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul _
  refine hb.mono' (measurable_killedHeat_time hU u v).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s hs => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
  exact killedHeat_le_rpow hR hUR (ht.trans hs) u v

/-- `‖K_x − K_{x'}‖² = ∫_{(t,∞)} (p(s;x,x) − 2p(s;x,x') + p(s;x',x')) ds`. -/
theorem sq_norm_wndKernelL2_sub_eq {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) (x x' : ℂ) :
    ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 =
      ∫ s in Ioi t, (killedHeat U s.toNNReal x x - 2 * killedHeat U s.toNNReal x x' +
        killedHeat U s.toNNReal x' x') := by
  rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_wndKernelL2 hU hR hUR measurableSet_Ioi ht Subset.rfl x x,
    inner_wndKernelL2 hU hR hUR measurableSet_Ioi ht Subset.rfl x x',
    inner_wndKernelL2 hU hR hUR measurableSet_Ioi ht Subset.rfl x' x']
  have i1 := integrableOn_killedHeat_Ioi_G hU hR hUR ht x x
  have i2 := integrableOn_killedHeat_Ioi_G hU hR hUR ht x x'
  have i3 := integrableOn_killedHeat_Ioi_G hU hR hUR ht x' x'
  rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul 2)]
  exact (integral_add (i1.sub (i2.const_mul 2)) i3).symm

lemma integrable_killedHeat_right_G {U : Set ℂ} (hU : IsOpen U) {t : ℝ≥0} (ht : t ≠ 0) (x : ℂ) :
    Integrable fun w ↦ killedHeat U t x w := by
  refine (integrable_heatKernel _ (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)) x).mono'
    (measurable_killedHeat_right hU ht x).aestronglyMeasurable (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
  exact killedHeat_le_heatKernel _ _ _ _

/-- `p_U(σ; y, y') ≤ (R²/π) σ⁻²` for `σ : ℝ≥0`. -/
lemma killedHeat_le_rpow_G {U : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hUR : U ⊆ ball c R)
    {σ : ℝ≥0} (hσ : σ ≠ 0) (y y' : ℂ) :
    killedHeat U σ y y' ≤ R ^ 2 / Real.pi * (σ : ℝ) ^ (-2 : ℝ) := by
  have h := killedHeat_le_rpow hR hUR (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ)) y y'
  rwa [Real.toNNReal_coe] at h

/-- **The pointwise semigroup bound**: for `σ ≠ 0`,
`|p(τ+(σ+τ); x,x) − 2p(…; x,x') + p(…; x',x')| ≤ (R²/π) σ⁻² (∫|g|)²`. -/
theorem abs_second_diff_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {τ σ : ℝ≥0} (hτ : τ ≠ 0) (hσ : σ ≠ 0) (x x' : ℂ) :
    |killedHeat U (τ + (σ + τ)) x x - 2 * killedHeat U (τ + (σ + τ)) x x' +
        killedHeat U (τ + (σ + τ)) x' x'| ≤
      R ^ 2 / Real.pi * (σ : ℝ) ^ (-2 : ℝ) *
        (∫ y, |killedHeat U τ x y - killedHeat U τ x' y|) ^ 2 := by
  have hστ : σ + τ ≠ 0 := by positivity
  set M : ℝ := R ^ 2 / Real.pi * (σ : ℝ) ^ (-2 : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  set g : ℂ → ℝ := fun y => killedHeat U τ x y - killedHeat U τ x' y with hg
  have hgi : Integrable g :=
    (integrable_killedHeat_right_G hU hτ x).sub (integrable_killedHeat_right_G hU hτ x')
  set H : ℂ → ℝ := fun y => killedHeat U (σ + τ) y x - killedHeat U (σ + τ) y x' with hH
  -- `H y = ∫ p(σ; y, y') g(y') dy'`
  have hHeq : ∀ y, H y = ∫ y', killedHeat U σ y y' * g y' := by
    intro y
    have hkb : ∀ y', |killedHeat U σ y y'| ≤ M := fun y' => by
      rw [abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
      exact killedHeat_le_rpow_G hR hUR hσ y y'
    have hi : ∀ b, Integrable fun y' => killedHeat U σ y y' * killedHeat U τ b y' := fun b =>
      ((integrable_killedHeat_right_G hU hτ b).const_mul M).mono'
        ((measurable_killedHeat_right hU hσ y).aestronglyMeasurable.mul
          (measurable_killedHeat_right hU hτ b).aestronglyMeasurable)
        (Eventually.of_forall fun y' => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg U σ y y'),
            abs_of_nonneg (killedHeat_nonneg U τ b y')]
          exact mul_le_mul_of_nonneg_right (killedHeat_le_rpow_G hR hUR hσ y y')
            (killedHeat_nonneg _ _ _ _))
    have e1 : ∀ b, (fun y1 => killedHeat U σ y y1 * killedHeat U τ y1 b) =
        fun y1 => killedHeat U σ y y1 * killedHeat U τ b y1 := fun b =>
      funext fun y1 => by rw [killedHeat_symm hU τ y1 b]
    simp only [hH, hg]
    rw [killedHeat_chapmanKolmogorov hU hσ hτ, killedHeat_chapmanKolmogorov hU hσ hτ,
      e1 x, e1 x', ← integral_sub (hi x) (hi x')]
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    simp only
    ring
  have hHb : ∀ y, |H y| ≤ M * ∫ y', |g y'| := by
    intro y
    rw [hHeq y, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (hgi.abs.const_mul M)
      (Eventually.of_forall fun y' => ?_))
    simp only
    rw [abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
    exact mul_le_mul_of_nonneg_right (killedHeat_le_rpow_G hR hUR hσ y y') (abs_nonneg _)
  have hHm : Measurable H :=
    (measurable_killedHeat_left hU hστ x).sub (measurable_killedHeat_left hU hστ x')
  have hiH : ∀ b, Integrable fun y => killedHeat U τ b y * H y := fun b =>
    ((integrable_killedHeat_right_G hU hτ b).const_mul (M * ∫ y', |g y'|)).mono'
      ((measurable_killedHeat_right hU hτ b).aestronglyMeasurable.mul hHm.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hHb y) (killedHeat_nonneg _ _ _ _))
  -- the second difference equals `∫ g H`
  have hQ : killedHeat U (τ + (σ + τ)) x x - 2 * killedHeat U (τ + (σ + τ)) x x' +
      killedHeat U (τ + (σ + τ)) x' x' = ∫ y, g y * H y := by
    have hs := killedHeat_symm hU (τ + (σ + τ)) x' x
    have e : killedHeat U (τ + (σ + τ)) x x - 2 * killedHeat U (τ + (σ + τ)) x x' +
        killedHeat U (τ + (σ + τ)) x' x' =
        (killedHeat U (τ + (σ + τ)) x x - killedHeat U (τ + (σ + τ)) x x') -
        (killedHeat U (τ + (σ + τ)) x' x - killedHeat U (τ + (σ + τ)) x' x') := by
      rw [hs]; ring
    rw [e]
    simp only [killedHeat_chapmanKolmogorov hU hτ hστ]
    have ha : ∀ b, (∫ y, killedHeat U τ b y * killedHeat U (σ + τ) y x) -
        ∫ y, killedHeat U τ b y * killedHeat U (σ + τ) y x' = ∫ y, killedHeat U τ b y * H y := by
      intro b
      have hib : ∀ a, Integrable fun y => killedHeat U τ b y * killedHeat U (σ + τ) y a :=
        fun a => ((integrable_killedHeat_right_G hU hτ b).const_mul
          (R ^ 2 / Real.pi * ((σ + τ : ℝ≥0) : ℝ) ^ (-2 : ℝ))).mono'
          ((measurable_killedHeat_right hU hτ b).aestronglyMeasurable.mul
            (measurable_killedHeat_left hU hστ a).aestronglyMeasurable)
          (Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _),
              abs_of_nonneg (killedHeat_nonneg _ _ _ _), mul_comm]
            exact mul_le_mul_of_nonneg_right (killedHeat_le_rpow_G hR hUR hστ y a)
              (killedHeat_nonneg _ _ _ _))
      rw [← integral_sub (hib x) (hib x')]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hH]; ring
    rw [ha x, ha x', ← integral_sub (hiH x) (hiH x')]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hg]; ring
  rw [hQ]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |g y * H y| ≤ ∫ y, |g y| * (M * ∫ y', |g y'|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hgi.abs.mul_const _) (Eventually.of_forall fun y => by
            dsimp only
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hHb y) (abs_nonneg _))
    _ = M * (∫ y, |g y|) ^ 2 := by rw [integral_mul_const]; ring

/-- **(L2), semigroup step**: `‖K_x − K_{x'}‖² ≤ 4R²/(π t) (∫ |p_U(τ;x,·) − p_U(τ;x',·)|)²`
for `0 < τ ≤ t/4`. -/
theorem sq_norm_wndKernelL2_sub_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {t : ℝ} (ht : 0 < t) {τ : ℝ≥0} (hτ : τ ≠ 0) (hτt : 4 * (τ : ℝ) ≤ t)
    (x x' : ℂ) :
    ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 ≤
      4 * R ^ 2 / (Real.pi * t) * (∫ y, |killedHeat U τ x y - killedHeat U τ x' y|) ^ 2 := by
  set L : ℝ := ∫ y, |killedHeat U τ x y - killedHeat U τ x' y| with hL
  rw [sq_norm_wndKernelL2_sub_eq hU hR hUR ht x x']
  have hτ0 : (0 : ℝ) < τ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
  have hbound : ∀ s ∈ Ioi t, killedHeat U s.toNNReal x x - 2 * killedHeat U s.toNNReal x x' +
      killedHeat U s.toNNReal x' x' ≤ 4 * R ^ 2 / Real.pi * L ^ 2 * s ^ (-2 : ℝ) := by
    intro s hs
    have hs0 : 0 < s := ht.trans hs
    have hle : 2 * τ ≤ s.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0.le]; push_cast
      linarith [show t < s from hs]
    set σ : ℝ≥0 := s.toNNReal - 2 * τ with hσdef
    have hσc : (σ : ℝ) = s - 2 * τ := by
      rw [hσdef, NNReal.coe_sub hle, Real.coe_toNNReal _ hs0.le]; push_cast; ring
    have hσpos : (0 : ℝ) < σ := by rw [hσc]; linarith [show t < s from hs]
    have hσ : σ ≠ 0 := fun h => by rw [h] at hσpos; simp at hσpos
    have hsplit : s.toNNReal = τ + (σ + τ) := by
      rw [show τ + (σ + τ) = σ + 2 * τ by ring, hσdef, tsub_add_cancel_of_le hle]
    have h := abs_second_diff_le hU hR hUR hτ hσ x x'
    rw [← hsplit] at h
    refine (le_abs_self _).trans (h.trans ?_)
    have hσs : (σ : ℝ) ^ (-2 : ℝ) ≤ 4 * s ^ (-2 : ℝ) := by
      have hs2 : s / 2 ≤ σ := by rw [hσc]; linarith [show t < s from hs]
      calc (σ : ℝ) ^ (-2 : ℝ) ≤ (s / 2) ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hs2 (by norm_num)
        _ = 4 * s ^ (-2 : ℝ) := by
            rw [Real.div_rpow hs0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            norm_num; ring
    have hL0 : 0 ≤ L ^ 2 := sq_nonneg _
    calc R ^ 2 / Real.pi * (σ : ℝ) ^ (-2 : ℝ) * L ^ 2
        ≤ R ^ 2 / Real.pi * (4 * s ^ (-2 : ℝ)) * L ^ 2 := by gcongr
      _ = 4 * R ^ 2 / Real.pi * L ^ 2 * s ^ (-2 : ℝ) := by ring
  have hint : IntegrableOn (fun s : ℝ => 4 * R ^ 2 / Real.pi * L ^ 2 * s ^ (-2 : ℝ)) (Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht).const_mul _
  have hiQ : IntegrableOn (fun s : ℝ => killedHeat U s.toNNReal x x -
      2 * killedHeat U s.toNNReal x x' + killedHeat U s.toNNReal x' x') (Ioi t) :=
    ((integrableOn_killedHeat_Ioi_G hU hR hUR ht x x).sub
      ((integrableOn_killedHeat_Ioi_G hU hR hUR ht x x').const_mul 2)).add
      (integrableOn_killedHeat_Ioi_G hU hR hUR ht x' x')
  refine (setIntegral_mono_on hiQ hint measurableSet_Ioi hbound).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ht]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

end ZBM
end CONF
end LQGMetric
