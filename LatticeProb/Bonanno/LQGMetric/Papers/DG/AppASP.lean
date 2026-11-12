/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppASP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppASchur
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAShell
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Second
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernelL2
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK

/-!
For an open set `D` let `a_x(τ)(w) := p(τ; x, w) − p_D(τ; x, w)` (`compK`), the kernel of the
paths from `x` that leave `D` before time `τ`. In the proof of DG Lemma A.1/A.2
(`metric-comparison-final.tex`, DG:2183–2232) the kernels of `(ĥ − ĥ^tr)(z₁)` and
`(ĥ − ĥ^tr)(z₂)` differ by a recentring of the killing ball (`AppAShell`) and by a change of the
start point inside a fixed ball, which is controlled here:

* `compK_split` — `a_x(τ₁ + τ₂) = ∫ p(τ₁; x, y) a_y(τ₂) dy + ∫ a_x(τ₁)(y) p_D(τ₂; y, ·) dy`
  (Chapman–Kolmogorov for `p` and `p_D`);
* `lintegral_sq_compK_sub_le` — `‖a_x(τ₁+τ₂) − a_c(τ₁+τ₂)‖₂² ≤ 2|x − c|²/(8π τ₁²) +
  2‖a_x(τ₁) − a_c(τ₁)‖₂²` (Schur's test `lintegral_sq_integral_le` for both terms, dominated by
  `p(τ₂; y, w)`).

DG instead couple bridges started at `±ε` (DG:2207–2216); that pointwise route needs a shell
estimate for bridges to arbitrary endpoints which fails uniformly (handoff/P2-DG3A.md). This
semigroup argument is our own replacement (DEVIATIONS: DG3B-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat

/-- `a_x(τ)(w) = p(τ; x, w) − p_D(τ; x, w)`. -/
def compK (D : Set ℂ) (τ : ℝ≥0) (x w : ℂ) : ℝ := heatKernel τ x w - killedHeat D τ x w

lemma compK_nonneg (D : Set ℂ) (τ : ℝ≥0) (x w : ℂ) : 0 ≤ compK D τ x w :=
  sub_nonneg.2 (killedHeat_le_heatKernel _ _ _ _)

lemma compK_le (D : Set ℂ) (τ : ℝ≥0) (x w : ℂ) : compK D τ x w ≤ heatKernel τ x w :=
  sub_le_self _ (killedHeat_nonneg _ _ _ _)

lemma measurable_compK_right {D : Set ℂ} (hD : IsOpen D) {τ : ℝ≥0} (hτ : τ ≠ 0) (x : ℂ) :
    Measurable fun w => compK D τ x w :=
  (measurable_heatKernel_right _ x).sub (measurable_killedHeat_right hD hτ x)

lemma measurable_compK_left {D : Set ℂ} (hD : IsOpen D) {τ : ℝ≥0} (hτ : τ ≠ 0) (w : ℂ) :
    Measurable fun x => compK D τ x w :=
  (measurable_heatKernel_left _ w).sub (measurable_killedHeat_left hD hτ w)

lemma pos_of_ne {τ : ℝ≥0} (hτ : τ ≠ 0) : (0 : ℝ) < τ :=
  lt_of_le_of_ne (NNReal.coe_nonneg τ) (Ne.symm (by exact_mod_cast hτ))

/-- Integrability of products dominated by `p(τ₁; x, y) p(τ₂; y, w)`. -/
lemma integrable_of_le_heat_mul {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) (x w : ℂ)
    {F : ℂ → ℝ} (hF : Measurable F)
    (hle : ∀ y, |F y| ≤ heatKernel τ₁ x y * heatKernel τ₂ y w) : Integrable F :=
  (HeatSq.integrable_heatKernel_mul_heatKernel_ck _ _ (pos_of_ne h₁) (pos_of_ne h₂) x w).mono'
    hF.aestronglyMeasurable (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hle y)

/-- **Splitting `a_x` at an intermediate time** (Chapman–Kolmogorov). -/
theorem compK_split {D : Set ℂ} (hD : IsOpen D) {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0)
    (x w : ℂ) :
    compK D (τ₁ + τ₂) x w = (∫ y, heatKernel τ₁ x y * compK D τ₂ y w) +
      ∫ y, compK D τ₁ x y * killedHeat D τ₂ y w := by
  have ck1 : heatKernel ((τ₁ + τ₂ : ℝ≥0) : ℝ) x w =
      ∫ y, heatKernel τ₁ x y * heatKernel τ₂ y w := by
    rw [NNReal.coe_add, HeatSq.integral_heatKernel_mul_heatKernel_ck _ _ (pos_of_ne h₁)
      (pos_of_ne h₂)]
  have ck2 := killedHeat_chapmanKolmogorov hD h₁ h₂ x w
  have hh0 : ∀ (t : ℝ≥0) (a b : ℂ), 0 ≤ heatKernel t a b := fun t a b => heatKernel_nonneg' t a b
  have iHH : Integrable fun y => heatKernel τ₁ x y * heatKernel τ₂ y w :=
    HeatSq.integrable_heatKernel_mul_heatKernel_ck _ _ (pos_of_ne h₁) (pos_of_ne h₂) x w
  have iHK : Integrable fun y => heatKernel τ₁ x y * killedHeat D τ₂ y w := by
    refine integrable_of_le_heat_mul h₁ h₂ x w ((measurable_heatKernel_right _ x).mul
      (measurable_killedHeat_left hD h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (hh0 _ _ _) (killedHeat_nonneg _ _ _ _))]
    exact mul_le_mul_of_nonneg_left (killedHeat_le_heatKernel _ _ _ _) (hh0 _ _ _)
  have iKK : Integrable fun y => killedHeat D τ₁ x y * killedHeat D τ₂ y w := by
    refine integrable_of_le_heat_mul h₁ h₂ x w ((measurable_killedHeat_right hD h₁ x).mul
      (measurable_killedHeat_left hD h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))]
    exact mul_le_mul (killedHeat_le_heatKernel _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
      (killedHeat_nonneg _ _ _ _) (hh0 _ _ _)
  unfold compK
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub iHH iHK, integral_sub iHK iKK, ck1, ck2]
  ring

lemma measurable_heatKernel_uncurry (τ : ℝ) : Measurable fun p : ℂ × ℂ => heatKernel τ p.1 p.2 := by
  unfold heatKernel; fun_prop

lemma measurable_killedHeat_uncurry {D : Set ℂ} (hD : IsOpen D) (τ : ℝ≥0) :
    Measurable fun p : ℂ × ℂ => killedHeat D τ p.1 p.2 :=
  (measurable_killedHeat hD).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))

lemma measurable_compK_uncurry {D : Set ℂ} (hD : IsOpen D) (τ : ℝ≥0) :
    Measurable fun p : ℂ × ℂ => compK D τ p.1 p.2 :=
  (measurable_heatKernel_uncurry _).sub (measurable_killedHeat_uncurry hD τ)

lemma lintegral_heat_left_le {τ : ℝ≥0} (hτ : τ ≠ 0) (w : ℂ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel τ y w) ≤ 1 := by
  simp_rw [heatKernel_comm _ _ w]
  exact (GFFExist.lintegral_ofReal_heatKernel (pos_of_ne hτ) w).le

lemma lintegral_heat_right_le {τ : ℝ≥0} (hτ : τ ≠ 0) (y : ℂ) :
    ∫⁻ w, ENNReal.ofReal (heatKernel τ y w) ≤ 1 :=
  (GFFExist.lintegral_ofReal_heatKernel (pos_of_ne hτ) y).le

/-- `∫ (p(τ; x, y) − p(τ; c, y))² dy ≤ |x − c|²/(8π τ²)` in `lintegral` form. -/
lemma lintegral_sq_heat_sub_le {τ : ℝ≥0} (hτ : τ ≠ 0) (x c : ℂ) :
    ∫⁻ y, ENNReal.ofReal ((heatKernel τ x y - heatKernel τ c y) ^ 2) ≤
      ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ : ℝ) ^ 2)) := by
  have hτ' := pos_of_ne hτ
  have hi : Integrable fun y => (heatKernel τ x y - heatKernel τ c y) ^ 2 := by
    have e : (fun y => (heatKernel τ x y - heatKernel τ c y) ^ 2) = fun y =>
        heatKernel τ x y * heatKernel τ x y - 2 * (heatKernel τ x y * heatKernel τ c y) +
          heatKernel τ c y * heatKernel τ c y := by funext y; ring
    rw [e]
    exact ((WhiteNoise.integrable_heatKernel_mul_heatKernel _ hτ' x x).sub
      ((WhiteNoise.integrable_heatKernel_mul_heatKernel _ hτ' x c).const_mul 2)).add
      (WhiteNoise.integrable_heatKernel_mul_heatKernel _ hτ' c c)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (HeatSq.integral_sq_heatKernel_sub_le' hτ' x c)

/-- **Start-point regularity of `a_x`** (Schur's test on both terms of `compK_split`):
`‖a_x(τ₁+τ₂) − a_c(τ₁+τ₂)‖₂² ≤ 2|x − c|²/(8πτ₁²) + 2‖a_x(τ₁) − a_c(τ₁)‖₂²`. -/
theorem lintegral_sq_compK_sub_le {D : Set ℂ} (hD : IsOpen D) {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0)
    (h₂ : τ₂ ≠ 0) (x c : ℂ) :
    ∫⁻ w, ENNReal.ofReal ((compK D (τ₁ + τ₂) x w - compK D (τ₁ + τ₂) c w) ^ 2) ≤
      2 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ₁ : ℝ) ^ 2)) +
        2 * ∫⁻ y, ENNReal.ofReal ((compK D τ₁ x y - compK D τ₁ c y) ^ 2) := by
  have hh0 : ∀ (t : ℝ≥0) (a b : ℂ), 0 ≤ heatKernel t a b := fun t a b => heatKernel_nonneg' t a b
  set T₁ : ℂ → ℝ := fun w => ∫ y, (heatKernel τ₁ x y - heatKernel τ₁ c y) * compK D τ₂ y w
  set T₂ : ℂ → ℝ := fun w => ∫ y, (compK D τ₁ x y - compK D τ₁ c y) * killedHeat D τ₂ y w
  have iA : ∀ (u w : ℂ), Integrable fun y => heatKernel τ₁ u y * compK D τ₂ y w := by
    intro u w
    refine integrable_of_le_heat_mul h₁ h₂ u w ((measurable_heatKernel_right _ u).mul
      (measurable_compK_left hD h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (hh0 _ _ _) (compK_nonneg _ _ _ _))]
    exact mul_le_mul_of_nonneg_left (compK_le _ _ _ _) (hh0 _ _ _)
  have iB : ∀ (u w : ℂ), Integrable fun y => compK D τ₁ u y * killedHeat D τ₂ y w := by
    intro u w
    refine integrable_of_le_heat_mul h₁ h₂ u w ((measurable_compK_right hD h₁ u).mul
      (measurable_killedHeat_left hD h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (compK_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))]
    exact mul_le_mul (compK_le _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
      (killedHeat_nonneg _ _ _ _) (hh0 _ _ _)
  have hsplit : ∀ w, compK D (τ₁ + τ₂) x w - compK D (τ₁ + τ₂) c w = T₁ w + T₂ w := by
    intro w
    rw [compK_split hD h₁ h₂ x w, compK_split hD h₁ h₂ c w]
    simp only [T₁, T₂, sub_mul]
    rw [integral_sub (iA x w) (iA c w), integral_sub (iB x w) (iB c w)]
    ring
  have hpt : ∀ w, ENNReal.ofReal ((compK D (τ₁ + τ₂) x w - compK D (τ₁ + τ₂) c w) ^ 2) ≤
      2 * ENNReal.ofReal (T₁ w ^ 2) + 2 * ENNReal.ofReal (T₂ w ^ 2) := by
    intro w
    rw [hsplit w]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (T₁ w - T₂ w)])
  have hT₁m : Measurable T₁ := by
    refine (StronglyMeasurable.integral_prod_left (f := fun y w =>
      (heatKernel τ₁ x y - heatKernel τ₁ c y) * compK D τ₂ y w) ?_).measurable
    exact ((((measurable_heatKernel_right _ x).sub (measurable_heatKernel_right _ c)).comp
      measurable_fst).mul (measurable_compK_uncurry hD τ₂)).stronglyMeasurable
  have hS₁ := lintegral_sq_integral_le (f := fun y => heatKernel τ₁ x y - heatKernel τ₁ c y)
    (G := fun y w => compK D τ₂ y w) (K := fun y w => heatKernel τ₂ y w)
    ((measurable_heatKernel_right _ x).sub (measurable_heatKernel_right _ c))
    (measurable_heatKernel_uncurry _)
    (fun y w => by rw [abs_of_nonneg (compK_nonneg _ _ _ _)]; exact compK_le _ _ _ _)
    (lintegral_heat_left_le h₂) (lintegral_heat_right_le h₂)
  have hS₂ := lintegral_sq_integral_le (f := fun y => compK D τ₁ x y - compK D τ₁ c y)
    (G := fun y w => killedHeat D τ₂ y w) (K := fun y w => heatKernel τ₂ y w)
    ((measurable_compK_right hD h₁ x).sub (measurable_compK_right hD h₁ c))
    (measurable_heatKernel_uncurry _)
    (fun y w => by
      rw [abs_of_nonneg (killedHeat_nonneg _ _ _ _)]; exact killedHeat_le_heatKernel _ _ _ _)
    (lintegral_heat_left_le h₂) (lintegral_heat_right_le h₂)
  calc ∫⁻ w, ENNReal.ofReal ((compK D (τ₁ + τ₂) x w - compK D (τ₁ + τ₂) c w) ^ 2)
      ≤ ∫⁻ w, (2 * ENNReal.ofReal (T₁ w ^ 2) + 2 * ENNReal.ofReal (T₂ w ^ 2)) :=
        lintegral_mono hpt
    _ = 2 * (∫⁻ w, ENNReal.ofReal (T₁ w ^ 2)) + 2 * ∫⁻ w, ENNReal.ofReal (T₂ w ^ 2) := by
        rw [lintegral_add_left' (((hT₁m.pow_const 2).ennreal_ofReal).const_mul 2).aemeasurable,
          lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le)
          (mul_le_mul_of_nonneg_left ?_ zero_le)
        · exact hS₁.trans (lintegral_sq_heat_sub_le h₁ x c)
        · exact hS₂

end DG
end LQGMetric
