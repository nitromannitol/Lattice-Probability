/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Second
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 (L2), part 2: the `L¹` increment of the killed heat kernel near the boundary
(packet P-127G, task P2-HEATG)

With `S(y) = ∫ p_U(τ₂; y, w) dw` (`survG`, the survival probability `P^y(τ_U > τ₂)`):

* `integral_abs_killedHeat_add_sub_le` (Chapman–Kolmogorov + Tonelli):
  `∫|p_U(τ₁+τ₂; x, ·) − p_U(τ₁+τ₂; x', ·)| ≤ ∫ |p_U(τ₁; x, y) − p_U(τ₁; x', y)| S(y) dy`;
* `integral_abs_heat_sub_mul_survG_le` (free part, `L²` heat-kernel increment
  `HeatSq.integral_sq_heatKernel_sub_le'` and AM–GM on `B(c, R) ⊇ U`):
  `∫ |p_{τ₁}(x, y) − p_{τ₁}(x', y)| S(y) dy ≤ (1/(16π) + πR²/2) |x − x'|/τ₁`;
* `integral_heat_sub_killed_mul_survG_le` (killed part): if `S ≤ ω` on `{y : B(y, ρ) ⊄ U}` then
  `∫ (p_{τ₁}(x, y) − p_U(τ₁; x, y)) S(y) dy ≤ ω + 4e^{−2(ρ/4)²/τ₁} + 2e^{−(ρ/3)²/(4τ₁)}`
  (bridges from `y` to `x` with `B(y, ρ) ⊆ U`, `|x − y| ≤ ρ/3` stay in `B(y, ρ)`
  (`one_sub_bridgeStay_ball_le'`, copied from P2-HEATC's `one_sub_bridgeStay_ball_le`, itself
  adapted from `DZZ.killedHeat_sub_inter_ball_le`, DZZ l. 491–499), plus the Gaussian tail);
* `integral_abs_killedHeat_sub_le`: the combination.

Own elementary argument (DV-P127G-1): the regularity of `x ↦ p_U(τ; x, ·)` in `L¹` up to `∂U` is
reduced to the decay of the survival probability `S` near `∂U`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

/-- The survival probability `P^y(τ_U > t) = ∫ p_U(t; y, w) dw` (real form). -/
def survG (U : Set ℂ) (t : ℝ≥0) (y : ℂ) : ℝ := ∫ w, killedHeat U t y w

lemma survG_nonneg (U : Set ℂ) (t : ℝ≥0) (y : ℂ) : 0 ≤ survG U t y :=
  integral_nonneg fun _ => killedHeat_nonneg _ _ _ _

lemma survG_le_one (U : Set ℂ) {t : ℝ≥0} (ht : t ≠ 0) (y : ℂ) : survG U t y ≤ 1 := by
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  calc ∫ w, killedHeat U t y w ≤ ∫ w, heatKernel t y w :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => killedHeat_nonneg _ _ _ _)
          (integrable_heatKernel _ ht' y)
          (Eventually.of_forall fun w => killedHeat_le_heatKernel _ _ _ _)
    _ = 1 := integral_heatKernel _ ht' y

lemma survG_eq_zero {U : Set ℂ} {t : ℝ≥0} (ht : t ≠ 0) {y : ℂ} (hy : y ∉ U) : survG U t y = 0 := by
  simp [survG, killedHeat_eq_zero_of_not_mem_left ht hy]

lemma measurable_killedHeat_pair {U : Set ℂ} (hU : IsOpen U) (t : ℝ≥0) :
    Measurable fun q : ℂ × ℂ => killedHeat U t q.1 q.2 :=
  (measurable_killedHeat hU).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))

lemma measurable_survG {U : Set ℂ} (hU : IsOpen U) (t : ℝ≥0) : Measurable (survG U t) :=
  ((measurable_killedHeat_pair hU t).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℂ))).measurable

lemma killedHeat_le_inv_G (U : Set ℂ) (t : ℝ≥0) (y w : ℂ) :
    killedHeat U t y w ≤ (2 * Real.pi * t)⁻¹ :=
  (killedHeat_le_heatKernel _ _ _ _).trans (heatKernel_le_inv _ (NNReal.coe_nonneg _) _ _)

/-- **Chapman–Kolmogorov in `L¹`.** -/
theorem integral_abs_killedHeat_add_sub_le {U : Set ℂ} (hU : IsOpen U) {τ₁ τ₂ : ℝ≥0}
    (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) (x x' : ℂ) :
    ∫ w, |killedHeat U (τ₁ + τ₂) x w - killedHeat U (τ₁ + τ₂) x' w| ≤
      ∫ y, |killedHeat U τ₁ x y - killedHeat U τ₁ x' y| * survG U τ₂ y := by
  set D : ℂ → ℝ := fun y => |killedHeat U τ₁ x y - killedHeat U τ₁ x' y| with hD
  have hDi : Integrable D :=
    ((integrable_killedHeat_right_G hU h₁ x).sub (integrable_killedHeat_right_G hU h₁ x')).abs
  have hDm : Measurable D := continuous_abs.measurable.comp
    ((measurable_killedHeat_right hU h₁ x).sub (measurable_killedHeat_right hU h₁ x'))
  have hD0 : ∀ y, 0 ≤ D y := fun y => abs_nonneg _
  set F : ℂ → ℂ → ℝ := fun y w => D y * killedHeat U τ₂ y w with hF
  have hFm : Measurable (Function.uncurry F) :=
    (hDm.comp measurable_fst).mul (measurable_killedHeat_pair hU τ₂)
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · exact (integrable_killedHeat_right_G hU h₂ y).const_mul (D y)
    · refine hDi.mono' (by
        exact ((hFm.norm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))
          ).aestronglyMeasurable)) (Eventually.of_forall fun y => ?_)
      have e : ∫ w, ‖Function.uncurry F (y, w)‖ = D y * survG U τ₂ y := by
        simp only [Function.uncurry_apply_pair, hF, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (hD0 y), abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
        exact integral_const_mul _ _
      rw [e, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hD0 y) (survG_nonneg _ _ _))]
      exact mul_le_of_le_one_right (hD0 y) (survG_le_one U h₂ y)
  -- pointwise in `w`
  have hpt : ∀ w, |killedHeat U (τ₁ + τ₂) x w - killedHeat U (τ₁ + τ₂) x' w| ≤ ∫ y, F y w := by
    intro w
    have hi : ∀ b, Integrable fun y => killedHeat U τ₁ b y * killedHeat U τ₂ y w := fun b =>
      ((integrable_killedHeat_right_G hU h₁ b).mul_const ((2 * Real.pi * τ₂)⁻¹)).mono'
        ((measurable_killedHeat_right hU h₁ b).aestronglyMeasurable.mul
          (measurable_killedHeat_left hU h₂ w).aestronglyMeasurable)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (killedHeat_nonneg _ _ _ _),
            abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
          exact mul_le_mul_of_nonneg_left (killedHeat_le_inv_G _ _ _ _) (killedHeat_nonneg _ _ _ _))
    rw [killedHeat_chapmanKolmogorov hU h₁ h₂, killedHeat_chapmanKolmogorov hU h₁ h₂,
      ← integral_sub (hi x) (hi x')]
    refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun y => ?_)))
    simp only [hF, hD]
    rw [← sub_mul, abs_mul]
    try rw [abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
  calc ∫ w, |killedHeat U (τ₁ + τ₂) x w - killedHeat U (τ₁ + τ₂) x' w|
      ≤ ∫ w, ∫ y, F y w :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          hFi.integral_prod_right (Eventually.of_forall hpt)
    _ = ∫ y, ∫ w, F y w := (integral_integral_swap hFi).symm
    _ = ∫ y, D y * survG U τ₂ y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hF, survG]
        rw [integral_const_mul]

/-- `|a| ≤ a²/(2ε) + ε/2`. -/
lemma abs_le_sq_div_add_G {a ε : ℝ} (hε : 0 < ε) : |a| ≤ a ^ 2 / (2 * ε) + ε / 2 := by
  have : |a| * (2 * ε) ≤ a ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg (|a| - ε), sq_abs a]
  calc |a| = |a| * (2 * ε) / (2 * ε) := by field_simp
    _ ≤ (a ^ 2 + ε ^ 2) / (2 * ε) := by gcongr
    _ = a ^ 2 / (2 * ε) + ε / 2 := by field_simp

lemma volume_real_ball_G (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (volume : Measure ℂ).real (ball c R) = Real.pi * R ^ 2 := by
  rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR]
  simp [mul_comm]

/-- **The free part.** -/
theorem integral_abs_heat_sub_mul_survG_le {U : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) (x x' : ℂ) :
    ∫ y, |heatKernel τ₁ x y - heatKernel τ₁ x' y| * survG U τ₂ y ≤
      (1 / (16 * Real.pi) + Real.pi * R ^ 2 / 2) * ‖x - x'‖ / τ₁ := by
  have ht : (0 : ℝ) < τ₁ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h₁)
  rcases eq_or_ne x x' with hxx | hxx
  · subst hxx; simp
  have hd : 0 < ‖x - x'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx)
  set d := ‖x - x'‖
  set ε : ℝ := d / τ₁ with hε
  have hε0 : 0 < ε := by positivity
  set f : ℂ → ℝ := fun y => heatKernel τ₁ x y - heatKernel τ₁ x' y with hf
  have hfi : Integrable fun y => f y ^ 2 := HeatSq.integrable_sq_heatKernel_sub ht x x'
  have hbi : Integrable ((ball c R).indicator fun _ : ℂ => ε / 2) :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_const (by
      rw [Complex.volume_ball]; exact ENNReal.mul_ne_top (by simp) (by simp)))
  have hpt : ∀ y, |f y| * survG U τ₂ y ≤
      (fun y => f y ^ 2 / (2 * ε)) y + (ball c R).indicator (fun _ : ℂ => ε / 2) y := by
    intro y
    by_cases hy : y ∈ ball c R
    · rw [indicator_of_mem hy]
      exact (mul_le_of_le_one_right (abs_nonneg _) (survG_le_one U h₂ y)).trans
        (abs_le_sq_div_add_G hε0)
    · have hyU : y ∉ U := fun h => hy (hUR h)
      rw [survG_eq_zero h₂ hyU, mul_zero, indicator_of_notMem hy, add_zero]
      positivity
  refine (integral_mono_of_nonneg (Eventually.of_forall fun y =>
    mul_nonneg (abs_nonneg _) (survG_nonneg _ _ _)) ((hfi.div_const _).add hbi)
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_add' (hfi.div_const _) hbi, integral_div, integral_indicator_const _ measurableSet_ball,
    volume_real_ball_G c hR, smul_eq_mul]
  have h2 := HeatSq.integral_sq_heatKernel_sub_le' ht x x'
  have hpi := Real.pi_pos
  calc (∫ y, f y ^ 2) / (2 * ε) + Real.pi * R ^ 2 * (ε / 2)
      ≤ (d ^ 2 / (8 * Real.pi * (τ₁ : ℝ) ^ 2)) / (2 * ε) + Real.pi * R ^ 2 * (ε / 2) := by
        gcongr
    _ = (1 / (16 * Real.pi) + Real.pi * R ^ 2 / 2) * d / τ₁ := by
        rw [hε]; field_simp; ring

/-- The bridge from `v` to `w` (`|w − v| ≤ r/3`) leaves `B(v, r)` with probability
`≤ 4 e^{-2(r/4)²/t}`. Copied verbatim from P2-HEATC's `CONF.ZBM.one_sub_bridgeStay_ball_le`
(Papers/CONF/S3D127C5, itself adapted from `DZZ.killedHeat_sub_inter_ball_le`, DZZ l. 491–499). -/
theorem one_sub_bridgeStay_ball_le' {t : ℝ≥0} (ht : t ≠ 0) {v w : ℂ} {r : ℝ} (hr : 0 < r)
    (hvw : ‖w - v‖ ≤ r / 3) :
    1 - bridgeStay (ball v r) t v w ≤ 4 * Real.exp (-(2 * (r / 4) ^ 2 / t)) := by
  set X := stdBridge t
  have hX : IsPlanarBridge t X P2 := isPlanarBridge_stdBridge ht
  have hY := DZZ.isPlanarBridge_neg hX
  haveI := hX.gauss.isProbabilityMeasure
  have hr4 : 0 < r / 4 := by positivity
  set E := bridgeEvent (ball v r) t v w X
  set F : Bool → (ℝ≥0 → Ω2 → ℂ) → Set Ω2 := fun b Z =>
    {ω | ∃ s : ℝ≥0, s ≤ t ∧ r / 4 < coordProc Z (b, s) ω}
  have hsub : Eᶜ ⊆ (F false X ∪ F true X) ∪ (F false (fun s ω => -X s ω) ∪
      F true (fun s ω => -X s ω)) := by
    intro ω hω
    simp only [E, bridgeEvent, mem_compl_iff, mem_setOf_eq, not_forall] at hω
    obtain ⟨s, hs, hsB⟩ := hω
    have hst : (s : ℝ) / t ≤ 1 := by
      rw [div_le_one (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht))]; exact_mod_cast hs
    have hst0 : 0 ≤ (s : ℝ) / t := by positivity
    have hdrift : ‖(((s : ℝ) / t : ℝ) : ℂ) * (w - v)‖ ≤ r / 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hst0]
      nlinarith [norm_nonneg (w - v)]
    have hnot : 2 * r / 3 ≤ ‖X s ω‖ := by
      rw [mem_ball, dist_eq_norm, bridgePath, not_lt] at hsB
      have := norm_add_le ((((s : ℝ) / t : ℝ) : ℂ) * (w - v)) (X s ω)
      rw [show v + (((s : ℝ) / t : ℝ) : ℂ) * (w - v) + X s ω - v =
        (((s : ℝ) / t : ℝ) : ℂ) * (w - v) + X s ω by ring] at hsB
      linarith
    have hle := Complex.norm_le_abs_re_add_abs_im (X s ω)
    simp only [F, mem_union, mem_setOf_eq, DZZ.coordProc_false, DZZ.coordProc_true,
      Complex.neg_re, Complex.neg_im]
    rcases le_total (r / 3) |(X s ω).re| with h | h
    · rcases le_or_gt 0 (X s ω).re with h0 | h0
      · rw [abs_of_nonneg h0] at h
        exact Or.inl (Or.inl ⟨s, hs, by linarith⟩)
      · rw [abs_of_neg h0] at h
        exact Or.inr (Or.inl ⟨s, hs, by linarith⟩)
    · have h' : r / 3 ≤ |(X s ω).im| := by linarith
      rcases le_or_gt 0 (X s ω).im with h0 | h0
      · rw [abs_of_nonneg h0] at h'
        exact Or.inl (Or.inr ⟨s, hs, by linarith⟩)
      · rw [abs_of_neg h0] at h'
        exact Or.inr (Or.inr ⟨s, hs, by linarith⟩)
  have h1 : (1 : ℝ) ≤ P2.real E + P2.real Eᶜ := by
    have := measureReal_union_le (μ := P2) E Eᶜ
    rwa [union_compl_self, measureReal_def, measure_univ, ENNReal.toReal_one] at this
  have h2 := (measureReal_mono hsub (measure_ne_top P2 _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _)
      (measureReal_union_le _ _)))
  have b1 := measureReal_bridge_max_gt ht hX false hr4
  have b2 := measureReal_bridge_max_gt ht hX true hr4
  have b3 := measureReal_bridge_max_gt ht hY false hr4
  have b4 := measureReal_bridge_max_gt ht hY true hr4
  simp only [F] at h2
  have hE : bridgeStay (ball v r) t v w = P2.real E := rfl
  rw [hE]
  linarith

/-- Gaussian tail (P2-HEATC's `heatKernel_le_tail'`, copied):
`p_s(x, w) ≤ 2 e^{-δ²/(4s)} p_{2s}(x, w)` if `δ ≤ |x − w|`. -/
theorem heatKernel_le_tail_G {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) {x w : ℂ} (hu : δ ≤ ‖x - w‖) :
    heatKernel s x w ≤ 2 * Real.exp (-δ ^ 2 / (4 * s)) * heatKernel (2 * s) x w := by
  simp only [heatKernel]
  have e : 2 * Real.exp (-δ ^ 2 / (4 * s)) * ((2 * Real.pi * (2 * s))⁻¹ *
      Real.exp (-‖x - w‖ ^ 2 / (2 * (2 * s)))) =
      (2 * Real.pi * s)⁻¹ * Real.exp (-δ ^ 2 / (4 * s) + -‖x - w‖ ^ 2 / (4 * s)) := by
    rw [Real.exp_add]; field_simp; ring_nf
  rw [e]
  gcongr
  have h1 : δ ^ 2 ≤ ‖x - w‖ ^ 2 := pow_le_pow_left₀ hδ hu 2
  have e2 : -‖x - w‖ ^ 2 / (2 * s) - (-δ ^ 2 / (4 * s) + -‖x - w‖ ^ 2 / (4 * s)) =
      (δ ^ 2 - ‖x - w‖ ^ 2) / (4 * s) := by field_simp; ring
  have : (δ ^ 2 - ‖x - w‖ ^ 2) / (4 * s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- The killed-mass error `4 e^{−2(ρ/4)²/τ} + 2 e^{−(ρ/3)²/(4τ)}`. -/
def killErrG (ρ τ : ℝ) : ℝ :=
  4 * Real.exp (-(2 * (ρ / 4) ^ 2 / τ)) + 2 * Real.exp (-(ρ / 3) ^ 2 / (4 * τ))

lemma killErrG_nonneg (ρ τ : ℝ) : 0 ≤ killErrG ρ τ := by unfold killErrG; positivity

/-- **The killed part.** If `S ≤ ω` at every `y` with `B(y, ρ) ⊄ U`, then
`∫ (p_{τ₁}(x, y) − p_U(τ₁; x, y)) S(y) dy ≤ ω + killErrG ρ τ₁`. -/
theorem integral_heat_sub_killed_mul_survG_le {U : Set ℂ} (hU : IsOpen U) {τ₁ τ₂ : ℝ≥0}
    (h₁ : τ₁ ≠ 0) (x : ℂ) {ρ ω : ℝ} (hρ : 0 < ρ) (hω0 : 0 ≤ ω)
    (hω : ∀ y, ¬ ball y ρ ⊆ U → survG U τ₂ y ≤ ω) (h₂ : τ₂ ≠ 0) :
    ∫ y, (heatKernel τ₁ x y - killedHeat U τ₁ x y) * survG U τ₂ y ≤ ω + killErrG ρ τ₁ := by
  have ht : (0 : ℝ) < τ₁ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h₁)
  set e1 : ℝ := 4 * Real.exp (-(2 * (ρ / 4) ^ 2 / τ₁))
  set e2 : ℝ := 2 * Real.exp (-(ρ / 3) ^ 2 / (4 * τ₁))
  have he1 : 0 ≤ e1 := by positivity
  have he2 : 0 ≤ e2 := by positivity
  have hk : ∀ y, killedHeat U τ₁ x y ≤ heatKernel τ₁ x y := fun y => killedHeat_le_heatKernel _ _ _ _
  have hpt : ∀ y, (heatKernel τ₁ x y - killedHeat U τ₁ x y) * survG U τ₂ y ≤
      (ω + e1) * heatKernel τ₁ x y + e2 * heatKernel (2 * τ₁) x y := by
    intro y
    have hh0 : 0 ≤ heatKernel τ₁ x y := heatKernel_nonneg' _ _ _
    have hh0' : 0 ≤ heatKernel (2 * τ₁) x y := heatKernel_nonneg _ (by positivity) _ _
    have hS0 := survG_nonneg U τ₂ y
    have hS1 := survG_le_one U h₂ y
    have hd0 : 0 ≤ heatKernel τ₁ x y - killedHeat U τ₁ x y := sub_nonneg.mpr (hk y)
    have hd1 : heatKernel τ₁ x y - killedHeat U τ₁ x y ≤ heatKernel τ₁ x y := by
      linarith [killedHeat_nonneg U τ₁ x y]
    by_cases hb : ball y ρ ⊆ U
    · by_cases hxy : ‖x - y‖ ≤ ρ / 3
      · have hq : 1 - bridgeStay U τ₁ x y ≤ e1 := by
          have h1 := one_sub_bridgeStay_ball_le' h₁ (v := y) (w := x) hρ hxy
          have h2 : bridgeStay (ball y ρ) τ₁ y x ≤ bridgeStay U τ₁ x y := by
            rw [bridgeStay_symm hU h₁ x y]; exact bridgeStay_mono hb _ _ _
          linarith
        have he : heatKernel τ₁ x y - killedHeat U τ₁ x y =
            heatKernel τ₁ x y * (1 - bridgeStay U τ₁ x y) := by
          simp only [killedHeat]; ring
        calc (heatKernel τ₁ x y - killedHeat U τ₁ x y) * survG U τ₂ y
            ≤ (heatKernel τ₁ x y - killedHeat U τ₁ x y) * 1 :=
              mul_le_mul_of_nonneg_left hS1 hd0
          _ = heatKernel τ₁ x y * (1 - bridgeStay U τ₁ x y) := by rw [mul_one, he]
          _ ≤ heatKernel τ₁ x y * e1 := mul_le_mul_of_nonneg_left hq hh0
          _ ≤ (ω + e1) * heatKernel τ₁ x y + e2 * heatKernel (2 * τ₁) x y := by
              nlinarith [mul_nonneg hω0 hh0, mul_nonneg he2 hh0']
      · push_neg at hxy
        have htail := heatKernel_le_tail_G ht (by positivity : (0 : ℝ) ≤ ρ / 3) hxy.le
        calc (heatKernel τ₁ x y - killedHeat U τ₁ x y) * survG U τ₂ y
            ≤ heatKernel τ₁ x y * 1 := mul_le_mul hd1 hS1 hS0 hh0
          _ ≤ e2 * heatKernel (2 * τ₁) x y := by rw [mul_one]; exact htail
          _ ≤ (ω + e1) * heatKernel τ₁ x y + e2 * heatKernel (2 * τ₁) x y := by
              nlinarith [mul_nonneg (add_nonneg hω0 he1) hh0]
    · calc (heatKernel τ₁ x y - killedHeat U τ₁ x y) * survG U τ₂ y
          ≤ heatKernel τ₁ x y * ω := mul_le_mul hd1 (hω y hb) hS0 hh0
        _ ≤ (ω + e1) * heatKernel τ₁ x y + e2 * heatKernel (2 * τ₁) x y := by
            nlinarith [mul_nonneg he1 hh0, mul_nonneg he2 hh0']
  have hi1 := integrable_heatKernel _ ht x
  have hi2 := integrable_heatKernel _ (by positivity : (0 : ℝ) < 2 * τ₁) x
  refine (integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg
    (sub_nonneg.mpr (hk y)) (survG_nonneg _ _ _)) ((hi1.const_mul _).add (hi2.const_mul _))
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_add' (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
    integral_heatKernel _ ht x, integral_heatKernel _ (by positivity) x]
  simp only [killErrG, mul_one, e1, e2]
  ring

/-- **The `L¹` increment of the killed heat kernel**: for `τ₁, τ₂ ≠ 0`, if
`P^y(τ_U > τ₂) ≤ ω` whenever `B(y, ρ) ⊄ U`, then
`∫|p_U(τ₁+τ₂; x, ·) − p_U(τ₁+τ₂; x', ·)| ≤ (1/(16π) + πR²/2)|x − x'|/τ₁ + 2(ω + killErrG ρ τ₁)`. -/
theorem integral_abs_killedHeat_sub_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) {ρ ω : ℝ} (hρ : 0 < ρ)
    (hω0 : 0 ≤ ω) (hω : ∀ y, ¬ ball y ρ ⊆ U → survG U τ₂ y ≤ ω) (x x' : ℂ) :
    ∫ w, |killedHeat U (τ₁ + τ₂) x w - killedHeat U (τ₁ + τ₂) x' w| ≤
      (1 / (16 * Real.pi) + Real.pi * R ^ 2 / 2) * ‖x - x'‖ / τ₁ + 2 * (ω + killErrG ρ τ₁) := by
  have ht : (0 : ℝ) < τ₁ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h₁)
  refine (integral_abs_killedHeat_add_sub_le hU h₁ h₂ x x').trans ?_
  have hSm := measurable_survG hU τ₂
  have hS1 := survG_le_one U h₂
  have hS0 := survG_nonneg U τ₂
  have hhx := integrable_heatKernel _ ht x
  have hhx' := integrable_heatKernel _ ht x'
  have hint : ∀ {f : ℂ → ℝ}, Integrable f → Integrable fun y => f y * survG U τ₂ y :=
    fun {f} hf => hf.norm.mono' (hf.aestronglyMeasurable.mul hSm.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs (survG U τ₂ y), abs_of_nonneg (hS0 y)]
        exact mul_le_of_le_one_right (norm_nonneg _) (hS1 y))
  set A : ℂ → ℝ := fun y => |heatKernel τ₁ x y - heatKernel τ₁ x' y| * survG U τ₂ y with hA
  set B : ℂ → ℝ := fun y => (heatKernel τ₁ x y - killedHeat U τ₁ x y) * survG U τ₂ y with hB
  set C : ℂ → ℝ := fun y => (heatKernel τ₁ x' y - killedHeat U τ₁ x' y) * survG U τ₂ y with hC
  have iA : Integrable A := hint (hhx.sub hhx').abs
  have iB : Integrable B := hint (hhx.sub (integrable_killedHeat_right_G hU h₁ x))
  have iC : Integrable C := hint (hhx'.sub (integrable_killedHeat_right_G hU h₁ x'))
  have iAB : Integrable fun y => A y + B y := iA.add iB
  have iABC : Integrable fun y => A y + B y + C y := iAB.add iC
  have e1 : ∫ y, (A y + B y + C y) = (∫ y, (A y + B y)) + ∫ y, C y := integral_add iAB iC
  have e2 : ∫ y, (A y + B y) = (∫ y, A y) + ∫ y, B y := integral_add iA iB
  have hpt : ∀ y, |killedHeat U τ₁ x y - killedHeat U τ₁ x' y| * survG U τ₂ y ≤
      A y + B y + C y := by
    intro y
    simp only [hA, hB, hC]
    rw [← add_mul, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hS0 y)
    have a1 := killedHeat_le_heatKernel U τ₁ x y
    have a2 := killedHeat_le_heatKernel U τ₁ x' y
    rw [abs_le]
    constructor <;> cases abs_cases (heatKernel τ₁ x y - heatKernel τ₁ x' y) <;> linarith
  refine (integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (abs_nonneg _)
    (hS0 y)) iABC (Eventually.of_forall hpt)).trans ?_
  rw [e1, e2]
  have bA := integral_abs_heat_sub_mul_survG_le hR hUR h₁ h₂ x x'
  have bB := integral_heat_sub_killed_mul_survG_le hU h₁ x hρ hω0 hω h₂
  have bC := integral_heat_sub_killed_mul_survG_le hU h₁ x' hρ hω0 hω h₂
  linarith

end ZBM
end CONF
end LQGMetric
