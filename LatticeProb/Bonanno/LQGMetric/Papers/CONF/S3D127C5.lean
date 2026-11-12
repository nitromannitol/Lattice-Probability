/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4(c) replaced: short-time survival in the interior, and heat convolutions
(packet P-127C)

* `one_sub_bridgeStay_ball_le` (adapted from `DZZ.killedHeat_sub_inter_ball_le`, which treats
  the loop `v → v`; here the bridge `v → w` with `|w − v| ≤ r/3`, same reflection-principle
  argument, DZZ l. 491–499 / 557): `1 − q_{B(v,r)}(t; v, w) ≤ 4 e^{-2(r/4)²/t}`;
* `one_le_killedSurv_add` : if `B(x, d) ⊆ U` then `1 ≤ P^x(τ_U > t) + err d t` with
  `err d t = 4 e^{-2(d/12)²/t} + 2 e^{-(d/3)²/(4t)}` (so `P^x(τ_U ≤ t) → 0` as `t → 0`,
  uniformly on `{x : B(x, d) ⊆ U}`);
* `continuous_heatConv`: `x ↦ ∫ p_t(x, v) g(v) dv` is continuous for bounded measurable `g`
  (dominated convergence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

/-- The bridge from `v` to `w` (`|w − v| ≤ r/3`) leaves `B(v, r)` with probability
`≤ 4 e^{-2(r/4)²/t}` (adapted from `DZZ.killedHeat_sub_inter_ball_le`). -/
theorem one_sub_bridgeStay_ball_le {t : ℝ≥0} (ht : t ≠ 0) {v w : ℂ} {r : ℝ} (hr : 0 < r)
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

/-- The short-time exit error `4 e^{-2(d/4)²/t} + 2 e^{-(d/3)²/(4t)}`. -/
def exitErr (d t : ℝ) : ℝ :=
  4 * Real.exp (-(2 * (d / 4) ^ 2 / t)) + 2 * Real.exp (-(d / 3) ^ 2 / (4 * t))

lemma exitErr_nonneg (d t : ℝ) : 0 ≤ exitErr d t := by unfold exitErr; positivity

/-- **Short-time survival in the interior**: `B(x, d) ⊆ U` gives `1 ≤ P^x(τ_U > t) + err`. -/
theorem one_le_killedSurv_add {U : Set ℂ} {t : ℝ≥0} (ht : t ≠ 0) {x : ℂ} {d : ℝ} (hd : 0 < d)
    (hball : ball x d ⊆ U) : 1 ≤ killedSurv U t x + ENNReal.ofReal (exitErr d t) := by
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  set N : Set ℂ := {w | dist w x ≤ d / 3} with hN
  have hNm : MeasurableSet N := measurableSet_le (measurable_id.dist measurable_const)
    measurable_const
  set e1 : ℝ := 4 * Real.exp (-(2 * (d / 4) ^ 2 / t)) with he1
  have hhm : Measurable fun y ↦ ENNReal.ofReal (heatKernel t x y) :=
    (measurable_heatKernel_right _ x).ennreal_ofReal
  rw [← lintegral_ofReal_heatKernel_eq_one ht' x,
    ← lintegral_add_compl (μ := (volume : Measure ℂ)) (fun y ↦ ENNReal.ofReal (heatKernel t x y))
      hNm]
  have hfar : ∫⁻ y in Nᶜ, ENNReal.ofReal (heatKernel t x y) ≤
      ENNReal.ofReal (2 * Real.exp (-(d / 3) ^ 2 / (4 * t))) :=
    lintegral_far_heatKernel_le ht' (by linarith) x _ fun w hw ↦ by
      simp only [hN, mem_compl_iff, mem_ofPred_eq, not_le] at hw
      exact hw.le
  have hpt : ∀ y ∈ N, ENNReal.ofReal (heatKernel t x y) ≤
      ENNReal.ofReal (killedHeat U t x y) + ENNReal.ofReal e1 * ENNReal.ofReal (heatKernel t x y) := by
    intro y hy
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (killedHeat_nonneg _ _ _ _)
        (mul_nonneg (by positivity) (heatKernel_nonneg' t x y))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq := one_sub_bridgeStay_ball_le ht (v := x) (w := y) hd
      (by rw [← dist_eq_norm]; exact hy)
    have hmono := bridgeStay_mono hball t x y
    have hp := heatKernel_nonneg' t x y
    rw [killedHeat]
    have h1 : 1 - bridgeStay U t x y ≤ e1 := by rw [he1]; linarith
    nlinarith
  have hnear : ∫⁻ y in N, ENNReal.ofReal (heatKernel t x y) ≤
      killedSurv U t x + ENNReal.ofReal e1 := by
    calc ∫⁻ y in N, ENNReal.ofReal (heatKernel t x y)
        ≤ ∫⁻ y in N, (ENNReal.ofReal (killedHeat U t x y) +
            ENNReal.ofReal e1 * ENNReal.ofReal (heatKernel t x y)) :=
          setLIntegral_mono' hNm hpt
      _ = (∫⁻ y in N, ENNReal.ofReal (killedHeat U t x y)) +
            ∫⁻ y in N, ENNReal.ofReal e1 * ENNReal.ofReal (heatKernel t x y) :=
          lintegral_add_right _ (hhm.const_mul _)
      _ ≤ killedSurv U t x + ENNReal.ofReal e1 * 1 := by
          refine add_le_add (setLIntegral_le_lintegral _ _) ?_
          rw [lintegral_const_mul _ hhm, ← lintegral_ofReal_heatKernel_eq_one ht' x]
          exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = killedSurv U t x + ENNReal.ofReal e1 := by rw [mul_one]
  calc (∫⁻ y in N, ENNReal.ofReal (heatKernel t x y)) +
        ∫⁻ y in Nᶜ, ENNReal.ofReal (heatKernel t x y)
      ≤ killedSurv U t x + ENNReal.ofReal e1 +
          ENNReal.ofReal (2 * Real.exp (-(d / 3) ^ 2 / (4 * t))) := add_le_add hnear hfar
    _ = killedSurv U t x + ENNReal.ofReal (exitErr d t) := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rfl

/-- **Heat convolutions are continuous**: `x ↦ ∫ p_t(x, v) g(v) dv` for bounded measurable `g`. -/
theorem continuous_heatConv {t : ℝ} (ht : 0 < t) {g : ℂ → ℝ} (hg : AEStronglyMeasurable g)
    {M : ℝ} (hM : ∀ v, |g v| ≤ M) : Continuous fun x ↦ ∫ v, heatKernel t x v * g v := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine continuousAt_of_dominated (bound := fun v ↦
      M * (2 * Real.exp ((2 * t)⁻¹) * heatKernel (2 * t) x0 v)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x ↦
      ((measurable_heatKernel_right _ x).aestronglyMeasurable).mul hg
  · filter_upwards [ball_mem_nhds x0 one_pos] with x hx
    refine Eventually.of_forall fun v ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg t ht.le x v), mul_comm]
    refine mul_le_mul (hM v) ?_ (heatKernel_nonneg t ht.le x v) hM0
    have hxx : ‖x - x0‖ < 1 := by rw [← dist_eq_norm]; exact hx
    have htri : ‖x0 - v‖ ≤ ‖x - v‖ + ‖x - x0‖ := by
      calc ‖x0 - v‖ = ‖(x - v) - (x - x0)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have hsq : ‖x0 - v‖ ^ 2 ≤ 2 * ‖x - v‖ ^ 2 + 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have hb2 : ‖x - x0‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - x0)]
      nlinarith [sq_nonneg (‖x - v‖ - ‖x - x0‖)]
    unfold heatKernel
    have e : 2 * Real.exp ((2 * t)⁻¹) * ((2 * Real.pi * (2 * t))⁻¹ *
        Real.exp (-‖x0 - v‖ ^ 2 / (2 * (2 * t)))) =
        (2 * Real.pi * t)⁻¹ * Real.exp ((2 * t)⁻¹ + -‖x0 - v‖ ^ 2 / (2 * (2 * t))) := by
      rw [Real.exp_add]; field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have key : -‖x - v‖ ^ 2 / (2 * t) = (-(2 * ‖x - v‖ ^ 2)) / (4 * t) := by
      field_simp; ring
    have key2 : (2 * t)⁻¹ + -‖x0 - v‖ ^ 2 / (2 * (2 * t)) = (2 - ‖x0 - v‖ ^ 2) / (4 * t) := by
      field_simp; ring
    rw [key, key2]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · exact ((integrable_heatKernel _ (by positivity) x0).const_mul _).const_mul _
  · exact Eventually.of_forall fun v ↦ by
      have : Continuous fun x : ℂ ↦ heatKernel t x v := by unfold heatKernel; fun_prop
      exact (this.mul continuous_const).continuousAt

end ZBM
end CONF
end LQGMetric
