/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CircleMeanValue at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2

/-!
# Mean value property of `log` on circles, and circle averages of the kernels on `ℍ`

* `integral_log_norm_sub_circleUnif`: `∫ log ‖w - y‖ d(circleUnif z r) = log (max r ‖z - y‖)`.
* Circle averages of `neumannH` (folded circle) and `greenH` (circle).
* Lipschitz dependence on the centre, bounded singular log potential, admissibility.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real ComplexConjugate

namespace QuantumZipper

namespace CircleMV

/-- `circleUnif` agrees with `LQGDimension`'s `circMeas` (`[0,2π)` vs `(0,2π]`). -/
theorem circleUnif_eq_circMeas (z : ℂ) (r : ℝ) :
    circleUnif z r = LQGDimension.Coupling.circMeas z r := by
  unfold circleUnif LQGDimension.Coupling.circMeas LQGDimension.Coupling.angMeas
  rw [Measure.map_smul, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  exact (measurable_circleMap z r).aemeasurable

theorem ae_circleUnif (z : ℂ) (r : ℝ) : ∀ᵐ w ∂circleUnif z r, ‖w - z‖ = |r| := by
  rw [circleUnif_eq_circMeas]; exact LQGDimension.Coupling.ae_circMeas z r

theorem integrable_log_norm_sub_circleUnif (z y : ℂ) (r : ℝ) :
    Integrable (fun w => Real.log ‖w - y‖) (circleUnif z r) := by
  rw [circleUnif_eq_circMeas]
  simpa [norm_sub_rev] using LQGDimension.Coupling.integrable_log_norm_sub_circ y z r

theorem log_add_posLog_eq {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    Real.log r + Real.posLog (r⁻¹ * a) = Real.log (max r a) := by
  rw [Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hr.ne'
    (by positivity : (0:ℝ) < max 1 (r⁻¹ * a)).ne', mul_max_of_nonneg _ _ hr.le, mul_one,
    ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

end CircleMV

open CircleMV

/-- Mean value property of `log` on circles. -/
theorem integral_log_norm_sub_circleUnif (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ w, Real.log ‖w - y‖ ∂(circleUnif z r) = Real.log (max r ‖z - y‖) := by
  rw [circleUnif_eq_circMeas]
  have h := LQGDimension.Coupling.integral_log_norm_sub_circ y z hr
  simp only [norm_sub_rev y] at h
  rw [h, log_add_posLog_eq hr (norm_nonneg _)]

theorem neumannH_foldH (x y : ℂ) : neumannH (foldH x) y = neumannH x y := by
  unfold foldH neumannH
  split_ifs
  · rfl
  · have h1 : ‖conj x - y‖ = ‖x - conj y‖ := by
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
    have h2 : ‖conj x - conj y‖ = ‖x - y‖ := by
      rw [← map_sub, Complex.norm_conj]
    rw [h1, h2]; ring

theorem integral_neumannH_foldedCircle (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ x, neumannH x y ∂(foldedCircle z r) =
      -Real.log (max r ‖z - y‖) - Real.log (max r ‖z - conj y‖) := by
  have hm : Measurable fun x => neumannH x y :=
    measurable_neumannH.comp (measurable_id.prodMk measurable_const)
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable hm.aestronglyMeasurable]
  simp only [neumannH_foldH]
  unfold neumannH
  rw [integral_sub (f := fun w => -Real.log ‖w - y‖) (integrable_log_norm_sub_circleUnif z y r).neg
    (integrable_log_norm_sub_circleUnif z (conj y) r), integral_neg,
    integral_log_norm_sub_circleUnif z y hr, integral_log_norm_sub_circleUnif z _ hr]

theorem integral_greenH_circleUnif (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ x, greenH x y ∂(circleUnif z r) =
      Real.log (max r ‖z - conj y‖) - Real.log (max r ‖z - y‖) := by
  unfold greenH
  rw [integral_sub (integrable_log_norm_sub_circleUnif z (conj y) r)
    (integrable_log_norm_sub_circleUnif z y r),
    integral_log_norm_sub_circleUnif z y hr, integral_log_norm_sub_circleUnif z _ hr]

/-- A circle that stays in `Hbar` is not affected by folding. (`0 ≤ r` is needed: for `r < 0`
`circleUnif z r` is the circle of radius `|r|`.) -/
theorem foldedCircle_eq_circleUnif {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hrz : r ≤ z.im) :
    foldedCircle z r = circleUnif z r := by
  unfold foldedCircle
  conv_rhs => rw [← Measure.map_id (μ := circleUnif z r)]
  refine Measure.map_congr ?_
  filter_upwards [ae_circleUnif z r] with w hw
  have him : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  rw [hw, abs_of_nonneg hr, Complex.sub_im] at him
  have : 0 ≤ w.im := by linarith [neg_abs_le (w.im - z.im)]
  simp [foldH, this]

/-! ## Lipschitz dependence on the centre -/

theorem CircleMV.log_sub_log_le {r u v : ℝ} (hr : 0 < r) (hu : r ≤ u) (hv : r ≤ v) :
    Real.log u - Real.log v ≤ |u - v| / r := by
  have hu0 : 0 < u := hr.trans_le hu
  have hv0 : 0 < v := hr.trans_le hv
  rcases le_or_gt u v with huv | huv
  · have : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
    have : 0 ≤ |u - v| / r := by positivity
    linarith
  · rw [← Real.log_div hu0.ne' hv0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hu0 hv0)).trans ?_
    rw [abs_of_pos (by linarith), div_sub_one hv0.ne']
    exact div_le_div_of_nonneg_left (by linarith) hr hv

theorem abs_log_max_sub_le (z w y : ℂ) {r : ℝ} (hr : 0 < r) :
    |Real.log (max r ‖z - y‖) - Real.log (max r ‖w - y‖)| ≤ ‖z - w‖ / r := by
  have hmax : |max r ‖z - y‖ - max r ‖w - y‖| ≤ ‖z - w‖ := by
    rw [max_comm r, max_comm r]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := abs_norm_sub_norm_le (z - y) (w - y)
    rwa [sub_sub_sub_cancel_right] at this
  have h1 := CircleMV.log_sub_log_le hr (le_max_left r ‖z - y‖) (le_max_left r ‖w - y‖)
  have h2 := CircleMV.log_sub_log_le hr (le_max_left r ‖w - y‖) (le_max_left r ‖z - y‖)
  rw [abs_sub_comm] at h2
  have h3 : |max r ‖z - y‖ - max r ‖w - y‖| / r ≤ ‖z - w‖ / r :=
    div_le_div_of_nonneg_right hmax hr.le
  rw [abs_sub_le_iff]; constructor <;> linarith

theorem abs_integral_neumannH_foldedCircle_sub_le (z w y : ℂ) {r : ℝ} (hr : 0 < r) :
    |∫ x, neumannH x y ∂(foldedCircle z r) - ∫ x, neumannH x y ∂(foldedCircle w r)| ≤
      2 * ‖z - w‖ / r := by
  rw [integral_neumannH_foldedCircle z y hr, integral_neumannH_foldedCircle w y hr]
  have h1 := abs_log_max_sub_le z w y hr
  have h2 := abs_log_max_sub_le z w (conj y) hr
  have : -Real.log (max r ‖z - y‖) - Real.log (max r ‖z - conj y‖) -
      (-Real.log (max r ‖w - y‖) - Real.log (max r ‖w - conj y‖)) =
      -((Real.log (max r ‖z - y‖) - Real.log (max r ‖w - y‖)) +
        (Real.log (max r ‖z - conj y‖) - Real.log (max r ‖w - conj y‖))) := by ring
  rw [this, abs_neg]
  refine (abs_add_le _ _).trans ?_
  rw [mul_div_assoc]; linarith

/-! ## Bounded singular logarithmic potential -/

theorem lintegral_negLog_circleUnif_le (z : ℂ) {r : ℝ} (hr : 0 < r) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(circleUnif z r) ≤
      ENNReal.ofReal (Real.log 2 + |Real.log r|) := by
  set M := max r ‖z - y‖ with hM
  have hM0 : 0 < M := hr.trans_le (le_max_left _ _)
  have hlogM : Real.log r ≤ Real.log M := Real.log_le_log hr (le_max_left _ _)
  set c := Real.log 2 + |Real.log r| + Real.log M with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    have := neg_abs_le (Real.log r)
    linarith
  have hint := (integrable_const c).sub (integrable_log_norm_sub_circleUnif z y r)
  have hnn : 0 ≤ᵐ[circleUnif z r] fun x => c - Real.log ‖x - y‖ := by
    filter_upwards [ae_circleUnif z r] with x hx
    rw [abs_of_pos hr] at hx
    have hle : ‖x - y‖ ≤ 2 * M := by
      calc ‖x - y‖ = ‖(x - z) + (z - y)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
        _ ≤ 2 * M := by rw [hx]; linarith [le_max_left r ‖z - y‖, le_max_right r ‖z - y‖]
    show 0 ≤ c - Real.log ‖x - y‖
    rcases (norm_nonneg (x - y)).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; linarith
    · have := Real.log_le_log h0 hle
      rw [Real.log_mul (by norm_num) hM0.ne'] at this
      have := neg_abs_le (Real.log r)
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      have := abs_nonneg (Real.log r)
      linarith [hc]
  calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(circleUnif z r)
      ≤ ∫⁻ x, ENNReal.ofReal (c - Real.log ‖x - y‖) ∂(circleUnif z r) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (∫ x, (c - Real.log ‖x - y‖) ∂(circleUnif z r)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (Real.log 2 + |Real.log r|) := by
        rw [integral_sub (integrable_const c) (integrable_log_norm_sub_circleUnif z y r),
          integral_const, integral_log_norm_sub_circleUnif z y hr]
        simp only [probReal_univ, one_smul, hc, hM]
        ring_nf

theorem CircleMV.norm_foldH_sub_conj (w y : ℂ) :
    ‖conj w - y‖ = ‖w - conj y‖ := by
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj]

theorem lintegral_negLog_foldedCircle_le (z : ℂ) {r : ℝ} (hr : 0 < r) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(foldedCircle z r) ≤
      2 * ENNReal.ofReal (Real.log 2 + |Real.log r|) := by
  have hm : Measurable fun x : ℂ => ENNReal.ofReal (-Real.log ‖x - y‖) := by fun_prop
  rw [foldedCircle, lintegral_map hm measurable_foldH, two_mul]
  calc ∫⁻ w, ENNReal.ofReal (-Real.log ‖foldH w - y‖) ∂(circleUnif z r)
      ≤ ∫⁻ w, (ENNReal.ofReal (-Real.log ‖w - y‖) +
          ENNReal.ofReal (-Real.log ‖w - conj y‖)) ∂(circleUnif z r) := by
        refine lintegral_mono fun w => ?_
        unfold foldH
        split_ifs
        · exact le_self_add
        · rw [CircleMV.norm_foldH_sub_conj]; exact le_add_self
    _ = _ := lintegral_add_left hm _
    _ ≤ _ := add_le_add (lintegral_negLog_circleUnif_le z hr y)
        (lintegral_negLog_circleUnif_le z hr (conj y))

/-! ## Admissibility and measurability in the centre -/

theorem isAdmissibleH_foldedCircle {z : ℂ} {r : ℝ} (_hz : z ∈ Hbar) (hr : 0 < r) :
    IsAdmissibleH (foldedCircle z r) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · set K := Metric.closedBall (0 : ℂ) (‖z‖ + r) ∩ Hbar
    have hK : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
    refine ⟨K, hK, Set.inter_subset_right, ?_⟩
    have : ∀ᵐ w ∂foldedCircle z r, w ∈ K := by
      rw [foldedCircle]
      refine (ae_map_iff measurable_foldH.aemeasurable hK.measurableSet).mpr ?_
      filter_upwards [ae_circleUnif z r] with w hw
      have hn : ‖foldH w‖ = ‖w‖ := by
        unfold foldH; split_ifs
        · rfl
        · exact Complex.norm_conj w
      have hH : foldH w ∈ Hbar := by
        unfold foldH Hbar; split_ifs with h
        · exact h
        · show 0 ≤ (conj w).im
          rw [Complex.conj_im]; linarith
      refine ⟨?_, hH⟩
      rw [Metric.mem_closedBall, dist_zero_right, hn]
      calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + r := by rw [hw, abs_of_pos hr]; ring
    exact ae_iff.mp this
  · exact ⟨_, ENNReal.mul_lt_top ENNReal.ofNat_lt_top ENNReal.ofReal_lt_top,
      lintegral_negLog_foldedCircle_le z hr⟩

theorem measurable_foldedCircle_apply (r : ℝ) {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable fun w => foldedCircle w r A := by
  have hS : MeasurableSet (foldH ⁻¹' A) := measurable_foldH hA
  have hc : Measurable fun p : ℂ × ℝ => circleMap p.1 r p.2 :=
    (by unfold circleMap; fun_prop : Continuous fun p : ℂ × ℝ => circleMap p.1 r p.2).measurable
  have key : ∀ w, foldedCircle w r A = (ENNReal.ofReal (2 * π))⁻¹ *
      ∫⁻ θ, (foldH ⁻¹' A).indicator 1 (circleMap w r θ) ∂(volume.restrict (Set.Ico 0 (2 * π))) := by
    intro w
    rw [foldedCircle, Measure.map_apply measurable_foldH hA, circleUnif, Measure.smul_apply,
      smul_eq_mul, ← lintegral_indicator_one hS,
      lintegral_map (measurable_one.indicator hS) (measurable_circleMap w r)]
  simp_rw [key]
  exact ((measurable_one.indicator hS).comp hc).lintegral_prod_right'.const_mul _

end QuantumZipper
