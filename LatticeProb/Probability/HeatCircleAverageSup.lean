import LatticeProb.Probability.HeatCircleAverageVariance
import LatticeProb.Probability.GaussianBlockTail
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.LemmaA1

/-!
# Uniform comparison of the heat-kernel mollification and the circle average

Let `h` be a whole-plane Gaussian free field normalized by `h_1(0) = 0`, `h*_ε` its heat-kernel
mollification (kernel `p_{ε²/2}`) and `h_ε` its circle average process. The difference
`R_ε(z) = h*_ε(z) − h_ε(z)` has a law that does not depend on the additive normalization, a
bounded variance (`heatCircleVarConst`), and increments `E(R_ε(z) − R_ε(w))² ≤ 4(√π + 1)|z − w|/ε`.
Gaussian chaining on discs of radius `10 ε` and a union bound over an `ε`-grid give

  `P(sup_{|z| ≤ 3} |R_ε(z)| > M √(log ε⁻¹)) ≤ η`  for all `ε ∈ (0, 1/2)`,

for every `η > 0` and a constant `M = M(η)`, i.e. `sup_{|z| ≤ 3} |h*_ε − h_ε| = O_P(√(log ε⁻¹))`.
The supremum is taken along any version of `R_ε` with almost surely continuous paths.

## Main results

* `isGaussianProcess_of_ae_eq_heatMollify_sub_circleAvg`,
  `variance_sub_le_of_ae_eq_heatMollify_sub_circleAvg`: a version of `R_ε` is a centred
  Gaussian process with increments Lipschitz in `L²` at scale `ε`;
* `measure_exists_ball_gt_le_of_ae_eq_heatMollify_sub_circleAvg`: the block tail on a disc;
* `measure_exists_norm_le_three_gt_le`: the union bound over the grid, for a fixed level;
* `exists_M_heatMollify_sub_circleAvg`: the `O_P(√(log ε⁻¹))` bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal

noncomputable section

namespace LQGMetric.HeatCircle

open LQGDimension.Osc37

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `h*_ε(z) − h_ε(z)` is centred. -/
lemma integral_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) : ∫ ω, (heatMollify ε (h ω) z - circleAvg (h ω) ε z) ∂P = 0 := by
  obtain ⟨V, hV, -⟩ := exists_gaussianReal_heatMollify_sub_circleAvg_le hh hε z
  have hm := measurable_heatMollify_sub_circleAvg hh.1 ε z
  calc ∫ ω, (heatMollify ε (h ω) z - circleAvg (h ω) ε z) ∂P
      = ∫ x, x ∂(P.map fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) :=
        (integral_map hm.aemeasurable aestronglyMeasurable_id).symm
    _ = 0 := by rw [hV, integral_id_gaussianReal]

variable {ε : ℝ} {Y : ℂ → Ω → ℝ}

/-- A process that is, at every point, almost surely equal to `h*_ε − h_ε` is a Gaussian
process. -/
lemma isGaussianProcess_of_ae_eq_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (hε : 0 < ε)
    (hY : ∀ z, Y z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) :
    IsGaussianProcess Y P := by
  have := hh.1.gaussian.isProbabilityMeasure
  exact ((isGaussianProcess_heatMollify_sub_circleAvg hh.1).comp_right
    fun z : ℂ => ((⟨ε, hε⟩ : Ioi (0 : ℝ)), z)).congr fun z => (hY z).symm

/-- A version of `h*_ε − h_ε` is centred. -/
lemma integral_eq_zero_of_ae_eq_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (hε : 0 < ε)
    (hY : ∀ z, Y z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) (z : ℂ) :
    ∫ ω, Y z ω ∂P = 0 := by
  rw [integral_congr_ae (hY z)]
  exact integral_heatMollify_sub_circleAvg hh hε z

/-- Increments of a version of `R_ε = h*_ε − h_ε`: `Var(R_ε(z) − R_ε(w)) ≤ 4(√π + 1)|z − w|/ε`. -/
lemma variance_sub_le_of_ae_eq_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (hε : 0 < ε)
    (hY : ∀ z, Y z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) (z w : ℂ) :
    Var[fun ω => Y z ω - Y w ω; P] ≤ 4 * (√π + 1) * ‖z - w‖ / ε := by
  have := hh.1.gaussian.isProbabilityMeasure
  have hX := isGaussianProcess_of_ae_eq_heatMollify_sub_circleAvg hh hε hY
  have hint : ∫ ω, (Y z ω - Y w ω) ∂P = 0 := by
    rw [integral_sub (hX.hasGaussianLaw_eval z).integrable (hX.hasGaussianLaw_eval w).integrable,
      integral_eq_zero_of_ae_eq_heatMollify_sub_circleAvg hh hε hY z,
      integral_eq_zero_of_ae_eq_heatMollify_sub_circleAvg hh hε hY w, sub_zero]
  have hD : (fun ω => (Y z ω - Y w ω) ^ 2) =ᵐ[P] fun ω =>
      ((heatMollify ε (h ω) z - circleAvg (h ω) ε z) -
        (heatMollify ε (h ω) w - circleAvg (h ω) ε w)) ^ 2 := by
    filter_upwards [hY z, hY w] with ω h1 h2
    rw [h1, h2]
  have hmz := measurable_heatMollify_sub_circleAvg hh.1 ε z
  have hmw := measurable_heatMollify_sub_circleAvg hh.1 ε w
  have hB : 0 ≤ 4 * (√π + 1) * ‖z - w‖ / ε := by positivity
  calc Var[fun ω => Y z ω - Y w ω; P] = ∫ ω, (Y z ω - Y w ω) ^ 2 ∂P :=
        variance_of_integral_eq_zero ((hX.aemeasurable z).sub (hX.aemeasurable w)) hint
    _ = ∫ ω, ((heatMollify ε (h ω) z - circleAvg (h ω) ε z) -
          (heatMollify ε (h ω) w - circleAvg (h ω) ε w)) ^ 2 ∂P := integral_congr_ae hD
    _ = (∫⁻ ω, ENNReal.ofReal (((heatMollify ε (h ω) z - circleAvg (h ω) ε z) -
          (heatMollify ε (h ω) w - circleAvg (h ω) ε w)) ^ 2) ∂P).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
          ((hmz.sub hmw).pow_const 2).aestronglyMeasurable
    _ ≤ 4 * (√π + 1) * ‖z - w‖ / ε :=
        ENNReal.toReal_le_of_le_ofReal hB
          (lintegral_sq_heatMollify_sub_circleAvg_incr_le hh hε z w)

/-- **Block tail of `h*_ε − h_ε` on a disc of radius `10 ε`**, along a version with almost
surely continuous paths. -/
theorem measure_exists_ball_gt_le_of_ae_eq_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (hε : 0 < ε)
    (hY : ∀ z, Y z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z)
    (hYc : ∀ᵐ ω ∂P, Continuous fun z => Y z ω) (g : ℂ) {t : ℝ}
    (ht : √(4 * (√π + 1) / 2) * chainConst ≤ t) :
    P {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |Y u ω - Y g ω|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-2 * (t / √(4 * (√π + 1) / 2) - chainConst) ^ 2 / (π ^ 2 * 20))) :=
  GaussianBlockTail.measure_exists_ball_abs_sub_gt_le
    (isGaussianProcess_of_ae_eq_heatMollify_sub_circleAvg hh hε hY)
    (integral_eq_zero_of_ae_eq_heatMollify_sub_circleAvg hh hε hY) hYc (by positivity) hε
    (variance_sub_le_of_ae_eq_heatMollify_sub_circleAvg hh hε hY) g ht

/-- **Union bound over the `ε`-grid.** For a version `Y` of `h*_ε − h_ε` with almost surely
continuous paths, `ε ∈ (0, 1]` and `t ≥ √(2(√π + 1)) c`,
`P(∃ z, |z| ≤ 3 ∧ |Y z| > 2t) ≤ (121/ε²) (2 e^{-t²/(2V₀)} + 2 e^{-2 (t/√(2(√π+1)) - c)²/(20π²)})`. -/
theorem measure_exists_norm_le_three_gt_le
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hY : ∀ z, Y z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z)
    (hYc : ∀ᵐ ω ∂P, Continuous fun z => Y z ω) {t : ℝ}
    (ht : √(4 * (√π + 1) / 2) * chainConst ≤ t) :
    P {ω | ∃ z : ℂ, ‖z‖ ≤ 3 ∧ 2 * t < |Y z ω|} ≤
      ENNReal.ofReal (121 / ε ^ 2 * (2 * Real.exp (-(t ^ 2 / (2 * heatCircleVarConst))) +
        2 * Real.exp (-2 * (t / √(4 * (√π + 1) / 2) - chainConst) ^ 2 / (π ^ 2 * 20)))) := by
  have hcc : 0 < chainConst := by unfold chainConst; positivity
  have ha0 : 0 < √(4 * (√π + 1) / 2) := Real.sqrt_pos.2 (by positivity)
  have ht0 : 0 < t := (mul_pos ha0 hcc).trans_le ht
  have hb1 : 0 ≤ 2 * Real.exp (-(t ^ 2 / (2 * heatCircleVarConst))) := by positivity
  have hb2 : 0 ≤ 2 * Real.exp (-2 * (t / √(4 * (√π + 1) / 2) - chainConst) ^ 2 / (π ^ 2 * 20)) :=
    by positivity
  have hsub : {ω | ∃ z : ℂ, ‖z‖ ≤ 3 ∧ 2 * t < |Y z ω|} ⊆
      ⋃ g ∈ grid ε, ({ω | t ≤ |Y g ω|} ∪
        {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |Y u ω - Y g ω|}) := by
    rintro ω ⟨z, hz, hlt⟩
    obtain ⟨g, hg, hzg⟩ := exists_grid hε hz
    refine mem_iUnion₂.2 ⟨g, hg, ?_⟩
    by_cases hgt : t ≤ |Y g ω|
    · exact Or.inl hgt
    · refine Or.inr ⟨z, by linarith, ?_⟩
      have := abs_sub_abs_le_abs_sub (Y z ω) (Y g ω)
      have hgt' := not_le.1 hgt
      linarith
  have hpt : ∀ g, P {ω | t ≤ |Y g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * heatCircleVarConst)))) := by
    intro g
    have hcongr : P {ω | t ≤ |Y g ω|} =
        P {ω | t ≤ |heatMollify ε (h ω) g - circleAvg (h ω) ε g|} := by
      refine measure_congr ?_
      filter_upwards [hY g] with ω hω
      rw [hω]
    rw [hcongr]
    exact measure_abs_heatMollify_sub_circleAvg_ge_le hh hε g ht0
  calc P _ ≤ P (⋃ g ∈ grid ε, ({ω | t ≤ |Y g ω|} ∪
        {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |Y u ω - Y g ω|})) := measure_mono hsub
    _ ≤ ∑ g ∈ grid ε, P ({ω | t ≤ |Y g ω|} ∪
        {ω | ∃ u : ℂ, ‖u - g‖ < 10 * ε ∧ t < |Y u ω - Y g ω|}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ grid ε, ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * heatCircleVarConst))) +
          2 * Real.exp (-2 * (t / √(4 * (√π + 1) / 2) - chainConst) ^ 2 / (π ^ 2 * 20))) :=
        Finset.sum_le_sum fun g _ => (measure_union_le _ _).trans
          ((add_le_add (hpt g) (measure_exists_ball_gt_le_of_ae_eq_heatMollify_sub_circleAvg
            hh hε hY hYc g ht)).trans_eq (ENNReal.ofReal_add hb1 hb2).symm)
    _ = ENNReal.ofReal ((grid ε).card *
          (2 * Real.exp (-(t ^ 2 / (2 * heatCircleVarConst))) +
          2 * Real.exp (-2 * (t / √(4 * (√π + 1) / 2) - chainConst) ^ 2 / (π ^ 2 * 20)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (card_grid_le hε hε1) (add_nonneg hb1 hb2))

/-- **`h*_ε − h_ε = O_P(√(log ε⁻¹))` uniformly on the disc of radius `3`.** For every `η > 0`
there is `M > 0` such that for every `ε ∈ (0, 1/2)` and every version `Y` of `h*_ε − h_ε` with
almost surely continuous paths, `P(∃ z, |z| ≤ 3 ∧ |Y z| > M √(log ε⁻¹)) ≤ η`. -/
theorem exists_M_heatMollify_sub_circleAvg
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {η : ℝ} (hη : 0 < η) :
    ∃ M > 0, ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹, ∀ Y : ℂ → Ω → ℝ,
      (∀ z, Y z =ᵐ[P] fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) →
      (∀ᵐ ω ∂P, Continuous fun z => Y z ω) →
      P {ω | ∃ z : ℂ, ‖z‖ ≤ 3 ∧ M * √(Real.log ε⁻¹) < |Y z ω|} ≤ ENNReal.ofReal η := by
  have hV := heatCircleVarConst_pos
  have hcc : 0 < chainConst := by unfold chainConst; positivity
  set a : ℝ := √(4 * (√π + 1) / 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hpi := Real.pi_pos
  set c : ℝ := min (1 / (2 * heatCircleVarConst)) (1 / (10 * π ^ 2 * a ^ 2)) with hc
  have hc0 : 0 < c := lt_min (one_div_pos.2 (mul_pos two_pos hV))
    (one_div_pos.2 (mul_pos (mul_pos (by norm_num) (pow_pos hpi 2)) (pow_pos ha0 2)))
  obtain ⟨M, hM0, hM⟩ := HigherDimLFPP.LemmaA1.exists_M hc0 (mul_nonneg ha0.le hcc.le)
    (show 0 < 49 * η / 121 by linarith)
  refine ⟨M, hM0, fun ε hε Y hY hYc => ?_⟩
  obtain ⟨hε0, hε2⟩ := hε
  obtain ⟨h2c, hbound⟩ := hM ε ⟨hε0, hε2⟩
  set T : ℝ := M * √(Real.log ε⁻¹) / 3 with hT
  have hT0 : 0 < T := (mul_pos two_pos (mul_pos ha0 hcc)).trans_le h2c
  have htT : a * chainConst ≤ T := by linarith [mul_pos ha0 hcc]
  have hmain := measure_exists_norm_le_three_gt_le hh hε0 (by linarith) hY hYc htT
  have hsub : {ω | ∃ z : ℂ, ‖z‖ ≤ 3 ∧ M * √(Real.log ε⁻¹) < |Y z ω|} ⊆
      {ω | ∃ z : ℂ, ‖z‖ ≤ 3 ∧ 2 * T < |Y z ω|} := by
    rintro ω ⟨z, hz, hlt⟩
    exact ⟨z, hz, by linarith⟩
  refine (measure_mono hsub).trans (hmain.trans (ENNReal.ofReal_le_ofReal ?_))
  have hT1 : 0 ≤ T - a * chainConst := by linarith
  have hTle : (T - a * chainConst) ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ hT1 (by linarith [mul_pos ha0 hcc]) 2
  have hE1 : Real.exp (-(T ^ 2 / (2 * heatCircleVarConst))) ≤
      Real.exp (-(c * (T - a * chainConst) ^ 2)) := by
    apply Real.exp_le_exp.2
    have h1 : c ≤ 1 / (2 * heatCircleVarConst) := min_le_left _ _
    have h2 : c * (T - a * chainConst) ^ 2 ≤ 1 / (2 * heatCircleVarConst) * T ^ 2 :=
      mul_le_mul h1 hTle (sq_nonneg _) (one_div_pos.2 (mul_pos two_pos hV)).le
    have h3 : T ^ 2 / (2 * heatCircleVarConst) = 1 / (2 * heatCircleVarConst) * T ^ 2 := by ring
    linarith
  have hE2 : Real.exp (-2 * (T / a - chainConst) ^ 2 / (π ^ 2 * 20)) ≤
      Real.exp (-(c * (T - a * chainConst) ^ 2)) := by
    apply Real.exp_le_exp.2
    have ha0' := ha0.ne'
    have hpi' := hpi.ne'
    have hrw : -2 * (T / a - chainConst) ^ 2 / (π ^ 2 * 20) =
        -(1 / (10 * π ^ 2 * a ^ 2) * (T - a * chainConst) ^ 2) := by
      field_simp
      ring
    rw [hrw]
    have h1 : c ≤ 1 / (10 * π ^ 2 * a ^ 2) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (T - a * chainConst))
    linarith
  have hE0 : 0 ≤ Real.exp (-(c * (T - a * chainConst) ^ 2)) := (Real.exp_pos _).le
  have hε2' : 0 < 121 / ε ^ 2 := by positivity
  calc 121 / ε ^ 2 * (2 * Real.exp (-(T ^ 2 / (2 * heatCircleVarConst))) +
        2 * Real.exp (-2 * (T / a - chainConst) ^ 2 / (π ^ 2 * 20)))
      ≤ 121 / ε ^ 2 * (6 * Real.exp (-(c * (T - a * chainConst) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hε2'.le
        linarith
    _ = 121 / 49 * (49 / ε ^ 2 * (6 * Real.exp (-(c * (T - a * chainConst) ^ 2)))) := by
        field_simp
    _ ≤ 121 / 49 * (49 * η / 121) := by gcongr
    _ = η := by ring

end LQGMetric.HeatCircle
