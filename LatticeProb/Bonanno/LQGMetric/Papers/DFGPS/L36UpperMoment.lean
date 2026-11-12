/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperMoment at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperScale
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25Gauss
import Mathlib.Analysis.MeanInequalitiesPow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
For the boundary layer of DFGPS Lemma 3.6 (D52) we bound, with probability → 1, the sums
`Σ_k r_k^{ξQ} e^{ξ h_{r_k}(c)}` over dyadic scales and `Σ_v e^{ξ h_δ(v)}` over a straight walk of
`≈ δ^{−a}` vertices. Own elementary argument (DEVIATIONS DV-DFC2-1): Markov's inequality for the
`θ`-th moment, `θ ∈ (0,1]`, with `(Σ x_i)^θ ≤ Σ x_i^θ` and the Gaussian exponential moment
`E e^{s h_ρ(z)} = e^{s² Var h_ρ(z)/2}` (`DG.lintegral_exp_circleAvg`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open LQGDimension (IsGFFCircleAverage)

/-- `(Σ x_i)^θ ≤ Σ x_i^θ` for `x_i ≥ 0`, `θ ∈ [0,1]` -/
lemma rpow_finsetSum_le {ι : Type*} (F : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : (∑ i ∈ F, x i) ^ θ ≤ ∑ i ∈ F, x i ^ θ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Real.zero_rpow hθ0.ne']
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hF : 0 ≤ ∑ i ∈ F, x i := Finset.sum_nonneg fun i _ => hx i
    have := NNReal.rpow_add_le_add_rpow ⟨x a, hx a⟩ ⟨_, hF⟩ hθ0.le hθ1
    have h2 : (x a + ∑ i ∈ F, x i) ^ θ ≤ x a ^ θ + (∑ i ∈ F, x i) ^ θ := by
      have := NNReal.coe_le_coe.2 this
      simp only [NNReal.coe_rpow, NNReal.coe_add] at this
      exact this
    linarith

/-- **Fractional-moment tail bound.** For `θ ∈ (0,1]`, `T > 0`, weights `w_i ≥ 0`:
`P[Σ_i w_i e^{ξ h_{ρ_i}(z_i)} > T] ≤ T^{−θ} Σ_i w_i^θ e^{(θξ)² Var h_{ρ_i}(z_i) / 2}`. -/
theorem prob_sum_exp_gt_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℝ → ℂ → Ω → ℝ} (hH : IsGFFCircleAverage H P) {ι : Type*} (F : Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (z : ι → ℂ) (ξ : ℝ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {T : ℝ} (hT : 0 < T) :
    P {ω | T < ∑ i ∈ F, w i * Real.exp (ξ * H (ρ i) (z i) ω)} ≤
      ENNReal.ofReal (T ^ (-θ) * ∑ i ∈ F, w i ^ θ *
        Real.exp (LQGDimension.gffCircleCov (ρ i) (z i) (ρ i) (z i) * (θ * ξ) ^ 2 / 2)) := by
  have hmeas : ∀ i, AEMeasurable (fun ω => H (ρ i) (z i) ω) P := fun i =>
    ((LQGDimension.SegLaw.isGaussianProcess_slice hH (hρ i)).hasGaussianLaw_eval (z i)).aemeasurable
  set X : Ω → ℝ := fun ω => ∑ i ∈ F, w i * Real.exp (ξ * H (ρ i) (z i) ω) with hX
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  set Y : Ω → ℝ≥0∞ := fun ω => ∑ i ∈ F, ENNReal.ofReal (w i ^ θ) *
    ENNReal.ofReal (Real.exp ((θ * ξ) * H (ρ i) (z i) ω)) with hY
  have hterm : ∀ i, AEMeasurable (fun ω => ENNReal.ofReal (w i ^ θ) *
      ENNReal.ofReal (Real.exp ((θ * ξ) * H (ρ i) (z i) ω))) P := fun i =>
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.continuous_exp.measurable.comp_aemeasurable ((hmeas i).const_mul _))).const_mul _
  have hYm : AEMeasurable Y P := Finset.aemeasurable_fun_sum _ fun i _ => hterm i
  have hsub : {ω | T < X ω} ⊆ {ω | ENNReal.ofReal (T ^ θ) ≤ Y ω} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω ⊢
    have h1 : T ^ θ ≤ X ω ^ θ := Real.rpow_le_rpow hT.le hω.le hθ0.le
    have h2 : X ω ^ θ ≤ ∑ i ∈ F, (w i * Real.exp (ξ * H (ρ i) (z i) ω)) ^ θ :=
      rpow_finsetSum_le F _ (fun i => mul_nonneg (hw i) (Real.exp_pos _).le) hθ0 hθ1
    have h3 : ∀ i ∈ F, (w i * Real.exp (ξ * H (ρ i) (z i) ω)) ^ θ =
        w i ^ θ * Real.exp ((θ * ξ) * H (ρ i) (z i) ω) := fun i _ => by
      rw [Real.mul_rpow (hw i) (Real.exp_pos _).le, ← Real.exp_mul]; ring_nf
    rw [Finset.sum_congr rfl h3] at h2
    calc ENNReal.ofReal (T ^ θ) ≤ ENNReal.ofReal (∑ i ∈ F, w i ^ θ *
          Real.exp ((θ * ξ) * H (ρ i) (z i) ω)) := ENNReal.ofReal_le_ofReal (h1.trans h2)
      _ = Y ω := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
          mul_nonneg (Real.rpow_nonneg (hw i) _) (Real.exp_pos _).le]
        exact Finset.sum_congr rfl fun i _ =>
          ENNReal.ofReal_mul (Real.rpow_nonneg (hw i) _)
  have hint : ∫⁻ ω, Y ω ∂P = ∑ i ∈ F, ENNReal.ofReal (w i ^ θ) *
      ENNReal.ofReal (Real.exp (LQGDimension.gffCircleCov (ρ i) (z i) (ρ i) (z i) *
        (θ * ξ) ^ 2 / 2)) := by
    rw [hY, lintegral_finsetSum' _ fun i _ => hterm i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      DG.lintegral_exp_circleAvg hH (hρ i) (z i) (θ * ξ)]
  have hM := mul_meas_ge_le_lintegral₀ hYm (ENNReal.ofReal (T ^ θ))
  have hTθ : ENNReal.ofReal (T ^ (-θ)) * ENNReal.ofReal (T ^ θ) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _), ← Real.rpow_add hT, neg_add_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  calc P {ω | T < X ω} ≤ P {ω | ENNReal.ofReal (T ^ θ) ≤ Y ω} := measure_mono hsub
    _ = ENNReal.ofReal (T ^ (-θ)) * (ENNReal.ofReal (T ^ θ) *
          P {ω | ENNReal.ofReal (T ^ θ) ≤ Y ω}) := by rw [← mul_assoc, hTθ, one_mul]
    _ ≤ ENNReal.ofReal (T ^ (-θ)) * ∫⁻ ω, Y ω ∂P := by gcongr
    _ = _ := by
        rw [hint, ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _), ENNReal.ofReal_sum_of_nonneg
          fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (Real.exp_pos _).le]
        congr 1
        exact Finset.sum_congr rfl fun i _ =>
          (ENNReal.ofReal_mul (Real.rpow_nonneg (hw i) _)).symm

end LQGMetric.DFGPS.L36
