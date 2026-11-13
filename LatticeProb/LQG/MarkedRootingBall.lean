import Mathlib
import LatticeProb.LQG.MarkedRootingTilt
import LatticeProb.LQG.MarkedRootingScaling
import LatticeProb.LQG.DilatedMarks
import LatticeProb.LQG.DilatedLIntegral

/-!
# The marked rooting identity on a ball of radius `2^j`

Let `h` be a whole-plane Gaussian free field (vanishing average over the unit circle), `μ` its `γ`-Liouville
measure, `φ_i` mean-zero test functions supported in the disk of radius `2^j`, `U` a measurable subset of that disk
and `f ≥ 0` measurable.  With `X = ((h, φ_i))_i`:
`E [∫_U f (z, X) dμ (z)] = ∫_U max(1, |z|)^{γ²} E [f (z, X + γ s(z))] dz`, `s_i(z) = ∫ φ_i(x) Cov (h(x), h(z)) dx`.

The proof dilates the field by `c = 2^j` (so that `U / c` lies in the unit disk), applies the identity with the
Gaussian tilt by `exp (-γ h_{1/c}(0))` to the dilated field, and changes variables back.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Marked rooting identity on a ball, given the dilation of the field and of its measure by `c ≥ 1`.** -/
theorem lintegral_lqgMeasure_marked_ball_of_dilation (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {c : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (hh' : IsWholePlaneGFF P (LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c)
      (LatticeProb.LQG.DyadicDilation.dilatedCirc hcirc c))
    (hμ' : LatticeProb.LQG.IsLQGMeasure P γ (LatticeProb.LQG.DyadicDilation.dilatedCirc hcirc c)
      (LatticeProb.LQG.DyadicDilation.dilatedMeasure γ hcirc μ c))
    (hmap : ∀ᵐ ω ∂P, (μ ω).map (fun x => x / (c : ℂ)) =
      LatticeProb.LQG.DyadicDilation.dilationFactor γ c (hcirc ω c 0) •
        LatticeProb.LQG.DyadicDilation.dilatedMeasure γ hcirc μ c ω)
    {m : ℕ} {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i)) (hφ0 : ∀ i, ∫ x, φ i x = 0)
    (hφs : ∀ i y, φ i y ≠ 0 → ‖y‖ < c) {U : Set ℂ} (hU : MeasurableSet U)
    (hUc : U ⊆ Metric.ball (0 : ℂ) c) {f : ℂ × (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ z in U, f (z, fun i => hC ω (φ i)) ∂μ ω) P ∧
    ∫⁻ ω, ∫⁻ z in U, f (z, fun i => hC ω (φ i)) ∂μ ω ∂P =
      ∫⁻ z in U, ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) *
        ∫⁻ ω, f (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hρ : 0 < c⁻¹ := inv_pos.2 hc
  have hρ1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  set ψ : Fin m → ℂ → ℝ := fun i => scaledTest c (φ i) with hψdef
  have hψ : ∀ i, IsTestFunction Set.univ (ψ i) := fun i => scaledTest_isTestFunction hc (hφ i)
  have hψs : ∀ i x, ψ i x ≠ 0 → ‖x‖ < 1 := fun i x hx => scaledTest_support hc (hφs i) hx
  set F := LatticeProb.LQG.DyadicDilation.dilatedIntegrand c U f with hFdef
  have hF : Measurable F :=
    LatticeProb.LQG.DyadicDilation.measurable_dilatedIntegrand c hU hf
  have hX : ∀ᵐ ω ∂P, ∀ i, LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c ω (ψ i) =
      hC ω (φ i) :=
    ae_all_iff.2 fun i => LatticeProb.LQG.DyadicDilation.ae_dilatedPairing_scaled hh hc (hφ i) (hφ0 i)
  have hτ := LatticeProb.LQG.DyadicDilation.ae_dilatedCirc_inv hh hc
  -- the pathwise rescaling
  have hpath : ∀ᵐ ω ∂P, ∫⁻ z in U, f (z, fun i => hC ω (φ i)) ∂μ ω =
      ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
        ∫⁻ w in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (Real.exp (-γ * LatticeProb.LQG.DyadicDilation.dilatedCirc hcirc c ω c⁻¹ 0)) *
            F (w, fun i => LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c ω (ψ i))
          ∂(LatticeProb.LQG.DyadicDilation.dilatedMeasure γ hcirc μ c ω) := by
    filter_upwards [hmap, hX, hτ] with ω hω hXω hτω
    rw [LatticeProb.LQG.DyadicDilation.lintegral_restrict_eq_mul_dilatedIntegrand hc hω hU hUc hf,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hXf : (fun i => LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c ω (ψ i)) =
        fun i => hC ω (φ i) := funext hXω
    have hexp : -γ * -hcirc ω c 0 = γ * hcirc ω c 0 := by ring
    rw [hXf, hτω, hexp]
    unfold LatticeProb.LQG.DyadicDilation.dilationFactor
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  -- the identity for the dilated field
  have hfm : Measurable fun q : (ℂ × (Fin m → ℝ)) × ℝ =>
      ENNReal.ofReal (Real.exp (-γ * q.2)) * F q.1 :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_snd.const_mul _))).mul
      (hF.comp measurable_fst)
  have hae1 := (hh'.lintegral_lqgMeasure_marked_circle_fun_eq hγ0 hγ2 hμ' hψ hρ hfm).1
  have h1 := hh'.lintegral_lqgMeasure_marked_tilt hγ0 hγ2 hμ' hψ hψs hρ hρ1 hF
  -- the inner expectation
  set G : ℂ → ℝ≥0∞ := fun z => ∫⁻ ω, f (z, fun i => hC ω (φ i) +
    γ * ∫ x, φ i x * wholePlaneCov x z) ∂P with hGdef
  have hinner : ∀ w : ℂ, ∫⁻ ω, F (w, fun i => LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c ω
        (ψ i) + γ * ((∫ x, ψ i x * wholePlaneCov x w) - ∫ x, ψ i x * -Real.log (max c⁻¹ ‖x‖))) ∂P =
      U.indicator G ((c : ℂ) * w) := by
    intro w
    have hz : c⁻¹ • ((c : ℂ) * w) = w := by
      rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_inv, inv_mul_cancel₀ hc', one_mul]
    have hsh : ∀ i, (∫ x, ψ i x * wholePlaneCov x w) - ∫ x, ψ i x * -Real.log (max c⁻¹ ‖x‖) =
        ∫ x, φ i x * wholePlaneCov x ((c : ℂ) * w) := fun i => by
      have := integral_scaledTest_shift hc (hφ i) (hφ0 i) (hφs i) ((c : ℂ) * w)
      rwa [hz] at this
    have hcongr : ∫⁻ ω, F (w, fun i => LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c ω
        (ψ i) + γ * ((∫ x, ψ i x * wholePlaneCov x w) - ∫ x, ψ i x * -Real.log (max c⁻¹ ‖x‖))) ∂P =
        ∫⁻ ω, F (w, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x ((c : ℂ) * w)) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hX] with ω hXω
      congr 2
      funext i
      rw [hXω i, hsh i]
    rw [hcongr]
    by_cases hw : (c : ℂ) * w ∈ U
    · simp [hFdef, LatticeProb.LQG.DyadicDilation.dilatedIntegrand, hw, hGdef]
    · simp [hFdef, LatticeProb.LQG.DyadicDilation.dilatedIntegrand, hw]
  refine ⟨?_, ?_⟩
  · exact (hae1.const_mul (ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)))).congr
      (hpath.mono fun ω h => h.symm)
  · calc ∫⁻ ω, ∫⁻ z in U, f (z, fun i => hC ω (φ i)) ∂μ ω ∂P
        = ∫⁻ ω, ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
            ∫⁻ w in Metric.ball (0 : ℂ) 1,
              ENNReal.ofReal (Real.exp (-γ *
                LatticeProb.LQG.DyadicDilation.dilatedCirc hcirc c ω c⁻¹ 0)) *
                F (w, fun i => LatticeProb.LQG.DyadicDilation.dilatedPairing hC hcirc c ω (ψ i))
              ∂(LatticeProb.LQG.DyadicDilation.dilatedMeasure γ hcirc μ c ω) ∂P :=
          lintegral_congr_ae hpath
      _ = ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
            ∫⁻ w in Metric.ball (0 : ℂ) 1,
              ENNReal.ofReal (Real.exp (γ ^ 2 * (-Real.log c⁻¹) / 2 +
                γ ^ 2 * Real.log (max c⁻¹ ‖w‖))) * U.indicator G ((c : ℂ) * w) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1]
          congr 1
          exact setLIntegral_congr_fun measurableSet_ball fun w _ => by rw [hinner w]
      _ = ∫⁻ w in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
            (ENNReal.ofReal (Real.exp (γ ^ 2 * (-Real.log c⁻¹) / 2 +
              γ ^ 2 * Real.log (max c⁻¹ ‖w‖))) * U.indicator G ((c : ℂ) * w)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ z in U, ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) * G z :=
          LatticeProb.LQG.DyadicDilation.lintegral_ball_weight_eq hc hU hUc G

/-- **Marked rooting identity on a ball of radius `2^j`.** -/
theorem lintegral_lqgMeasure_marked_ball (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LatticeProb.LQG.IsLQGMeasure P γ hcirc μ)
    (j : ℕ) {m : ℕ} {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    (hφ0 : ∀ i, ∫ x, φ i x = 0) (hφs : ∀ i y, φ i y ≠ 0 → ‖y‖ < (2 : ℝ) ^ j) {U : Set ℂ}
    (hU : MeasurableSet U) (hUc : U ⊆ Metric.ball (0 : ℂ) ((2 : ℝ) ^ j))
    {f : ℂ × (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ z in U, f (z, fun i => hC ω (φ i)) ∂μ ω) P ∧
    ∫⁻ ω, ∫⁻ z in U, f (z, fun i => hC ω (φ i)) ∂μ ω ∂P =
      ∫⁻ z in U, ENNReal.ofReal (max 1 ‖z‖ ^ γ ^ 2) *
        ∫⁻ ω, f (z, fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  obtain ⟨hh', hμ', hmap⟩ := LatticeProb.LQG.DyadicDilation.dilation_two_pow hγ0 hh hμ j
  exact hh.lintegral_lqgMeasure_marked_ball_of_dilation hγ0 hγ2 (by positivity)
    (one_le_pow₀ (by norm_num)) hh' hμ' hmap hφ hφ0 hφs hU hUc hf

end IsWholePlaneGFF

end LatticeProb.Gauss
