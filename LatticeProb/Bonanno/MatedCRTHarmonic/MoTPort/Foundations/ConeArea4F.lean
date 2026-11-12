/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4F at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4E
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
* `lintegral_radG_le`: `E|X_r(0) − X_1(0)| ≤ 1 + |log r|` for `0 < r ≤ 1`, since
  `t ↦ X_{e^{−t}}(0) − X_1(0)` is a Brownian motion (Duplantier–Sheffield arXiv:0808.1560
  Prop. 3.3; LM `CircleAvg.isPreBrownianReal_circleAvg`) and `E B_t² = t` (QZ `integral_sq`);
* `ae_integrableOn_radG`: a.s. `z ↦ X_{|z|}(0) − X_1(0)` is integrable on the unit disc
  (Tonelli and `∫_{B(0,1)} (1 + |log|z||) dz < ∞`, mathlib `integrableOn_fun_norm_addHaar`);
* **`ae_radial_R2`**: radial continuity and integrability statement (R2), in the exact form of the hypothesis `hR2`
  of `ConeArea3.ae_isVagueLimitOn_coneField_punctured_of` (with ConeArea4E for the version).

Own elementary argument (first moment + Tonelli); DMS use the local integrability of the radial
part implicitly when they write `h = h_{|·|}(0) + (h − h_{|·|}(0))` (DMS Section 4.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Field}

/-- first absolute moment of the radial increment -/
theorem lintegral_radG_le [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal |radG X r ω| ∂P ≤ ENNReal.ofReal (1 + |Real.log r|) := by
  obtain ⟨B, hB, -, hBae⟩ := CircleAvg.isPreBrownianReal_circleAvg hX 0
  have hlog : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
  set t : ℝ≥0 := ⟨-Real.log r, by linarith⟩
  have ht : Real.exp (-(t : ℝ)) = r := by
    show Real.exp (-(-Real.log r)) = r
    rw [neg_neg, Real.exp_log hr0]
  have e1 : ∫⁻ ω, ENNReal.ofReal |radG X r ω| ∂P = ∫⁻ ω, ENNReal.ofReal |B t ω| ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hBae t] with ω hω
    rw [hω, ht]
    rfl
  have hint : Integrable (fun ω => 1 + B t ω ^ 2) P :=
    (integrable_const 1).add (by simpa [sq_abs] using integrable_pow hB t 2)
  rw [e1]
  calc ∫⁻ ω, ENNReal.ofReal |B t ω| ∂P ≤ ∫⁻ ω, ENNReal.ofReal (1 + B t ω ^ 2) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by
          nlinarith [abs_nonneg (B t ω), sq_abs (B t ω)])
    _ = ENNReal.ofReal (∫ ω, (1 + B t ω ^ 2) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun ω => by positivity)).symm
    _ = ENNReal.ofReal (1 + |Real.log r|) := by
        rw [integral_add (integrable_const 1) (by simpa [sq_abs] using integrable_pow hB t 2),
          integral_sq hB t]
        simp [abs_of_nonpos hlog]
        rfl

/-- `1 + |log|z||` is integrable on the unit disc -/
lemma integrableOn_one_add_abs_log :
    IntegrableOn (fun z : ℂ => 1 + |Real.log ‖z‖|) (ball 0 1) volume := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => 1 + |Real.log y|)]
  refine Measure.integrableOn_of_bounded (M := 2) (by simp) ?_ ?_
  · exact (((measurable_id.pow_const _).smul (measurable_const.add
      (continuous_abs.measurable.comp Real.measurable_log)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    obtain ⟨h0, h1⟩ := hy
    have hl := Real.abs_log_mul_self_lt y h0 h1.le
    rw [Complex.finrank_real_complex, smul_eq_mul, Real.norm_eq_abs, pow_one,
      abs_of_nonneg (by positivity), mul_add, mul_one]
    rw [abs_mul, abs_of_pos h0] at hl
    nlinarith

/-- **a.s. the radial increment is integrable on the unit disc** -/
theorem ae_integrableOn_radG [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, IntegrableOn (fun z : ℂ => radG X ‖z‖ ω) (ball 0 1) volume := by
  have hg := measurable_radG hX.measurable
  have hF : Measurable fun p : Ω × ℂ => ENNReal.ofReal |radG X ‖p.2‖ p.1| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (hg.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
      ((measurable_norm.comp measurable_snd).prodMk measurable_fst)))
  have hne : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), z ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton 0))
  have hbound : ∫⁻ ω, (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal |radG X ‖z‖ ω|) ∂P ≠ ⊤ := by
    rw [lintegral_lintegral_swap (hF.aemeasurable)]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_)
      integrableOn_one_add_abs_log.lintegral_lt_top)
    filter_upwards [hne, ae_restrict_mem measurableSet_ball] with z hz hzb
    exact lintegral_radG_le hX (norm_pos_iff.2 hz)
      (le_of_lt (by simpa [mem_ball, dist_zero_right] using hzb))
  filter_upwards [ae_lt_top' (hF.lintegral_prod_right'.aemeasurable) hbound] with ω hω
  refine ⟨((hg.comp (f := fun z : ℂ => (‖z‖, ω))
    (measurable_norm.prodMk measurable_const))).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simpa only [Real.enorm_eq_ofReal_abs] using hω

/-- **Radial continuity and integrability statement (R2)** -/
theorem ae_radial_R2 [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ∃ R : ℝ → ℝ, ContinuousOn R (Ioi 0) ∧ Measurable R ∧
      radialFun (X ω) =ᵐ[volume] (fun z => R ‖z‖) ∧
      LocallyIntegrable (fun z : ℂ => R ‖z‖) volume := by
  filter_upwards [ae_radial_version hX, ae_integrableOn_radG hX] with ω ⟨R, hRc, hRm, hRe⟩ hint
  refine ⟨R, hRc, hRm, hRe, (locallyIntegrable_iff).2 fun K hK => ?_⟩
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  refine IntegrableOn.mono_set ?_ (hM.trans (show closedBall (0 : ℂ) M ⊆
    ball 0 1 ∪ {z : ℂ | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ M} from fun z hz => ?_))
  · refine IntegrableOn.union ?_ ?_
    · -- on the unit disc: `R(|z|) = X_{|z|}(0) = radG + X_1(0)` a.e.
      have h1 : IntegrableOn (fun z : ℂ => radG X ‖z‖ ω + circleAvg (X ω) 1 0) (ball 0 1) :=
        hint.add (integrableOn_const (by simp))
      refine h1.congr_fun_ae ?_
      filter_upwards [ae_restrict_of_ae hRe] with z hz
      rw [← hz]
      simp only [radialFun, radG]
      ring
    · have hc : IsCompact {z : ℂ | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ M} :=
        (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset
          ((isClosed_le continuous_const continuous_norm).inter
            (isClosed_le continuous_norm continuous_const))
          fun z hz => by simpa [mem_closedBall, dist_zero_right] using hz.2
      refine ContinuousOn.integrableOn_compact hc ?_
      exact hRc.comp continuous_norm.continuousOn fun z hz =>
        (show (0 : ℝ) < ‖z‖ by linarith [hz.1])
  · by_cases h : ‖z‖ < 1
    · exact Or.inl (by simpa [mem_ball, dist_zero_right] using h)
    · exact Or.inr ⟨by linarith [not_lt.1 h],
        by simpa [mem_closedBall, dist_zero_right] using hz⟩

end ConeArea4
end MatedCRTHarmonic.MoTPort
