/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18T5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P15
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Prop 3.17 on squares: reduction to one reference process (DG:1593–1595)

DG passes from `h^{𝕊(1)}` to the whole-plane field and to every square by the law of the field
(DG:1593–1595, as in DG:1774–1777). `DGProp3_17Sq` quantifies over every process `hc` with
`IsGFFCircleAverage hc P`; its event is `{δ^{λ+ζ} ≤ D^δ(K, ∂U)}` (`p17SetDist`, paths in `Ū`).

* `t18_lfppLength_le_meas` — the LFPP comparison `φ ≤ ψ + a` ⇒ `L_φ ≤ e^{ξa} L_ψ` for a
  measurable `ψ` bounded on `S` (the continuity of `p18_lfppLength_le` is only used for
  integrability);
* `t18_cmp_p17` — `p17SetDist` has the comparison property `T18Cmp` on `Ū`;
* **`dgProp3_17Sq_of_ref : DGProp3_17SqRef → DGProp3_17Sq`** via the law transfer
  `t18_lower_eq` (S3P18T4).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-- **LFPP comparison along a path** for a measurable `ψ` bounded on `S` -/
lemma t18_lfppLength_le_meas {ξ a : ℝ} (hξ : 0 ≤ ξ) {φ ψ : ℂ → ℝ} {S : Set ℂ}
    (hψm : Measurable ψ) {B : ℝ} (hψB : ∀ x ∈ S, |ψ x| ≤ B) (hφψ : ∀ x ∈ S, φ x ≤ ψ x + a)
    {z w : ℂ} {q : ℝ → ℂ} (hq : IsDGPath S z w q) :
    LQGDimension.lfppLength ξ φ q ≤ Real.exp (ξ * a) * LQGDimension.lfppLength ξ ψ q := by
  have hd : IntegrableOn (fun t => ‖deriv q t‖) (Ioc (0 : ℝ) 1) := by
    have h := (DFGPS.L36.dgPath_deriv_intervalIntegrable hq).norm
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  have hqm : AEMeasurable q (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hq.continuousOn.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hmeas : AEStronglyMeasurable (fun t => Real.exp (ξ * a) * (Real.exp (ξ * ψ (q t)) *
      ‖deriv q t‖)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (aemeasurable_const.mul (((hψm.comp_aemeasurable hqm).const_mul ξ).exp.mul
      (measurable_deriv q).norm.aemeasurable)).aestronglyMeasurable
  have hi : IntegrableOn (fun t => Real.exp (ξ * a) * (Real.exp (ξ * ψ (q t)) * ‖deriv q t‖))
      (Ioc (0 : ℝ) 1) := by
    refine Integrable.mono' (hd.const_mul (Real.exp (ξ * a) * Real.exp (ξ * B))) hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have hqt := hq.mapsTo (Ioc_subset_Icc_self ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (Real.exp_pos _).le) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hψB _ hqt)) hξ
  unfold LQGDimension.lfppLength
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hi ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  have hqt := hq.mapsTo (Ioc_subset_Icc_self ht)
  rw [← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  nlinarith [hφψ _ hqt]

/-- `p17SetDist` has the comparison property on `Ū` -/
lemma t18_cmp_p17 {ξ : ℝ} (hξ : 0 ≤ ξ) (K U : Set ℂ) :
    T18Cmp ξ (closure U) (fun φ => p17SetDist ξ φ K U) := by
  intro φ ψ _ hψ ⟨B, hB⟩ η _ hφψ
  have h0 : ENNReal.ofReal (Real.exp (ξ * η)) ≠ 0 := by simp [Real.exp_pos]
  simp only [p17SetDist]
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun z => iInf_mono fun _ => iInf_mono fun w => iInf_mono fun _ =>
    iInf_mono fun q => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (t18_lfppLength_le_meas hξ hψ hB hφψ q.2)

lemma t18Sq_isClosed (c : ℂ) (r : ℝ) : IsClosed (t18Sq c r) :=
  (isClosed_le (continuous_abs.comp (Complex.continuous_re.comp (continuous_sub_right c)))
    continuous_const).inter
  (isClosed_le (continuous_abs.comp (Complex.continuous_im.comp (continuous_sub_right c)))
    continuous_const)

lemma t18_closure_sub_ball {U : Set ℂ} {c : ℂ} {r : ℝ} (hUS : U ⊆ t18Sq c r) :
    closure U ⊆ closedBall 0 (‖c‖ + 2 * r) := fun x hx => by
  have h := t18Sq_subset_ball c r (closure_minimal hUS (t18Sq_isClosed c r) hx)
  rw [mem_closedBall, dist_eq_norm] at h
  rw [mem_closedBall, dist_zero_right]
  have := norm_le_norm_add_norm_sub' x c
  linarith

/-- `DGProp3_17Sq` for one process with `IsGFFCircleAverage` (per `γ, S, K, U, ζ`) -/
def DGProp3_17SqRef : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (c : ℂ) (r : ℝ), 0 < r →
    ∀ K U : Set ℂ, IsCompact K → IsOpen U → K ⊆ U → U ⊆ t18Sq c r → ∀ ζ ∈ Ioo (0 : ℝ) 1,
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ),
        LQGDimension.IsGFFCircleAverage hc P ∧ ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧
          ∀ δ ∈ Ioo (0 : ℝ) δ₀,
            P {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
              p17SetDist (xiGamma γ) (fun x => hc δ x ω) K U} ≤ ENNReal.ofReal (C * δ ^ p)

/-- **`DGProp3_17Sq` from one reference process** (the law step of DG:1593–1595) -/
theorem dgProp3_17Sq_of_ref (h : DGProp3_17SqRef) : DGProp3_17Sq := by
  intro γ hγ hγ2 Ω _ P hc hG c r hr K U hK hU hKU hUS ζ hζ
  obtain ⟨Ω₀, _, P₀, H, hH, p, C, δ₀, hp, hδ₀, hb⟩ := h γ hγ hγ2 c r hr K U hK hU hKU hUS ζ hζ
  refine ⟨p, C, δ₀, hp, hδ₀, fun δ hδ => ?_⟩
  rw [t18_lower_eq hG hH hδ.1 (t18_closure_sub_ball hUS)
    (t18_cmp_p17 (xiGamma_pos hγ).le K U)]
  exact hb δ hδ

end LQGMetric.DG
