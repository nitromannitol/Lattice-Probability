import Mathlib
import LatticeProb.Gauss.CircleAverageApprox
import LatticeProb.Gauss.CameronMartinDerived2

/-! # Circle-average approximants and their almost sure convergence

LP copy of the approximant chain of the whole-plane GFF: the covariance kernel of an annular density against the
logarithmic kernel `wholePlaneCov` (`FirstPass/S11u/Mixed.lean`, Duplantier-Sheffield 2011, Section 3.1), the variance
of a pairing minus a circle average (`FirstPass/S11u/Variance.lean`), the annular approximants (`FirstPass/S11u.lean`,
`FirstPass/S11at/Producers.lean`), ending with `ae_tendsto_circleApprox`: almost surely the pairings with the explicit
annular approximants converge to the circle average. Mechanical transcription in the definitions of `LatticeProb.Gauss`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

/-- The whole-plane GFF lives on a probability space (LP form of `HarmonicBalls.isProbabilityMeasure`). -/
theorem IsWholePlaneGFF.isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) : IsProbabilityMeasure P :=
  have : Nonempty GFFObservable.Admissible := ⟨⟨.circle 1 0, one_pos⟩⟩
  hh.isGaussianProcess.isProbabilityMeasure

/-- Each circle average of positive radius is Gaussian (LP form of `HarmonicBalls.hasGaussianLaw_circle`). -/
theorem IsWholePlaneGFF.hasGaussianLaw_circle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    HasGaussianLaw (fun ω => hcirc ω r z) P :=
  hh.isGaussianProcess.hasGaussianLaw_eval (⟨.circle r z, hr⟩ : GFFObservable.Admissible)

end LatticeProb.Gauss

-- ===== Proofs/Sec8/CircleDensityPolarIntegrability

/-! # Polar integrability for annular densities

The change-of-variables theorem gives the integrability needed to apply
Fubini even when an observable has a logarithmic singularity. The imported
Section 8 argument uses Leonardo Bonanno's LatticeProb formalization of the
ergodic theorem.
-/

open MeasureTheory Set Metric Filter Real
open scoped Topology

namespace LatticeProb.Gauss

/-- An integrable function on the plane, composed with polar coordinates and
multiplied by the polar Jacobian, is integrable on the polar target. -/
theorem integrableOn_polarCoord_symm_of_integrable {f : ℂ → ℝ} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hpair : Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf
  have hj := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.symm.open_source.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn (f ∘ Complex.measurableEquivRealProd.symm)
  have hi := hj.mp hpair.integrableOn
  simp only [det_fderivPolarCoordSymm] at hi
  refine hi.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  simp only [smul_eq_mul, Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply,
    abs_of_pos (show 0 < p.1 from hp.1)]

/-- The radial-mixture identity remains valid for any observable integrable
against the annular density, including singular observables. -/
theorem integral_circleDensity_eq_circleAverage_of_integrable {r δ : ℝ}
    (hδ : 0 < δ) (z : ℂ) {f : ℂ → ℝ}
    (hf : Integrable (fun x => circleDensity r δ hδ z x * f x)) :
    (∫ x, circleDensity r δ hδ z x * f x) =
      2 * Real.pi * ∫ ρ in Ioi (0 : ℝ),
        ρ * circleRadiusBump r δ hδ (ρ ^ 2) * Real.circleAverage f z ρ := by
  let g : ℝ × ℝ → ℝ := fun p =>
    p.1 * circleRadiusBump r δ hδ (p.1 ^ 2) * f (circleMap z p.1 p.2)
  have hshift : Integrable (fun u : ℂ => circleDensity r δ hδ z (u + z) * f (u + z)) := by
    exact (measurePreserving_add_right volume z).integrable_comp_of_integrable hf
  have hpolar : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (circleDensity r δ hδ z
        (Complex.polarCoord.symm p + z) * f (Complex.polarCoord.symm p + z)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    integrableOn_polarCoord_symm_of_integrable hshift
  have heq : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 * (circleDensity r δ hδ z (Complex.polarCoord.symm p + z) *
        f (Complex.polarCoord.symm p + z)) = g p := by
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    change 0 < ρ at hρ
    have hcircle : Complex.polarCoord.symm (ρ, θ) + z = circleMap z ρ θ := by
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, add_comm]
    simp only [g, hcircle, circleDensity, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos hρ]
    ring
  have hint : IntegrableOn g (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    hpolar.congr_fun heq (measurableSet_Ioi.prod measurableSet_Ioo)
  have htrans : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ u : ℂ, circleDensity r δ hδ z (u + z) * f (u + z) := by
    simpa using (integral_sub_right_eq_self
      (fun u : ℂ => circleDensity r δ hδ z (u + z) * f (u + z)) z)
  have hpoleq : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, g p := by
    rw [htrans, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    simpa only [smul_eq_mul] using heq p hp
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
  rw [hpoleq, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  change (∫ θ in Ioo (-Real.pi) Real.pi,
    ρ * circleRadiusBump r δ hδ (ρ ^ 2) * f (circleMap z ρ θ)) = _
  rw [integral_const_mul, integral_circleMap_eq_circleAverage]
  ring

/-- The normalized version of the mixture formula under the same integrability
hypothesis. -/
theorem integral_normalized_circleDensity_eq_circleAverage_of_integrable {r δ : ℝ}
    (hδ : 0 < δ) (z : ℂ) {f : ℂ → ℝ}
    (hf : Integrable (fun x => circleDensity r δ hδ z x * f x)) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x * f x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        Real.circleAverage f z ρ := by
  have heq : (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleDensity r δ hδ z x * f x) =
      (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
        ∫ x, circleDensity r δ hδ z x * f x := by
    simp_rw [mul_assoc, integral_const_mul]
  rw [heq, integral_circleDensity_eq_circleAverage_of_integrable hδ z hf,
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  simp only [circleDensityRadialWeight]
  ring

/-- The logarithmic kernel is integrable against a compactly supported
annular density, including when its singularity lies in the annulus. -/
theorem integrable_circleDensity_mul_log_norm_sub {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z w : ℂ) :
    Integrable (fun x => circleDensity r δ hδ z x * Real.log ‖x - w‖) := by
  have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm w
    ).integrable_smul_right_of_hasCompactSupport (circleDensity_contDiff r δ hδ z).continuous
      (circleDensity_hasCompactSupport hr hδ z)
  simpa only [smul_eq_mul, mul_comm] using h

/-- The logarithmic potential of a normalized annular density is the radial
mixture of the explicit circle potentials. -/
theorem integral_normalized_circleDensity_mul_log_norm_sub {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z w : ℂ) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
      Real.log ‖x - w‖) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        Real.log (max ρ ‖z - w‖) := by
  rw [integral_normalized_circleDensity_eq_circleAverage_of_integrable hδ z
    (integrable_circleDensity_mul_log_norm_sub hr hδ z w)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  change circleDensityRadialWeight r δ hδ ρ *
      Real.circleAverage (fun x => Real.log ‖x - w‖) z ρ =
    circleDensityRadialWeight r δ hδ ρ * Real.log (max ρ ‖z - w‖)
  rw [circleAverage_log_norm_sub_eq_log_max (show 0 < ρ from hρ)]

/-- A narrow annular density has logarithmic potential between the potentials
of the two bounding circles, uniformly in the evaluation point. -/
theorem circleDensity_log_potential_bounds {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hηr : η < r) (hwidth : δ ≤ r * η)
    (z w : ℂ) :
    Real.log (max (r - η) ‖z - w‖) ≤
      (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
        Real.log ‖x - w‖) ∧
      (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
        Real.log ‖x - w‖) ≤ Real.log (max (r + η) ‖z - w‖) := by
  let W := circleDensityRadialWeight r δ hδ
  let L : ℝ → ℝ := fun ρ => Real.log (max ρ ‖z - w‖)
  have hW : Continuous W := by
    dsimp [W, circleDensityRadialWeight]
    exact continuous_const.mul (continuous_id.mul
      ((circleRadiusBump r δ hδ).continuous.comp (continuous_id.pow 2)))
  have hL : ContinuousOn L (Icc (r - η) (r + η)) := by
    dsimp [L]
    apply (continuous_id.max continuous_const).continuousOn.log
    intro ρ hρ
    exact ne_of_gt (lt_of_lt_of_le (by linarith) (hρ.1.trans (le_max_left _ _)))
  have hi : IntegrableOn (fun ρ => W ρ * L ρ) (Ioi (0 : ℝ)) := by
    have hc : IntegrableOn (fun ρ => W ρ * L ρ) (Icc (r - η) (r + η)) :=
      (hW.continuousOn.mul hL).integrableOn_compact isCompact_Icc
    refine hc.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro ρ hρ
    by_cases hw : W ρ = 0
    · simp [hw]
    · have hnear := circleDensityRadialWeight_support_radius hr hδ hwidth
        (show 0 ≤ ρ from le_of_lt hρ.1) hw
      rw [abs_lt] at hnear
      exact (hρ.2 ⟨by linarith [hnear.1], by linarith [hnear.2]⟩).elim
  have hwi : IntegrableOn W (Ioi (0 : ℝ)) := circleDensityRadialWeight_integrableOn hr.le hδ
  have hwm : (∫ ρ in Ioi (0 : ℝ), W ρ) = 1 := circleDensityRadialWeight_integral hr.le hδ
  rw [integral_normalized_circleDensity_mul_log_norm_sub hr.le hδ z w]
  constructor
  · calc
      _ = ∫ ρ in Ioi (0 : ℝ), W ρ * Real.log (max (r - η) ‖z - w‖) := by
        rw [integral_mul_const, hwm, one_mul]
      _ ≤ ∫ ρ in Ioi (0 : ℝ), W ρ * L ρ := by
        apply integral_mono_ae (hwi.mul_const _) hi
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have hn := circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw
          rw [abs_lt] at hn
          apply Real.log_le_log
          · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
          · exact max_le_max_right _ (by linarith [hn.1])
  · calc
      (∫ ρ in Ioi (0 : ℝ), W ρ * L ρ) ≤
          ∫ ρ in Ioi (0 : ℝ), W ρ * Real.log (max (r + η) ‖z - w‖) := by
        apply integral_mono_ae hi (hwi.mul_const _)
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have hn := circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw
          rw [abs_lt] at hn
          apply Real.log_le_log
          · exact lt_of_lt_of_le hρ (le_max_left _ _)
          · exact max_le_max_right _ (by linarith [hn.2])
      _ = _ := by rw [integral_mul_const, hwm, one_mul]

/-- The change in a circle's logarithmic potential between two radii is
bounded by their logarithmic separation, uniformly in the other point. -/
theorem log_max_sub_log_max_le {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (max b d) - Real.log (max a d) ≤ Real.log b - Real.log a := by
  by_cases hda : d ≤ a
  · rw [max_eq_left hda, max_eq_left (hda.trans hab)]
  · have had : a ≤ d := le_of_not_ge hda
    by_cases hdb : d ≤ b
    · rw [max_eq_right had, max_eq_left hdb]
      have h := Real.log_le_log ha had
      linarith
    · have hbd : b ≤ d := le_of_not_ge hdb
      rw [max_eq_right had, max_eq_right hbd]
      have h := Real.log_le_log ha hab
      linarith

/-- The normalized annular logarithmic potential differs from the target
circle potential by at most the logarithmic separation of the bounding
circles, uniformly in the point at which it is evaluated. -/
theorem abs_circleDensity_log_potential_sub_circle_le {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hηr : η < r) (hwidth : δ ≤ r * η) (z w : ℂ) :
    |(∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
      Real.log ‖x - w‖) - Real.log (max r ‖z - w‖)| ≤
      Real.log (r + η) - Real.log (r - η) := by
  have hη : 0 < η := by nlinarith
  have hb := circleDensity_log_potential_bounds hr hδ hηr hwidth z w
  have hlower : Real.log (max (r - η) ‖z - w‖) ≤ Real.log (max r ‖z - w‖) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · exact max_le_max_right _ (by linarith)
  have hupper : Real.log (max r ‖z - w‖) ≤ Real.log (max (r + η) ‖z - w‖) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le hr (le_max_left _ _)
    · exact max_le_max_right _ (by linarith)
  have hspan := log_max_sub_log_max_le (a := r - η) (b := r + η)
    (d := ‖z - w‖) (by linarith) (by linarith)
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- Shrinking annular densities have logarithmic potentials converging
uniformly, over both the center and evaluation point, to the circle potential. -/
theorem circleDensity_log_potential_tendsto_uniformly {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ z w : ℂ,
      |(∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
          (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
          circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x *
          Real.log ‖x - w‖) - Real.log (max r ‖z - w‖)| < ε := by
  have hηlim : Tendsto (fun n : ℕ => η / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hp : Tendsto (fun n : ℕ => r + η / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).add hηlim
  have hm : Tendsto (fun n : ℕ => r - η / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).sub hηlim
  have hspan : Tendsto (fun n : ℕ => Real.log (r + η / ((n : ℝ) + 1)) -
      Real.log (r - η / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log hr.ne').tendsto.comp hp).sub
      ((Real.continuousAt_log hr.ne').tendsto.comp hm)
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, η / ((n : ℝ) + 1) < r :=
    (tendsto_order.1 hηlim).2 r hr
  have herror : ∀ᶠ n : ℕ in atTop,
      Real.log (r + η / ((n : ℝ) + 1)) -
        Real.log (r - η / ((n : ℝ) + 1)) < ε := (tendsto_order.1 hspan).2 ε hε
  have hgoal : ∀ᶠ n : ℕ in atTop, ∀ z w : ℂ,
      |(∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
          (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
          circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x *
          Real.log ‖x - w‖) - Real.log (max r ‖z - w‖)| < ε := by
    filter_upwards [hsmall, herror] with n hsmalln herrorn
    intro z w
    have hwidth : circleDensityWidth r η n ≤ r * (η / ((n : ℝ) + 1)) := by
      simp [circleDensityWidth, div_eq_mul_inv, mul_assoc]
    exact (abs_circleDensity_log_potential_sub_circle_le hr
      (circleDensityWidth_pos hr hη n) hsmalln hwidth z w).trans_lt herrorn
  exact eventually_atTop.1 hgoal

end LatticeProb.Gauss

-- ===== FirstPass/S11u/Kernel (part)

/-!
# Kernel identities for the whole-plane covariance on circles

The whole-plane kernel `wholePlaneCov x y = log (max |x| 1 * max |y| 1 / |x - y|)` (Defs/GFF.lean) splits as
`a x + a y - log |x - y|` off the diagonal, with `a x = log max(|x|, 1)`. Averaging over a circle `∂B_ρ(z)` in the
variable `y` gives the Jensen formula (Duplantier-Sheffield, Section 3.1; Armitage-Gardiner for the logarithmic
potential). The diagonal `x = y` is handled by the codiscrete congruence of circle averages.
-/

namespace LatticeProb.Gauss

open MeasureTheory Filter Set Metric Topology

/-- `a x = log max(|x|, 1)`: the additive part of the whole-plane covariance kernel. -/
noncomputable def logMaxAbs (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)

theorem logMaxAbs_continuous : Continuous logMaxAbs := by
  unfold logMaxAbs
  exact (continuous_norm.max continuous_const).log
    (fun x => ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _)))

/-- Off the diagonal the whole-plane kernel is `a x + a y - log |x - y|`. -/
theorem wholePlaneCov_eq_of_ne_circleAverageApprox2 {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖ := by
  have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hy : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  unfold wholePlaneCov logMaxAbs
  rw [Real.log_div (mul_ne_zero hx hy) hd, Real.log_mul hx hy]

/-- Jensen's formula: the average of `log |y - w|` over `∂B_ρ(z)` is `log max(ρ, |z - w|)`. -/
theorem circleAverage_log_norm_sub_eq (z w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun y => Real.log ‖y - w‖) z ρ = Real.log (max ρ ‖z - w‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hρ.ne',
    Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hρ.ne'
      (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))),
    mul_max_of_nonneg _ _ hρ.le, mul_one, mul_inv_cancel_left₀ hρ.ne']

/-- The circle average of the whole-plane kernel in `y` over `∂B_ρ(z)`, for every `x`. -/
theorem circleAverage_wholePlaneCov {z x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun y => wholePlaneCov x y) z ρ =
      logMaxAbs x + Real.circleAverage logMaxAbs z ρ - Real.log (max ρ ‖x - z‖) := by
  have hcongr : (fun y => wholePlaneCov x y) =ᶠ[codiscreteWithin (sphere z |ρ|)]
      (fun y => logMaxAbs x + logMaxAbs y - Real.log ‖y - x‖) := by
    refine Filter.eventually_of_mem (compl_singleton_mem_codiscreteWithin x) ?_
    intro y hy
    have hyx : x ≠ y := fun h => hy (h.symm ▸ rfl)
    show wholePlaneCov x y = _
    rw [wholePlaneCov_eq_of_ne_circleAverageApprox2 hyx, norm_sub_rev]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hρ.ne']
  have hc1 : CircleIntegrable (fun y => logMaxAbs x + logMaxAbs y) z ρ :=
    ContinuousOn.circleIntegrable' (continuous_const.add logMaxAbs_continuous).continuousOn
  have hc2 : CircleIntegrable (fun y => Real.log ‖y - x‖) z ρ :=
    circleIntegrable_log_norm_sub_const ρ
  rw [show (fun y => logMaxAbs x + logMaxAbs y - Real.log ‖y - x‖) =
      (fun y => logMaxAbs x + logMaxAbs y) - (fun y => Real.log ‖y - x‖) from rfl,
    Real.circleAverage_sub hc1 hc2, show (fun y => logMaxAbs x + logMaxAbs y) =
      (fun _ => logMaxAbs x) + logMaxAbs from rfl,
    Real.circleAverage_add (circleIntegrable_const _ _ _)
      (ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn),
    Real.circleAverage_const, circleAverage_log_norm_sub_eq z x hρ, norm_sub_rev]

end LatticeProb.Gauss

-- ===== FirstPass/S11u/Mixed

/-!
# Mixed covariances of a unit annular density and a circle average

For the normalized Section 8 bump `unitCircleDensity r δ z` (unit mass, supported in an annulus around `∂B_r(z)`),
the three whole-plane covariances of `hC(μ)` and `hcirc(r, z)` are expressed through the logarithmic potentials
`U x = ∫ μ(y) log|y - x| dy` and `J x = log max(r, |x - z|)` (Jensen). Their combination is bounded by the uniform
potential error `log(r + η) - log(r - η)` (Section 8, `abs_circleDensity_log_potential_sub_circle_le`).
-/

namespace LatticeProb.Gauss

open MeasureTheory Filter Set Metric Topology

/-- The unit-mass annular density `μ(x) = (∫ circleDensity 0)⁻¹ circleDensity z x` around `∂B_r(z)`. -/
noncomputable def unitCircleDensity (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) : ℝ :=
  (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x

/-- The logarithmic potential `U x = ∫ μ(y) log|y - x| dy` of the unit annular density. -/
noncomputable def logPotential (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) : ℝ :=
  ∫ y, unitCircleDensity r δ hδ z y * Real.log ‖y - x‖

/-- `J x = log max(r, |x - z|)`: the logarithmic potential of the uniform measure on `∂B_r(z)`. -/
noncomputable def circlePotential (r : ℝ) (z x : ℂ) : ℝ := Real.log (max r ‖x - z‖)

theorem unitCircleDensity_nonneg {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z x : ℂ) :
    0 ≤ unitCircleDensity r δ hδ z x :=
  mul_nonneg (inv_nonneg.mpr (circleDensity_integral_pos hr hδ 0).le) (circleDensity_nonneg r δ hδ z x)

theorem integral_unitCircleDensity {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) :
    ∫ x, unitCircleDensity r δ hδ z x = 1 :=
  circleDensity_normalized_integral hr hδ z

theorem unitCircleDensity_continuous (r δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    Continuous (unitCircleDensity r δ hδ z) :=
  continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous

theorem unitCircleDensity_hasCompactSupport {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) :
    HasCompactSupport (unitCircleDensity r δ hδ z) :=
  (circleDensity_hasCompactSupport hr hδ z).mul_left

theorem integrable_unitCircleDensity_mul {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) {g : ℂ → ℝ}
    (hg : Continuous g) : Integrable (fun x => unitCircleDensity r δ hδ z x * g x) :=
  (((unitCircleDensity_continuous r δ hδ z).mul hg)).integrable_of_hasCompactSupport
    ((unitCircleDensity_hasCompactSupport hr hδ z).mul_right)

theorem integrable_unitCircleDensity_mul_log {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z w : ℂ) :
    Integrable (fun y => unitCircleDensity r δ hδ z y * Real.log ‖y - w‖) := by
  unfold unitCircleDensity
  simpa only [mul_assoc] using (integrable_circleDensity_mul_log_norm_sub hr hδ z w).const_mul
    (∫ y, circleDensity r δ hδ 0 y)⁻¹

theorem stronglyMeasurable_logPotential {r δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    StronglyMeasurable (logPotential r δ hδ z) := by
  unfold logPotential
  refine StronglyMeasurable.integral_prod_right'
    (f := fun p : ℂ × ℂ => unitCircleDensity r δ hδ z p.2 * Real.log ‖p.2 - p.1‖) ?_
  apply Measurable.stronglyMeasurable
  exact (((unitCircleDensity_continuous r δ hδ z).measurable.comp measurable_snd)).mul
    (Real.measurable_log.comp (measurable_norm.comp (measurable_snd.sub measurable_fst)))

theorem circlePotential_continuous {r : ℝ} (hr : 0 < r) (z : ℂ) : Continuous (circlePotential r z) :=
  (continuous_const.max (continuous_norm.comp (continuous_id.sub continuous_const))).log
    (fun _ => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))

/-- The uniform bound on the potential error (Section 8, `abs_circleDensity_log_potential_sub_circle_le`). -/
theorem abs_logPotential_sub_circlePotential_le {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hηr : η < r)
    (hwidth : δ ≤ r * η) (z x : ℂ) :
    |logPotential r δ hδ z x - circlePotential r z x| ≤ Real.log (r + η) - Real.log (r - η) := by
  have h := abs_circleDensity_log_potential_sub_circle_le hr hδ hηr hwidth z x
  rw [norm_sub_rev z x] at h
  exact h

theorem integrable_unitCircleDensity_mul_logPotential {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hηr : η < r)
    (hwidth : δ ≤ r * η) (z : ℂ) :
    Integrable (fun x => unitCircleDensity r δ hδ z x * logPotential r δ hδ z x) := by
  set e := Real.log (r + η) - Real.log (r - η) with he
  have hg : Integrable (fun x => unitCircleDensity r δ hδ z x * (|circlePotential r z x| + e)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (unitCircleDensity_continuous r δ hδ z).mul
        ((circlePotential_continuous hr z).abs.add continuous_const)
    · exact (unitCircleDensity_hasCompactSupport hr.le hδ z).mul_right
  refine hg.mono' ?_ ?_
  · exact ((unitCircleDensity_continuous r δ hδ z).stronglyMeasurable.mul
      (stronglyMeasurable_logPotential hδ z)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hμ := unitCircleDensity_nonneg hr.le hδ z x
    have hU := abs_logPotential_sub_circlePotential_le hr hδ hηr hwidth z x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hμ]
    apply mul_le_mul_of_nonneg_left _ hμ
    have h1 := abs_sub_abs_le_abs_sub (logPotential r δ hδ z x) (circlePotential r z x)
    have h2 : |logPotential r δ hδ z x| ≤ |circlePotential r z x| + e := by
      have := abs_sub_abs_le_abs_sub (logPotential r δ hδ z x) (circlePotential r z x)
      linarith [abs_sub_comm (logPotential r δ hδ z x) (circlePotential r z x)]
    exact h2

theorem integrable_unitCircleDensity {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) :
    Integrable (unitCircleDensity r δ hδ z) :=
  (unitCircleDensity_continuous r δ hδ z).integrable_of_hasCompactSupport
    (unitCircleDensity_hasCompactSupport hr hδ z)

/-- Scaling: an integrable `μ g` makes `circleDensity z g` integrable (`μ = M⁻¹ circleDensity`). -/
theorem integrable_circleDensity_mul_of_unit {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) {g : ℂ → ℝ}
    (hg : Integrable (fun x => unitCircleDensity r δ hδ z x * g x)) :
    Integrable (fun x => circleDensity r δ hδ z x * g x) := by
  have hM : (∫ y, circleDensity r δ hδ 0 y) ≠ 0 := (circleDensity_integral_pos hr hδ 0).ne'
  refine (hg.const_mul (∫ y, circleDensity r δ hδ 0 y)).congr (Filter.Eventually.of_forall fun x => ?_)
  unfold unitCircleDensity
  field_simp

/-- The inner integral of the whole-plane kernel against the unit density, at a point `x`. -/
theorem integral_unitCircleDensity_mul_wholePlaneCov {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z x : ℂ) :
    ∫ y, unitCircleDensity r δ hδ z y * wholePlaneCov x y =
      logMaxAbs x + (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) - logPotential r δ hδ z x := by
  have hae : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  have hcongr : (fun y => unitCircleDensity r δ hδ z y * wholePlaneCov x y) =ᵐ[volume]
      (fun y => logMaxAbs x * unitCircleDensity r δ hδ z y +
        unitCircleDensity r δ hδ z y * logMaxAbs y - unitCircleDensity r δ hδ z y * Real.log ‖y - x‖) := by
    filter_upwards [hae] with y hy
    rw [wholePlaneCov_eq_of_ne_circleAverageApprox2 hy.symm, norm_sub_rev]
    ring
  have I1 : Integrable (fun y => logMaxAbs x * unitCircleDensity r δ hδ z y) :=
    (integrable_unitCircleDensity hr hδ z).const_mul _
  have I2 : Integrable (fun y => unitCircleDensity r δ hδ z y * logMaxAbs y) :=
    integrable_unitCircleDensity_mul hr hδ z logMaxAbs_continuous
  have I3 : Integrable (fun y => unitCircleDensity r δ hδ z y * Real.log ‖y - x‖) :=
    integrable_unitCircleDensity_mul_log hr hδ z x
  have I12 : Integrable (fun y => logMaxAbs x * unitCircleDensity r δ hδ z y + unitCircleDensity r δ hδ z y * logMaxAbs y) := I1.add I2
  rw [integral_congr_ae hcongr, integral_sub I12 I3, integral_add I1 I2,
    integral_const_mul, integral_unitCircleDensity hr hδ z, logPotential]
  ring

/-- `Kpp = ∫ μ(x) ∫ μ(y) K(x,y) dy dx = 2 ∫ μ a - ∫ μ U`. -/
theorem integral_unitCircleDensity_mul_inner {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hηr : η < r)
    (hwidth : δ ≤ r * η) (z : ℂ) :
    ∫ x, unitCircleDensity r δ hδ z x * ∫ y, unitCircleDensity r δ hδ z y * wholePlaneCov x y =
      2 * (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) -
        ∫ x, unitCircleDensity r δ hδ z x * logPotential r δ hδ z x := by
  simp only [integral_unitCircleDensity_mul_wholePlaneCov (r := r) (δ := δ) hr.le hδ z]
  have hA : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x) :=
    integrable_unitCircleDensity_mul hr.le hδ z logMaxAbs_continuous
  have hC : Integrable (fun x => (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) *
      unitCircleDensity r δ hδ z x) :=
    (integrable_unitCircleDensity hr.le hδ z).const_mul _
  have hsum : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x +
      (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) * unitCircleDensity r δ hδ z x) := hA.add hC
  have hI : Integrable (fun x => unitCircleDensity r δ hδ z x * logPotential r δ hδ z x) :=
    integrable_unitCircleDensity_mul_logPotential hr hδ hηr hwidth z
  have hpt : ∀ x, unitCircleDensity r δ hδ z x * (logMaxAbs x +
      (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) - logPotential r δ hδ z x) =
      (unitCircleDensity r δ hδ z x * logMaxAbs x +
        (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) * unitCircleDensity r δ hδ z x) -
        unitCircleDensity r δ hδ z x * logPotential r δ hδ z x := fun x => by ring
  simp only [hpt]
  rw [integral_sub hsum hI, integral_add hA hC, integral_const_mul,
    integral_unitCircleDensity hr.le hδ z]
  ring

/-- `Kpc = ∫ μ(x) circleAverage_y K(x,y) dx = ∫ μ a + A - ∫ μ J`, with `A = circleAverage a`. -/
theorem integral_unitCircleDensity_mul_circleAverage {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) :
    ∫ x, unitCircleDensity r δ hδ z x * Real.circleAverage (fun y => wholePlaneCov x y) z r =
      (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) + Real.circleAverage logMaxAbs z r -
        ∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x := by
  simp only [circleAverage_wholePlaneCov hr]
  have hA : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x) :=
    integrable_unitCircleDensity_mul hr.le hδ z logMaxAbs_continuous
  have hC : Integrable (fun x => (Real.circleAverage logMaxAbs z r) *
      unitCircleDensity r δ hδ z x) :=
    (integrable_unitCircleDensity hr.le hδ z).const_mul _
  have hsum : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x +
      (Real.circleAverage logMaxAbs z r) * unitCircleDensity r δ hδ z x) := hA.add hC
  have hJ : Integrable (fun x => unitCircleDensity r δ hδ z x * circlePotential r z x) :=
    integrable_unitCircleDensity_mul hr.le hδ z (circlePotential_continuous hr z)
  have hpt : ∀ x, unitCircleDensity r δ hδ z x * (logMaxAbs x + Real.circleAverage logMaxAbs z r -
      Real.log (max r ‖x - z‖)) = (unitCircleDensity r δ hδ z x * logMaxAbs x +
        (Real.circleAverage logMaxAbs z r) * unitCircleDensity r δ hδ z x) -
        unitCircleDensity r δ hδ z x * circlePotential r z x := fun x => by
    unfold circlePotential
    ring
  simp only [hpt]
  rw [integral_sub hsum hJ, integral_add hA hC, integral_const_mul,
    integral_unitCircleDensity hr.le hδ z]
  ring

/-- `Kzz = circleAverage_x circleAverage_y K(x,y) = 2 A - log r`. -/
theorem circleAverage_circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r =
      2 * Real.circleAverage logMaxAbs z r - Real.log r := by
  have hfun : (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) =
      (fun x => logMaxAbs x + Real.circleAverage logMaxAbs z r - circlePotential r z x) := by
    funext x
    rw [circleAverage_wholePlaneCov hr]
    rfl
  rw [hfun]
  have h1 : CircleIntegrable logMaxAbs z r :=
    ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn
  have h2 : CircleIntegrable (circlePotential r z) z r :=
    ContinuousOn.circleIntegrable' (circlePotential_continuous hr z).continuousOn
  have h3 : CircleIntegrable (logMaxAbs + fun _ => Real.circleAverage logMaxAbs z r) z r :=
    h1.add (circleIntegrable_const _ _ _)
  rw [show (fun x => logMaxAbs x + Real.circleAverage logMaxAbs z r - circlePotential r z x) =
      (logMaxAbs + fun _ => Real.circleAverage logMaxAbs z r) - circlePotential r z from rfl,
    Real.circleAverage_sub h3 h2, Real.circleAverage_add h1 (circleIntegrable_const _ _ _),
    Real.circleAverage_const]
  have hJ : Real.circleAverage (circlePotential r z) z r = Real.log r := by
    apply Real.circleAverage_const_on_circle
    intro x hx
    rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr] at hx
    unfold circlePotential
    rw [hx, max_self]
  rw [hJ]
  ring

/-- `|∫ μ (J - U)| ≤ e`: the uniform potential error integrated against the unit mass. -/
theorem abs_integral_unitCircleDensity_sub_potential_le {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hηr : η < r) (hwidth : δ ≤ r * η) (z : ℂ) :
    |(∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) -
        ∫ x, unitCircleDensity r δ hδ z x * logPotential r δ hδ z x| ≤
      Real.log (r + η) - Real.log (r - η) := by
  rw [← integral_sub (integrable_unitCircleDensity_mul hr.le hδ z (circlePotential_continuous hr z))
    (integrable_unitCircleDensity_mul_logPotential hr hδ hηr hwidth z)]
  have hpt : ∀ x, ‖unitCircleDensity r δ hδ z x * circlePotential r z x -
      unitCircleDensity r δ hδ z x * logPotential r δ hδ z x‖ ≤
      (Real.log (r + η) - Real.log (r - η)) * unitCircleDensity r δ hδ z x := by
    intro x
    have hμ := unitCircleDensity_nonneg hr.le hδ z x
    have hU := abs_logPotential_sub_circlePotential_le hr hδ hηr hwidth z x
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg hμ, abs_sub_comm]
    have := mul_le_mul_of_nonneg_left hU hμ
    linarith [mul_comm (unitCircleDensity r δ hδ z x) (Real.log (r + η) - Real.log (r - η))]
  have hint := norm_integral_le_of_norm_le
    ((integrable_unitCircleDensity hr.le hδ z).const_mul (Real.log (r + η) - Real.log (r - η)))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_unitCircleDensity hr.le hδ z, mul_one] at hint
  simpa [Real.norm_eq_abs] using hint

/-- The circle average of `J = log max(r, |· - z|)` over `∂B_ρ(z)` is `log max(r, ρ)`. -/
theorem circleAverage_circlePotential_eq {r : ℝ} (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (circlePotential r z) z ρ = Real.log (max r ρ) := by
  apply Real.circleAverage_const_on_circle
  intro x hx
  rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hρ] at hx
  unfold circlePotential
  rw [hx]

/-- `|∫ μ J - log r| ≤ e`: the polar identity for the radial weight and its support in `|ρ - r| < η`. -/
theorem abs_integral_unitCircleDensity_mul_circlePotential_sub_log_le {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hηr : η < r) (hwidth : δ ≤ r * η) (z : ℂ) :
    |(∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) - Real.log r| ≤
      Real.log (r + η) - Real.log (r - η) := by
  have hf : Integrable (fun x => circleDensity r δ hδ z x * circlePotential r z x) :=
    integrable_circleDensity_mul_of_unit hr.le hδ z
      (integrable_unitCircleDensity_mul hr.le hδ z (circlePotential_continuous hr z))
  have hpolar : (∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.circleAverage (circlePotential r z) z ρ :=
    integral_normalized_circleDensity_eq_circleAverage_of_integrable hδ z hf
  have hpolar' : (∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.log (max r ρ) := by
    rw [hpolar]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    rw [circleAverage_circlePotential_eq z hρ]
  have hW := circleDensityRadialWeight_integrableOn hr.le hδ
  have hcont : Continuous (fun ρ : ℝ => Real.log (max r ρ) - Real.log r) :=
    ((continuous_const.max continuous_id).log (fun ρ => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))).sub
      continuous_const
  have hpt : ∀ ρ : ℝ, 0 < ρ → ‖circleDensityRadialWeight r δ hδ ρ *
      (Real.log (max r ρ) - Real.log r)‖ ≤
      (Real.log (r + η) - Real.log (r - η)) * circleDensityRadialWeight r δ hδ ρ := by
    intro ρ hρ
    have hw0 := circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le
    by_cases hw : circleDensityRadialWeight r δ hδ ρ = 0
    · simp [hw]
    · have hsup := circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw
      obtain ⟨hs1, hs2⟩ := abs_lt.mp hsup
      have hc1 : Real.log r ≤ Real.log (max r ρ) := Real.log_le_log hr (le_max_left _ _)
      have hc2 : Real.log (max r ρ) ≤ Real.log (r + η) :=
        Real.log_le_log (lt_of_lt_of_le hr (le_max_left _ _))
          (max_le (by linarith) (by linarith))
      have hc3 : Real.log (r - η) ≤ Real.log r := Real.log_le_log (by linarith) (by linarith)
      have hbd : |Real.log (max r ρ) - Real.log r| ≤ Real.log (r + η) - Real.log (r - η) := by
        rw [abs_le]
        constructor <;> linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
      have := mul_le_mul_of_nonneg_left hbd hw0
      linarith [mul_comm (circleDensityRadialWeight r δ hδ ρ) (Real.log (r + η) - Real.log (r - η))]
  have hI1 : IntegrableOn (fun ρ => circleDensityRadialWeight r δ hδ ρ *
      (Real.log (max r ρ) - Real.log r)) (Ioi 0) := by
    refine Integrable.mono' (hW.const_mul (Real.log (r + η) - Real.log (r - η))) ?_ ?_
    · exact (hW.aestronglyMeasurable.mul hcont.aestronglyMeasurable)
    · exact (ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => hpt ρ hρ
  have hI2 : IntegrableOn (fun ρ => Real.log r * circleDensityRadialWeight r δ hδ ρ) (Ioi 0) :=
    hW.const_mul _
  have hsplit : (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.log (max r ρ)) =
      (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        (Real.log (max r ρ) - Real.log r)) + Real.log r := by
    have h1 : (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.log (max r ρ)) =
        ∫ ρ in Ioi (0 : ℝ), (circleDensityRadialWeight r δ hδ ρ *
          (Real.log (max r ρ) - Real.log r) + Real.log r * circleDensityRadialWeight r δ hδ ρ) :=
      setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => by ring)
    rw [h1, integral_add hI1 hI2, integral_const_mul, circleDensityRadialWeight_integral hr.le hδ,
      mul_one]
  have hfin : |∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
      (Real.log (max r ρ) - Real.log r)| ≤ Real.log (r + η) - Real.log (r - η) := by
    have hint := norm_integral_le_of_norm_le (hW.const_mul (Real.log (r + η) - Real.log (r - η)))
      ((ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => hpt ρ hρ)
    rw [integral_const_mul, circleDensityRadialWeight_integral hr.le hδ, mul_one] at hint
    simpa [Real.norm_eq_abs] using hint
  rw [hpolar', hsplit, add_sub_cancel_right]
  exact hfin

/-- The whole-plane covariance combination `Kpp + Kzz - 2 Kpc` of a unit annular density, bounded by the
uniform potential error. This is the variance of `hC μ - hcirc(r, z)` (see `variance_unitCircleDensity`). -/
theorem abs_unitCircleDensity_covariance_combination {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hηr : η < r) (hwidth : δ ≤ r * η) (z : ℂ) :
    |(∫ x, unitCircleDensity r δ hδ z x * ∫ y, unitCircleDensity r δ hδ z y * wholePlaneCov x y) +
        Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r -
      2 * ∫ x, unitCircleDensity r δ hδ z x * Real.circleAverage (fun y => wholePlaneCov x y) z r| ≤
      2 * (Real.log (r + η) - Real.log (r - η)) := by
  rw [integral_unitCircleDensity_mul_inner hr hδ hηr hwidth z,
    integral_unitCircleDensity_mul_circleAverage hr hδ z,
    circleAverage_circleAverage_wholePlaneCov hr z]
  have key : ∀ a b u j L : ℝ, (2 * a - u) + (2 * b - L) - 2 * (a + b - j) = (j - u) + (j - L) :=
    fun a b u j L => by ring
  rw [key]
  have h2 := abs_integral_unitCircleDensity_sub_potential_le hr hδ hηr hwidth z
  have h3 := abs_integral_unitCircleDensity_mul_circlePotential_sub_log_le hr hδ hηr hwidth z
  have h4 := abs_add_le ((∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) -
      ∫ x, unitCircleDensity r δ hδ z x * logPotential r δ hδ z x)
    ((∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) - Real.log r)
  linarith

end LatticeProb.Gauss

-- ===== FirstPass/S11u/Variance

/-!
# Variance of a pairing minus a circle average, and a.s. convergence from summable second moments

For a whole-plane GFF `(P, hC, hcirc)` and a test function `φ`, the variance of `hC φ - hcirc(r, z)` is the
combination `Kpp + Kzz - 2 Kpc` of the three kernel integrals (`IsWholePlaneGFF.covariance_eq`, `wholePlaneGFFCov`).
A centered random variable has variance equal to its second moment; summable second moments give almost sure
convergence (the lintegral-of-series argument).
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

universe u

/-- The variance of `hC φ - hcirc(r, z)` is the whole-plane kernel combination. -/
theorem variance_pairing_sub_circle_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    variance (fun ω => hC ω φ - hcirc ω r z) P =
      (∫ x, φ x * ∫ y, φ y * wholePlaneCov x y) +
        Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r -
      2 * ∫ x, φ x * Real.circleAverage (fun y => wholePlaneCov x y) z r := by
  have := hGFF.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  change variance ((fun ω => hC ω φ) - (fun ω => hcirc ω r z)) P = _
  rw [variance_sub hp hz, ← covariance_self hp.aemeasurable, ← covariance_self hz.aemeasurable]
  have hpp := hGFF.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
  have hzz := hGFF.covariance_eq (.circle r z) (.circle r z) hr hr
  have hpz := hGFF.covariance_eq (.pairing φ) (.circle r z) hφ hr
  simp only [GFFObservable.eval] at hpp hzz hpz
  rw [hpp, hzz, hpz]
  have key : ∀ a b c : ℝ, a - 2 * c + b = a + b - 2 * c := fun a b c => by ring
  rw [key]
  rfl

/-- A centered `hC φ - hcirc(r, z)` has variance equal to its second moment. -/
theorem integral_sq_pairing_sub_circle_eq_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    ∫ ω, (hC ω φ - hcirc ω r z) ^ 2 ∂P = variance (fun ω => hC ω φ - hcirc ω r z) P := by
  have := hGFF.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have hD : MemLp (fun ω => hC ω φ - hcirc ω r z) 2 P := hp.sub hz
  have hmean : ∫ ω, (hC ω φ - hcirc ω r z) ∂P = 0 := by
    have h1 := hGFF.integral_eq_zero (.pairing φ) hφ
    have h2 := hGFF.integral_eq_zero (.circle r z) hr
    simp only [GFFObservable.eval] at h1 h2
    rw [integral_sub (hp.integrable (by norm_num)) (hz.integrable (by norm_num)), h1, h2, sub_zero]
  rw [variance_eq_sub hD]
  simp only [Pi.pow_apply, hmean, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]

/-- Summable second moments give almost sure convergence to zero. -/
theorem ae_tendsto_zero_of_summable_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : ℕ → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 P) (b : ℕ → ℝ)
    (hb : Summable b) (hbound : ∀ j, ∫ ω, (D j ω) ^ 2 ∂P ≤ b j) :
    ∀ᵐ ω ∂P, Tendsto (fun j => D j ω) atTop (𝓝 0) := by
  have hsq : ∀ j, Integrable (fun ω => (D j ω) ^ 2) P := fun j => (hD j).integrable_sq
  have hnn : ∀ j, 0 ≤ᵐ[P] fun ω => (D j ω) ^ 2 := fun j => Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hbnn : ∀ j, 0 ≤ b j := fun j => (integral_nonneg fun ω => sq_nonneg _).trans (hbound j)
  have hmeas : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal ((D j ω) ^ 2)) P := fun j =>
    ((hD j).aemeasurable.pow_const 2).ennreal_ofReal
  have hFm : AEMeasurable (fun ω => ∑' j, ENNReal.ofReal ((D j ω) ^ 2)) P :=
    AEMeasurable.tsum hmeas
  have hlint : ∫⁻ ω, ∑' j, ENNReal.ofReal ((D j ω) ^ 2) ∂P ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have heq : ∀ j, ∫⁻ ω, ENNReal.ofReal ((D j ω) ^ 2) ∂P = ENNReal.ofReal (∫ ω, (D j ω) ^ 2 ∂P) :=
      fun j => (ofReal_integral_eq_lintegral_ofReal (hsq j) (hnn j)).symm
    simp only [heq]
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hbound j)) ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg hbnn hb]
    exact ENNReal.ofReal_lt_top
  filter_upwards [ae_lt_top' hFm hlint] with ω hω
  have hsum : Summable (fun j => (D j ω) ^ 2) := by
    have h := ENNReal.summable_toReal (f := fun j => ENNReal.ofReal ((D j ω) ^ 2)) hω.ne
    exact h.congr fun j => ENNReal.toReal_ofReal (sq_nonneg _)
  have h2 : Tendsto (fun j => (D j ω) ^ 2) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have h3 : Tendsto (fun j => |D j ω|) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp h2
    have hfun : (fun j => |D j ω|) = fun j => √((D j ω) ^ 2) := funext fun j => (Real.sqrt_sq_eq_abs _).symm
    rw [hfun]
    simpa [Function.comp_def, Real.sqrt_zero] using h
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h3

end LatticeProb.Gauss

-- ===== FirstPass/S11u (through log_add_sub_log_sub_le_four_mul)

/-!
# The circle-average limit derived from the whole-plane GFF

`WholePlaneCircleAverageLimitFrozen` (Frozen/S11p.lean) is proved as the theorem
`wholePlaneCircleAverageLimit_derived`, from `IsWholePlaneGFF` alone. The unit-mass test functions are the normalized
Section 8 annular bumps `unitCircleDensity r (r η) z` (support in `{| |x - z| - r | ≤ η}`, width `δ = r η`), with
`η_j = η₀ 2^{-j}`. The second moment of `hC ψ_j - hcirc(r, z)` is the whole-plane kernel combination, bounded by
`8 η_j / r` (`abs_unitCircleDensity_covariance_combination`), so the series converges almost surely.
Reference: Duplantier-Sheffield, arXiv:0808.1560v2, Section 3.1, Proposition 3.1; Bou-Rabee-Gwynne,
arXiv:2208.11795v3, Section 2.1 eq. (2.1), p. 8.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

universe u

/-- On the support of the annular density, `| |x - z| - r | < η` (from `|ρ² - r²| < δ = r η`). -/
theorem abs_norm_sub_radius_lt_of_unitCircleDensity_ne_zero {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hwidth : δ ≤ r * η) (z x : ℂ) (hx : unitCircleDensity r δ hδ z x ≠ 0) :
    |‖x - z‖ - r| < η := by
  have hcd : circleDensity r δ hδ z x ≠ 0 := (mul_ne_zero_iff.mp hx).2
  have hsup := circleDensity_support r δ hδ z x hcd
  rw [abs_lt] at hsup
  obtain ⟨h1, h2⟩ := hsup
  have hρ : 0 ≤ ‖x - z‖ := norm_nonneg _
  have hη : 0 < η := by
    by_contra hneg
    have hneg' : η ≤ 0 := not_lt.mp hneg
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

/-- The support of the normalized annular density lies in the closed annulus of width `η`. -/
theorem tsupport_unitCircleDensity_subset {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    (z : ℂ) :
    tsupport (unitCircleDensity r δ hδ z) ⊆ {x : ℂ | |‖x - z‖ - r| ≤ η} := by
  apply closure_minimal _ (isClosed_le (by fun_prop : Continuous fun x : ℂ => |‖x - z‖ - r|) continuous_const)
  intro x hx
  exact (abs_norm_sub_radius_lt_of_unitCircleDensity_ne_zero hr hδ hwidth z x hx).le

/-- The closed annulus `{| |x - z| - r | ≤ η}` lies in any thickening of the circle `∂B_r(z)` of width `> η`. -/
theorem annulus_subset_thickening {r η δ₀ : ℝ} (hr : 0 < r) (hηr : η < r / 2) (hηδ : η < δ₀) (z : ℂ) :
    {x : ℂ | |‖x - z‖ - r| ≤ η} ⊆ thickening δ₀ (sphere z r) := by
  intro x hx
  change |‖x - z‖ - r| ≤ η at hx
  have hρ : 0 < ‖x - z‖ := by
    have := (abs_le.mp hx).1
    linarith
  set ρ := ‖x - z‖ with hρdef
  set t : ℝ := r / ρ with htdef
  have ht : 0 < t := div_pos hr hρ
  rw [mem_thickening_iff]
  refine ⟨z + ((t : ℝ) : ℂ) * (x - z), ?_, ?_⟩
  · rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, htdef, ← hρdef]
    field_simp
  · have hxy : x - (z + ((t : ℝ) : ℂ) * (x - z)) = (((1 - t : ℝ)) : ℂ) * (x - z) := by
      push_cast
      ring
    rw [dist_eq_norm, hxy, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hρdef]
    have h1 : |1 - t| * ρ = |ρ - r| := by
      rw [show 1 - t = (ρ - r) / ρ by rw [htdef]; field_simp, abs_div, abs_of_pos hρ,
        div_mul_cancel₀ _ hρ.ne']
    rw [h1]
    linarith

/-- The normalized annular density is a test function on `O` once its annulus lies in `O`. -/
theorem isTestFunction_unitCircleDensity {O : Set ℂ} {r η : ℝ} (z : ℂ) (hr : 0 < r) (hη : 0 < η)
    (hO : {x : ℂ | |‖x - z‖ - r| ≤ η} ⊆ O) :
    IsTestFunction O (unitCircleDensity r (r * η) (mul_pos hr hη) z) := by
  refine ⟨?_, unitCircleDensity_hasCompactSupport hr.le (mul_pos hr hη) z, ?_⟩
  · exact ContDiff.mul contDiff_const (circleDensity_contDiff r (r * η) (mul_pos hr hη) z)
  · exact (tsupport_unitCircleDensity_subset hr (mul_pos hr hη) le_rfl z).trans hO

/-- `log(r + η) - log(r - η) ≤ 4 η / r` for `0 < η ≤ r / 2`. -/
theorem log_add_sub_log_sub_le_four_mul {r η : ℝ} (hr : 0 < r) (hη : 0 < η) (hηr : η ≤ r / 2) :
    Real.log (r + η) - Real.log (r - η) ≤ 4 * η / r := by
  have hpos : 0 < r - η := by linarith
  rw [← Real.log_div (by linarith) hpos.ne']
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (r + η) / (r - η) by positivity)
  have h2 : (r + η) / (r - η) - 1 ≤ 4 * η / r := by
    rw [div_sub_one hpos.ne', div_le_div_iff₀ hpos hr]
    nlinarith [mul_nonneg hη.le (show 0 ≤ r - 2 * η by linarith)]
  linarith

end LatticeProb.Gauss

-- ===== FirstPass/S11at/Producers (approximants and a.s. convergence)
namespace LatticeProb.Gauss

/-- The annular width parameter `η_j = (r/4) (1/2)^j` of the `j`-th explicit approximant. -/
noncomputable def approxEta (r : ℝ) (j : ℕ) : ℝ := (r / 4) * (1 / 2 : ℝ) ^ j

theorem approxEta_pos {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 < approxEta r j := by
  unfold approxEta; positivity

theorem approxEta_le {r : ℝ} (hr : 0 < r) (j : ℕ) : approxEta r j ≤ r / 4 := by
  unfold approxEta
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

/-- The explicit unit annular approximant `ψ_j` of the circle average at `(r, z)`: the density of
`FirstPass/S11u` with annulus width `r * η_j`. -/
noncomputable def circleApprox {r : ℝ} (hr : 0 < r) (z : ℂ) (j : ℕ) : ℂ → ℝ :=
  unitCircleDensity r (r * approxEta r j) (mul_pos hr (approxEta_pos hr j)) z

theorem integral_circleApprox {r : ℝ} (hr : 0 < r) (z : ℂ) (j : ℕ) :
    ∫ x, circleApprox hr z j x = 1 :=
  integral_unitCircleDensity hr.le (mul_pos hr (approxEta_pos hr j)) z

theorem isTestFunction_circleApprox {r : ℝ} (hr : 0 < r) (z : ℂ) (j : ℕ) :
    IsTestFunction univ (circleApprox hr z j) :=
  isTestFunction_unitCircleDensity z hr (approxEta_pos hr j) (subset_univ _)

/-- **A.s. convergence of the explicit annular approximants** (the argument of
`wholePlaneCircleAverageLimit_derived`, with the explicit geometric widths). -/
theorem ae_tendsto_circleApprox {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (circleApprox hr z j)) atTop (𝓝 (hcirc ω r z)) := by
  have hD : ∀ j, MemLp (fun ω => hC ω (circleApprox hr z j) - hcirc ω r z) 2 P := by
    intro j
    have hp : MemLp (fun ω => hC ω (circleApprox hr z j)) 2 P :=
      (hGFF.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing _, isTestFunction_circleApprox hr z j⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
    exact hp.sub hz
  have hbound : ∀ j, ∫ ω, (hC ω (circleApprox hr z j) - hcirc ω r z) ^ 2 ∂P ≤
      8 * (r / 4) / r * (1 / 2) ^ j := by
    intro j
    rw [integral_sq_pairing_sub_circle_eq_variance hGFF hr z _ (isTestFunction_circleApprox hr z j),
      variance_pairing_sub_circle_eq hGFF hr z _ (isTestFunction_circleApprox hr z j)]
    have hηr : approxEta r j ≤ r / 2 := (approxEta_le hr j).trans (by linarith)
    have hc := abs_unitCircleDensity_covariance_combination (r := r) (δ := r * approxEta r j)
      (η := approxEta r j) hr (mul_pos hr (approxEta_pos hr j)) (by linarith [approxEta_le hr j]) le_rfl z
    have hl := log_add_sub_log_sub_le_four_mul hr (approxEta_pos hr j) hηr
    refine le_trans (le_abs_self _) (le_trans hc ?_)
    have hscale : 2 * (4 * approxEta r j / r) = 8 * (r / 4) / r * (1 / 2) ^ j := by
      unfold approxEta
      field_simp
      ring
    linarith
  have hsum : Summable (fun j : ℕ => 8 * (r / 4) / r * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  filter_upwards [ae_tendsto_zero_of_summable_integral_sq
    (fun j ω => hC ω (circleApprox hr z j) - hcirc ω r z) hD _ hsum hbound] with ω hω
  exact tendsto_sub_nhds_zero_iff.mp hω

/-- Continuous observables: the annular averages converge to the circle average, for any widths
`δ_j → 0`. -/
theorem tendsto_unitCircleDensity_mul_continuous {r : ℝ} (hr : 0 < r) {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → δ j ≤ r * η) (z : ℂ) {f : ℂ → ℝ}
    (hf : Continuous f) :
    Tendsto (fun j => ∫ x, unitCircleDensity r (δ j) (hδ j) z x * f x) atTop
      (𝓝 (Real.circleAverage f z r)) := by
  have hg : Continuous (Real.circleAverage f z) := by fun_prop
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨κ, hκ, hk⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (half_pos hε)
  set η : ℝ := min κ (r / 2) with hηdef
  have hη : 0 < η := lt_min hκ (by linarith)
  have hηκ : η ≤ κ := min_le_left _ _
  obtain ⟨N, hN⟩ := hsmall η hη
  refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
  have hint := integral_normalized_circleDensity_eq_circleAverage hr.le (hδ j) z hf
  have hb := circleDensityRadialWeight_integral_sub_le hr (hδ j) (hN j hj) (Real.circleAverage f z) hg
    (ε := ε / 2) (by
      intro ρ hρ
      have hd : dist ρ r < κ := by
        rw [Real.dist_eq]
        linarith
      have := hk hd
      rw [Real.dist_eq] at this
      exact this.le)
  have hab := abs_le.mp hb
  unfold unitCircleDensity
  rw [Real.dist_eq, hint, abs_lt]
  constructor <;> linarith [hab.1, hab.2]

end LatticeProb.Gauss
