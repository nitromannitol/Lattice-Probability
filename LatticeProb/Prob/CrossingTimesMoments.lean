import Mathlib
import LatticeProb.Prob.CrossingTimesRenewal
import LatticeProb.Prob.BrownianStayTail

/-!
# Second moment of the first crossing time of a Brownian motion

The first `ε`-crossing time `σ₁ = crossTime ε (B · ω) 1` of a Brownian motion `B` in `ℝ ^ d` is the
first exit time from the closed-threshold ball of radius `ε`; it does not depend on the starting
point of `B`.  The exponential tail of the time spent in a ball (`exists_brownian_stay_tail`)
gives `P (σ₁ > t) ≤ c exp (- r t)` with `r = c₁ / ε ^ 2`, hence `E σ₁ ^ 2 ≤ C ε ^ 4`, where `C`
depends only on the dimension.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- **Second moment from an exponential tail.**  If `P (f > t) ≤ c exp (- r t)` for every
`t > 0`, then `E f ^ 2 ≤ 2 c / r ^ 2`. -/
theorem lintegral_sq_le_of_exp_tail {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[P] f) (hf : AEMeasurable f P)
    {c r : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < f ω} ≤ ENNReal.ofReal (c * Real.exp (-(r * t)))) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal (2 * c / r ^ 2) := by
  have hp := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := P) hf0 hf (p := 2) two_pos
  simp only [Real.rpow_two] at hp
  rw [hp]
  have hI : IntegrableOn (fun t : ℝ => c * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r) (by norm_num)
      one_pos hr
    refine IntegrableOn.congr_fun (h.const_mul c) (fun t _ => ?_) measurableSet_Ioi
    norm_num [neg_mul]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t : ℝ => c * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t))) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht =>
      mul_nonneg hc (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le))
  calc ENNReal.ofReal 2 * ∫⁻ t in Ioi 0, P {a | t < f a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
      ≤ ENNReal.ofReal 2 * ∫⁻ t in Ioi 0,
          ENNReal.ofReal (c * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))) := by
        gcongr ENNReal.ofReal 2 * ?_
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        calc P {a | t < f a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))
            ≤ ENNReal.ofReal (c * Real.exp (-(r * t))) * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) :=
              by gcongr; exact htail t ht
          _ = ENNReal.ofReal (c * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))) := by
              rw [← ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_pos _).le)]
              congr 1
              ring
    _ = ENNReal.ofReal 2 * ENNReal.ofReal
          (∫ t in Ioi 0, c * (t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hI hnn]
    _ = ENNReal.ofReal (2 * c / r ^ 2) := by
        rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        norm_num [Real.Gamma_two, Real.rpow_two]
        field_simp

omit [MeasurableSpace Ω] in
/-- The first crossing time of the centred motion is the first crossing time of the motion. -/
theorem crossTime_restartPath_zero (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun t => B t ω) (ε : ℝ) (k : ℕ) (ω : Ω) :
    crossTime ε (fun s => restartPath B hcont (fun _ => 0) ω s) k =
      crossTime ε (fun t => B t ω) k := by
  have h : (fun s => restartPath B hcont (fun _ => 0) ω s) =
      fun s => (fun t => B t ω) s - B 0 ω := by
    funext s
    simp [restartPath]
  rw [h]
  exact congrFun (crossTime_sub_const ε (fun t => B t ω) (B 0 ω)) k

omit [MeasurableSpace Ω] in
/-- If the first `ε`-crossing time of a path started at `x` exceeds `t`, the path stays within
distance `ε` of `x` up to time `t`. -/
theorem norm_lt_of_lt_crossTime_one {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} {ω : Ω} (hx : B 0 ω = x) {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (hlt : t < (crossTime ε (fun t => B t ω) 1).toReal) :
    ∀ s : ℝ≥0, (s : ℝ) ≤ t → ‖B s ω - x‖ < ε := by
  intro s hs
  by_contra hcon
  have hout : B s ω ∉ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hcon
  have h3 : crossTime ε (fun t => B t ω) 1 ≤ (s : ℝ≥0∞) :=
    (crossTime_one_le_openExitTime hx hε).trans (openExitTime_le_of_not_mem hout)
  have h4 := ENNReal.toReal_mono ENNReal.coe_ne_top h3
  rw [ENNReal.coe_toReal] at h4
  linarith

/-- **The second moment of the first `ε`-crossing time of a Brownian motion is at most
`C ε ^ 4`, with `C` depending only on the dimension.** -/
theorem exists_crossTime_one_sq_lintegral_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      IsBrownianSpace d x B P → (∀ t, StronglyMeasurable (B t)) →
      (∀ ω, Continuous fun t => B t ω) → ∀ ε : ℝ, 0 < ε →
        ∫⁻ ω, (crossTime ε (fun t => B t ω) 1) ^ 2 ∂P ≤ ENNReal.ofReal (C * ε ^ 4) := by
  obtain ⟨c0, c1, hc0, hc1, hstay⟩ := exists_brownian_stay_tail d hd
  have hc'0 : 0 ≤ max c0 (Real.exp c1) := le_trans hc0.le (le_max_left _ _)
  refine ⟨2 * max c0 (Real.exp c1) / c1 ^ 2, by positivity, ?_⟩
  intro Ω _ P _ x B hB hm hcont ε hε
  have hε2 : 0 < ε ^ 2 := by positivity
  have hTm : Measurable fun ω => crossTime ε (fun t => B t ω) 1 :=
    measurable_crossTime_process B hm hcont hε 1
  have hfin : ∀ᵐ ω ∂P, crossTime ε (fun t => B t ω) 1 ≠ ⊤ := ae_crossTime_one_ne_top hd hB hε
  have htail : ∀ t : ℝ, 0 < t → P {ω | t < (crossTime ε (fun t => B t ω) 1).toReal} ≤
      ENNReal.ofReal (max c0 (Real.exp c1) * Real.exp (-(c1 / ε ^ 2 * t))) := by
    intro t ht
    have hexp : c1 / ε ^ 2 * t = c1 * (t / ε ^ 2) := by ring
    rw [hexp]
    by_cases hA : 1 ≤ t / ε ^ 2
    · have h1 := hstay x Ω P ‹_› B hB ε hε (t / ε ^ 2) hA
      have hsub : {ω | t < (crossTime ε (fun t => B t ω) 1).toReal} ≤ᵐ[P]
          {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ t / ε ^ 2 * ε ^ 2 → ‖B s ω - x‖ < ε} := by
        filter_upwards [hB.start] with ω hω hmem
        rw [div_mul_cancel₀ _ hε2.ne']
        exact norm_lt_of_lt_crossTime_one hω hε hmem
      calc P {ω | t < (crossTime ε (fun t => B t ω) 1).toReal}
          ≤ P {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ t / ε ^ 2 * ε ^ 2 → ‖B s ω - x‖ < ε} :=
            measure_mono_ae hsub
        _ ≤ ENNReal.ofReal (c0 * Real.exp (-(c1 * (t / ε ^ 2)))) := h1
        _ ≤ ENNReal.ofReal (max c0 (Real.exp c1) * Real.exp (-(c1 * (t / ε ^ 2)))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · push Not at hA
      refine (prob_le_one).trans ?_
      rw [ENNReal.one_le_ofReal]
      have h2 : Real.exp (-c1) ≤ Real.exp (-(c1 * (t / ε ^ 2))) :=
        Real.exp_le_exp.2 (neg_le_neg (mul_le_of_le_one_right hc1.le hA.le))
      calc (1 : ℝ) = Real.exp c1 * Real.exp (-c1) := by rw [← Real.exp_add]; simp
        _ ≤ max c0 (Real.exp c1) * Real.exp (-(c1 * (t / ε ^ 2))) :=
          mul_le_mul (le_max_right _ _) h2 (Real.exp_pos _).le hc'0
  have hM := lintegral_sq_le_of_exp_tail (P := P)
    (f := fun ω => (crossTime ε (fun t => B t ω) 1).toReal)
    (Eventually.of_forall fun ω => ENNReal.toReal_nonneg) hTm.ennreal_toReal.aemeasurable hc'0
    (div_pos hc1 hε2) htail
  have hae : ∀ᵐ ω ∂P, (crossTime ε (fun t => B t ω) 1) ^ 2 =
      ENNReal.ofReal ((crossTime ε (fun t => B t ω) 1).toReal ^ 2) := by
    filter_upwards [hfin] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω]
  rw [lintegral_congr_ae hae]
  refine hM.trans (le_of_eq ?_)
  congr 1
  field_simp

end LatticeProb
