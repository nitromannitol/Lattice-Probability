/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4a, part 3: the Green potential of `1` vanishes at `∂U` (packet P-127C)

`∫ G_U(x, y) dy = π E^x[τ_U]` (Berestycki–Powell arXiv:2404.16642 §1.2, `G_D = π ∫₀^∞ p_D`), and
`E^x[τ_U] ≤ 2h + P^x(τ_U > h) · 2R⁴/h` for `U ⊆ B(c, R)` (Markov property at time `s/2` and
`p_U(s; ·, ·) ≤ R²/(π s²)`, `killedHeat_le_rpow`). With the decay of `P^x(τ_U > h)` near `Uᶜ`
(`exists_killedSurv_le_of_corkscrew`) this gives D127 N4(a):

`integral_killedGreen_le_of_corkscrew`: `∀ ε > 0, ∃ η > 0, ∀ x, infDist x Uᶜ < η →
∫ y, killedGreen U x y ≤ ε` for bounded open `U` with an exterior corkscrew condition.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat

/-- `P^w(τ_U > s) ≤ R⁴ s⁻²` for `U ⊆ B(c, R)`. -/
theorem killedSurv_le_rpow {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {s : ℝ} (hs : 0 < s) (w : ℂ) :
    killedSurv U s.toNNReal w ≤ ENNReal.ofReal (R ^ 4 * s ^ (-2 : ℝ)) := by
  have hs' : s.toNNReal ≠ 0 := by simpa using hs
  unfold killedSurv
  have hsupp : Function.support (fun y ↦ ENNReal.ofReal (killedHeat U s.toNNReal w y)) ⊆
      ball c R := fun y hy ↦ by
    by_contra h
    exact hy (by dsimp only; rw [killedHeat_eq_zero_of_not_mem_right hU hs' w (fun h' ↦ h (hUR h')),
      ENNReal.ofReal_zero])
  rw [← setLIntegral_eq_of_support_subset hsupp]
  calc ∫⁻ y in ball c R, ENNReal.ofReal (killedHeat U s.toNNReal w y)
      ≤ ∫⁻ _ in ball c R, ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ)) :=
        setLIntegral_mono measurable_const fun y _ ↦
          ENNReal.ofReal_le_ofReal (killedHeat_le_rpow hR hUR hs w y)
    _ = ENNReal.ofReal (R ^ 4 * s ^ (-2 : ℝ)) := by
        rw [setLIntegral_const, Complex.volume_ball, ← ENNReal.ofReal_pow hR,
          ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), NNReal.coe_real_pi]
        congr 1
        field_simp

/-- `P^x(τ > s) ≤ P^x(τ > h) · 4R⁴ s⁻²` for `s ≥ 2h` (Markov property at `s/2`). -/
theorem killedSurv_le_mul_rpow {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {h : ℝ≥0} (hh : h ≠ 0) {s : ℝ} (hs : 2 * (h : ℝ) ≤ s) (x : ℂ) :
    killedSurv U s.toNNReal x ≤ killedSurv U h x * ENNReal.ofReal (4 * R ^ 4 * s ^ (-2 : ℝ)) := by
  have hh' : (0 : ℝ) < h := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
  have hs0 : 0 < s := by linarith
  have hs2 : 0 < s / 2 := by linarith
  have hne : (s / 2).toNNReal ≠ 0 := by simpa using hs2
  have hsplit : s.toNNReal = (s / 2).toNNReal + (s / 2).toNNReal := by
    rw [← Real.toNNReal_add hs2.le hs2.le, add_halves]
  have hb : ∀ w, killedSurv U (s / 2).toNNReal w ≤ ENNReal.ofReal (4 * R ^ 4 * s ^ (-2 : ℝ)) :=
    fun w ↦ (killedSurv_le_rpow hU hR hUR hs2 w).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by
      rw [Real.div_rpow hs0.le zero_le_two, Real.rpow_neg zero_le_two, Real.rpow_neg hs0.le,
        Real.rpow_two]
      field_simp
      ring)))
  rw [hsplit, killedSurv_add hU hne hne]
  calc ∫⁻ w, ENNReal.ofReal (killedHeat U (s / 2).toNNReal x w) * killedSurv U (s / 2).toNNReal w
      ≤ ∫⁻ w, ENNReal.ofReal (killedHeat U (s / 2).toNNReal x w) *
          ENNReal.ofReal (4 * R ^ 4 * s ^ (-2 : ℝ)) :=
        lintegral_mono fun w ↦ mul_le_mul' le_rfl (hb w)
    _ = killedSurv U (s / 2).toNNReal x * ENNReal.ofReal (4 * R ^ 4 * s ^ (-2 : ℝ)) := by
        rw [lintegral_mul_const _ (measurable_killedHeat_right hU hne x).ennreal_ofReal]
        rfl
    _ ≤ _ := by
        refine mul_le_mul' (killedSurv_anti hU hh ?_ x) le_rfl
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs2.le]
        linarith

/-- `∫ P^x(τ > s) ds ≤ 2h + P^x(τ > h) · 2R⁴/h`. -/
theorem lintegral_killedSurv_le {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) {h : ℝ≥0} (hh : h ≠ 0) (x : ℂ) :
    ∫⁻ s in Ioi (0 : ℝ), killedSurv U s.toNNReal x ≤
      ENNReal.ofReal (2 * h) + killedSurv U h x * ENNReal.ofReal (2 * R ^ 4 / h) := by
  have hh' : (0 : ℝ) < h := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
  have h2h : (0 : ℝ) ≤ 2 * h := by positivity
  rw [← Ioc_union_Ioi_eq_Ioi h2h, lintegral_union measurableSet_Ioi
    (Ioc_disjoint_Ioi le_rfl)]
  refine add_le_add ?_ ?_
  · calc ∫⁻ s in Ioc 0 (2 * (h : ℝ)), killedSurv U s.toNNReal x
        ≤ ∫⁻ _ in Ioc 0 (2 * (h : ℝ)), (1 : ℝ≥0∞) :=
          setLIntegral_mono measurable_const fun s hs ↦
            killedSurv_le_one U (by simpa using hs.1) x
      _ = ENNReal.ofReal (2 * h) := by simp
  · have hmf : Measurable fun s : ℝ ↦ ENNReal.ofReal (4 * R ^ 4 * s ^ (-2 : ℝ)) :=
      ((measurable_id.pow_const (-2 : ℝ)).const_mul (4 * R ^ 4)).ennreal_ofReal
    have hint : IntegrableOn (fun s : ℝ ↦ 4 * R ^ 4 * s ^ (-2 : ℝ)) (Ioi (2 * (h : ℝ))) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)).const_mul _
    calc ∫⁻ s in Ioi (2 * (h : ℝ)), killedSurv U s.toNNReal x
        ≤ ∫⁻ s in Ioi (2 * (h : ℝ)),
            killedSurv U h x * ENNReal.ofReal (4 * R ^ 4 * s ^ (-2 : ℝ)) :=
          setLIntegral_mono (hmf.const_mul _)
            fun s hs ↦ killedSurv_le_mul_rpow hU hR hUR hh (le_of_lt hs) x
      _ = killedSurv U h x * ENNReal.ofReal (∫ s in Ioi (2 * (h : ℝ)),
            4 * R ^ 4 * s ^ (-2 : ℝ)) := by
          rw [lintegral_const_mul _ hmf,
            ofReal_integral_eq_lintegral_ofReal hint]
          refine (ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ ?_
          have : 0 < s := lt_of_le_of_lt h2h hs
          positivity
      _ = killedSurv U h x * ENNReal.ofReal (2 * R ^ 4 / h) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by positivity)]
          congr 2
          rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
          field_simp
          ring

/-- `∫ G_U(x, y) dy ≤ π ∫₀^∞ P^x(τ > s) ds` (`G_U = π ∫₀^∞ p_U`, Tonelli). -/
theorem lintegral_killedGreen_le {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    ∫⁻ y, ENNReal.ofReal (killedGreen U x y) ≤
      ENNReal.ofReal Real.pi * ∫⁻ s in Ioi (0 : ℝ), killedSurv U s.toNNReal x := by
  have hmeas : Measurable fun q : ℂ × ℝ ↦ ENNReal.ofReal (killedHeat U q.2.toNNReal x q.1) :=
    ((measurable_killedHeat hU).comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
      (measurable_const.prodMk measurable_fst))).ennreal_ofReal
  calc ∫⁻ y, ENNReal.ofReal (killedGreen U x y)
      ≤ ∫⁻ y, ENNReal.ofReal Real.pi *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal x y) := by
        refine lintegral_mono fun y ↦ ?_
        rw [killedGreen, ENNReal.ofReal_mul Real.pi_pos.le]
        refine mul_le_mul' le_rfl ?_
        by_cases hi : IntegrableOn (fun s : ℝ ↦ killedHeat U s.toNNReal x y) (Ioi 0)
        · rw [ofReal_integral_eq_lintegral_ofReal hi
            (Filter.Eventually.of_forall fun s ↦ killedHeat_nonneg _ _ _ _)]
        · rw [integral_undef hi, ENNReal.ofReal_zero]; exact zero_le
    _ = ENNReal.ofReal Real.pi * ∫⁻ s in Ioi (0 : ℝ), killedSurv U s.toNNReal x := by
        rw [lintegral_const_mul _ (hmeas.lintegral_prod_right')]
        unfold killedSurv
        congr 1
        rw [lintegral_lintegral_swap hmeas.aemeasurable]

/-- **D127 N4(a)**: for bounded open `U` with an exterior corkscrew condition, the Green
potential of `1` (`π E^x[τ_U]`) tends to `0` at `Uᶜ`, uniformly. -/
theorem integral_killedGreen_le_of_corkscrew {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hUR : U ⊆ ball c R) {L : ℝ} (hL : 0 < L) (hcork : ExtCorkscrew U L) :
    ∀ ε > 0, ∃ η > 0, ∀ x : ℂ, infDist x Uᶜ < η → ∫ y, killedGreen U x y ≤ ε := by
  intro ε hε
  have hπ := Real.pi_pos
  set h : ℝ≥0 := (ε / (4 * Real.pi)).toNNReal with hh_def
  have hh' : (h : ℝ) = ε / (4 * Real.pi) := Real.coe_toNNReal _ (by positivity)
  have hh0 : h ≠ 0 := by
    intro h0; have : (h : ℝ) = 0 := by rw [h0]; rfl
    rw [hh'] at this; have : 0 < ε / (4 * Real.pi) := by positivity
    linarith
  have hhpos : (0 : ℝ) < h := by rw [hh']; positivity
  set δ : ℝ := ε * h / (4 * Real.pi * (2 * R ^ 4)) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨η, hη, hηs⟩ := exists_killedSurv_le_of_corkscrew hU hL hcork hδ hh0
  refine ⟨η, hη, fun x hx ↦ ?_⟩
  have hne : (Uᶜ).Nonempty := by
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w ∉ ball c R :=
      ⟨c + R, by simp [mem_ball, dist_eq_norm, abs_of_pos hR]⟩
    exact ⟨w, fun h' ↦ hw (hUR h')⟩
  obtain ⟨p, hp, hxp⟩ := (infDist_lt_iff hne).mp hx
  have hS := hηs x p hp hxp
  have hL' : ∫⁻ y, ENNReal.ofReal (killedGreen U x y) ≤ ENNReal.ofReal ε := by
    refine (lintegral_killedGreen_le hU x).trans ?_
    refine (mul_le_mul' le_rfl (lintegral_killedSurv_le hU hR.le hUR hh0 x)).trans ?_
    calc ENNReal.ofReal Real.pi *
          (ENNReal.ofReal (2 * h) + killedSurv U h x * ENNReal.ofReal (2 * R ^ 4 / h))
        ≤ ENNReal.ofReal Real.pi *
          (ENNReal.ofReal (2 * h) + ENNReal.ofReal δ * ENNReal.ofReal (2 * R ^ 4 / h)) := by
          gcongr
      _ = ENNReal.ofReal (Real.pi * (2 * h + δ * (2 * R ^ 4 / h))) := by
          rw [← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul hπ.le]
      _ = ENNReal.ofReal (3 * ε / 4) := by
          congr 1
          rw [hδ_def, hh']
          field_simp
          ring
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  by_cases hi : Integrable fun y ↦ killedGreen U x y
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun y ↦ killedGreen_nonneg U x y) hi.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'
  · rw [integral_undef hi]; exact hε.le

end ZBM
end CONF
end LQGMetric
