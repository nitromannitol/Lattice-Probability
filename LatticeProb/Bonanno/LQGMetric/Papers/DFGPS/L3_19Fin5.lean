/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19Fin5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin4
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.19, square part: (3.31) for the square

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), T:2300 ("proven similarly but
with Proposition 3.10 used in place of Proposition 3.9").

* `moment_sq_centre`: uniform moments of `𝔠_ρ⁻¹ e^{−ξ h_ρ(z)} diam(S^ρ(z); S^ρ(z))`, from
  Prop 3.10 at the corner `w = z − ρ(1+i)/2` (`moment_sq_corner`) and Hölder's inequality with the
  Gaussian `h_ρ(w) − h_ρ(z)` (variance `≤ 2`, `CircleAvg.incCov_self_le`) (DEVIATIONS DFA7b-2).
* `moment_sq`: (3.31) for the square `S^ρ(z) ⊆ B̄_ρ(z)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

lemma sqCentred_subset {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : sqCentred ρ z ⊆ closedBall z ρ := by
  rintro x ⟨u, ⟨h1, h2, h3, h4⟩, rfl⟩
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : ((ρ : ℂ) * u + (z - ((ρ / 2 : ℝ) : ℂ) * (1 + Complex.I)) - z).re =
      ρ * u.re - ρ / 2 := by simp; ring
  have him : ((ρ : ℂ) * u + (z - ((ρ / 2 : ℝ) : ℂ) * (1 + Complex.I)) - z).im =
      ρ * u.im - ρ / 2 := by simp; ring
  rw [hre, him]
  have a1 : |ρ * u.re - ρ / 2| ≤ ρ / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have a2 : |ρ * u.im - ρ / 2| ≤ ρ / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  linarith

lemma mem_sqCentred (ρ : ℝ) (z : ℂ) : z ∈ sqCentred ρ z := by
  refine ⟨(1 + Complex.I) / 2, ⟨by simp, by simp; norm_num, by simp, by simp; norm_num⟩, ?_⟩
  push_cast
  ring

lemma isOpen_sqCentred {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : IsOpen (sqCentred ρ z) :=
  isOpen_scaleSet_of hρ _ isOpen_unitSq

/-- uniform moments of `𝔠_ρ⁻¹ e^{−ξ h_ρ(z)} diam(S^ρ(z); S^ρ(z))` (Prop 3.10 + Hölder) -/
theorem moment_sq_centre (h310 : Prop3_10) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {p : ℝ} (hp0 : 0 < p) (hp : p < 4 * dGamma γ / γ ^ 2) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
        AEMeasurable (fun ω => internalDiam (D (h ω)) (sqCentred ρ z) (sqCentred ρ z)) P →
        ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ z)⁻¹ *
          internalDiam (D (h ω)) (sqCentred ρ z) (sqCentred ρ z)) ^ p ∂P ≤
            ENNReal.ofReal C := by
  set q := (p + 4 * dGamma γ / γ ^ 2) / 2 with hq_def
  have hpq : p < q := by rw [hq_def]; linarith
  have hq : q < 4 * dGamma γ / γ ^ 2 := by rw [hq_def]; linarith
  set a := q / p with ha_def
  have ha : 1 < a := (one_lt_div hp0).2 hpq
  set b := Real.conjExponent a with hb_def
  have hab : a.HolderConjugate b := Real.HolderConjugate.conjExponent ha
  have hb : 0 < b := div_pos (by linarith) (by linarith)
  have hpa : p * a = q := by rw [ha_def]; field_simp
  obtain ⟨C₁, hC₁⟩ := moment_sq_corner h310 hγ0 hγ2 hD hq
  set ξ := xiGamma γ with hξ_def
  set t := b * (p * ξ) with ht_def
  refine ⟨max C₁ 0 ^ (1 / a) * Real.exp (t ^ 2) ^ (1 / b), ?_⟩
  intro Ω _ P _ h hh ρ hρ z hDm
  set w := z - ((ρ / 2 : ℝ) : ℂ) * (1 + Complex.I) with hw_def
  set Dm : Ω → ℝ≥0∞ := fun ω => internalDiam (D (h ω)) (sqCentred ρ z) (sqCentred ρ z)
  set F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (scaleFac ξ c (h ω) ρ w)⁻¹ * Dm ω with hF_def
  set G : Ω → ℝ := CircleAvg.cInc h ρ w ρ z with hG_def
  have hGm : Measurable G := CircleAvg.measurable_cInc hh.1 ρ w ρ z
  set E : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (p * ξ * G ω)) with hE_def
  have hcρ : 0 < c ρ := hD.tightness.1 ρ hρ
  have hpt : ∀ ω, (ENNReal.ofReal (scaleFac ξ c (h ω) ρ z)⁻¹ * Dm ω) ^ p =
      (fun ω => F ω ^ p) ω * E ω := by
    intro ω
    simp only [hF_def, hE_def, hG_def, CircleAvg.cInc]
    have hA : ENNReal.ofReal (scaleFac ξ c (h ω) ρ z)⁻¹ = ENNReal.ofReal (scaleFac ξ c (h ω) ρ w)⁻¹ *
        ENNReal.ofReal (Real.exp (ξ * (circleAvg (h ω) ρ w - circleAvg (h ω) ρ z))) := by
      rw [← ENNReal.ofReal_mul (by unfold scaleFac; positivity)]
      congr 1
      rw [scaleFac, scaleFac, mul_inv, mul_inv, mul_assoc]
      congr 1
      rw [← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [hA, mul_right_comm, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp0.le, ← Real.exp_mul]
    congr 3
    ring
  rw [lintegral_congr hpt]
  have hFm : AEMeasurable F P := by
    show AEMeasurable (fun ω => ENNReal.ofReal (c ρ * Real.exp (ξ * circleAvg (h ω) ρ w))⁻¹ *
      Dm ω) P
    exact ((ENNReal.measurable_ofReal.comp ((measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_circleAvg_left ρ w).comp hh.1.measurable)))).inv)
      ).aemeasurable).mul hDm
  have hfm : AEMeasurable (fun ω => F ω ^ p) P := hFm.pow_const p
  have hEm : AEMeasurable E P :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hGm))).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hab hfm hEm
  simp only [Pi.mul_apply] at hH
  refine hH.trans ?_
  -- the moment of the square at the corner
  have h1 : ∫⁻ ω, (F ω ^ p) ^ a ∂P ≤ ENNReal.ofReal (max C₁ 0) := by
    simp_rw [← ENNReal.rpow_mul, hpa]
    exact (hC₁ P h hh ρ hρ w).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the Gaussian factor
  have h2 : ∫⁻ ω, E ω ^ b ∂P ≤ ENNReal.ofReal (Real.exp (t ^ 2)) := by
    have hE : ∀ ω, E ω ^ b = ENNReal.ofReal (Real.exp (t * G ω)) := fun ω => by
      simp only [hE_def]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hb.le, ← Real.exp_mul, ht_def]
      ring_nf
    simp_rw [hE]
    obtain ⟨hmap, -⟩ := CircleAvg.map_cInc hh.1 hρ hρ w z
    rw [lintegral_exp_of_map hGm hmap t]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hv := CircleAvg.incCov_self_le hρ hρ w z
    have hwz : ‖w - z‖ ≤ ρ := by
      rw [hw_def, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
        refine (norm_add_le _ _).trans ?_; simp; norm_num
      nlinarith [norm_nonneg ((1 : ℂ) + Complex.I)]
    rw [sub_self, abs_zero, zero_add, min_self] at hv
    have hv2 : CircleAvg.incCov w ρ z ρ w ρ z ρ ≤ 2 := by
      refine hv.trans ?_
      have : ‖w - z‖ / ρ ≤ 1 := by rw [div_le_one hρ]; exact hwz
      linarith
    have hv3 : ((CircleAvg.incCov w ρ z ρ w ρ z ρ).toNNReal : ℝ) ≤ 2 := by
      rw [Real.coe_toNNReal']; exact max_le hv2 (by norm_num)
    nlinarith [sq_nonneg t]
  calc (∫⁻ ω, (F ω ^ p) ^ a ∂P) ^ (1 / a) * (∫⁻ ω, E ω ^ b ∂P) ^ (1 / b)
      ≤ ENNReal.ofReal (max C₁ 0) ^ (1 / a) * ENNReal.ofReal (Real.exp (t ^ 2)) ^ (1 / b) := by
        gcongr
    _ = ENNReal.ofReal (max C₁ 0 ^ (1 / a) * Real.exp (t ^ 2) ^ (1 / b)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
          ENNReal.ofReal_mul (by positivity)]

/-- **(3.31) for the square** `S^ρ(z) ⊆ B̄_ρ(z)`. -/
theorem moment_sq (h310 : Prop3_10) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    {p : ℝ} (hp0 : 0 < p) (hp : p < 4 * dGamma γ / γ ^ 2) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → ∀ z : ℂ,
        AEMeasurable (fun ω => ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ *
          internalDiam (D (h ω)) (sqCentred ρ z) (sqCentred ρ z)) P ∧
        ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ *
          internalDiam (D (h ω)) (sqCentred ρ z) (sqCentred ρ z)) ^ p ∂P ≤
        ENNReal.ofReal ((c ρ / c r) ^ p *
          Real.exp ((Real.log r - Real.log ρ) * (p * xiGamma γ) ^ 2 / 2) * C) := by
  obtain ⟨C, hC⟩ := moment_sq_centre h310 hγ0 hγ2 hD hp0 hp
  refine ⟨C, ?_⟩
  intro Ω _ P _ h hh ρ r hρ hρr z
  set U : Opens ℂ := ⟨sqCentred ρ z, isOpen_sqCentred hρ z⟩
  obtain ⟨Y, hYm, hI, hYae⟩ := indepFun_internalDiamU hD hh.1 z hρ hρr U
    (sqCentred_subset hρ z) (A := sqCentred ρ z) subset_rfl ⟨z, mem_sqCentred ρ z⟩
  have hDm : AEMeasurable (fun ω => internalDiam (D (h ω)) (sqCentred ρ z) (sqCentred ρ z)) P := by
    have hm : Measurable fun ω =>
        ENNReal.ofReal (Real.exp (xiGamma γ * circleAvg (h ω) ρ z)) * Y ω :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
        ((measurable_circleAvg_left ρ z).comp hh.1.measurable)))).mul hYm
    refine hm.aemeasurable.congr (hYae.mono fun ω hω => ?_)
    dsimp only
    rw [hω, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one, one_mul]
    rfl
  exact moment_of_local hD hh.1 z hρ hρr _ hYm hI hYae hp0.le (hC P h hh ρ hρ z hDm)

end L319
end LQGMetric.DFGPS
