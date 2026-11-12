/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19Fin at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19ProofMom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4Tail
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 3.19,
T:2274–2297.

* `moment_eps`: (3.31), `E[(𝔠_r⁻¹ e^{−ξ h_r(z)} diam(B_{ρ/2}(z); B_ρ(z)))^p]
  ≤ (𝔠_ρ/𝔠_r)^p e^{ξ²p² log(r/ρ)/2} C_p` (T:2282–2289), from the independence of
  `h_ρ(z) − h_r(z)` and the local diameter (`indepFun_internalDiam`), `E[e^X] = e^{Var X/2}`
  (`lintegral_factor`) and Prop 3.9 at centre `z` (`moment_ball`).
* `cheb`: the Chebyshev inequality used at T:2292.
* `p_lt`: `p = (ξQ − s)/ξ² < 4/(γξ) = 4 dγ/γ²` for `s > 0`, `γ < 2` (T:2296).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **(3.31)** (T:2282–2289), with `ρ = 2ε𝕣`, `r = 𝕣` in the paper. -/
theorem moment_eps (h39 : Prop3_9) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 4 * dGamma γ / γ ^ 2) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ρ r : ℝ, 0 < ρ → ρ ≤ r → ∀ z : ℂ,
        AEMeasurable (fun ω => ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ *
          internalDiam (D (h ω)) (ball z (ρ / 2)) (ball z ρ)) P ∧
        ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ *
          internalDiam (D (h ω)) (ball z (ρ / 2)) (ball z ρ)) ^ p ∂P ≤
        ENNReal.ofReal ((c ρ / c r) ^ p *
          Real.exp ((Real.log r - Real.log ρ) * (p * xiGamma γ) ^ 2 / 2) * C) := by
  obtain ⟨C, hC⟩ := moment_ball h39 hγ0 hγ2 hD hp0 hp
  refine ⟨C, ?_⟩
  intro Ω _ P _ h hh ρ r hρ hρr z
  have hr : 0 < r := hρ.trans_le hρr
  set ξ := xiGamma γ with hξ_def
  obtain ⟨Y, hYm, hI, hYae⟩ := indepFun_internalDiam hD hh.1 z hρ hρr
    (A := ball z (ρ / 2)) (ball_subset_ball (by linarith)) (nonempty_ball.2 (by positivity))
  set Y' : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (c ρ)⁻¹ * Y ω with hY'_def
  have hY'm : Measurable Y' := measurable_const.mul hYm
  have hI' : IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y' P :=
    hI.comp (φ := id) (ψ := fun y : ℝ≥0∞ => ENNReal.ofReal (c ρ)⁻¹ * y) measurable_id
      (measurable_const.mul measurable_id)
  have hfac := lintegral_factor hh.1 z hρ hρr hY'm hI' ξ p hp0
  have hcρ : 0 < c ρ := hD.tightness.1 ρ hρ
  have hcr : 0 < c r := hD.tightness.1 r hr
  set X : Ω → ℝ := fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z with hX_def
  have hXm : Measurable X := CircleAvg.measurable_cInc hh.1 ρ z r z
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (scaleFac ξ c (h ω) r z)⁻¹ *
      internalDiam (D (h ω)) (ball z (ρ / 2)) (ball z ρ) =
      ENNReal.ofReal (c ρ / c r) * (ENNReal.ofReal (Real.exp (ξ * X ω)) * Y' ω) := by
    filter_upwards [hYae] with ω hω
    rw [hY'_def]
    simp only
    rw [hω, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [scaleFac, hX_def]
    simp only
    rw [mul_sub, Real.exp_sub, Real.exp_neg]
    field_simp
    rw [hξ_def, mul_comm]
  have hae2 : ∀ᵐ ω ∂P, Y' ω = ENNReal.ofReal (scaleFac ξ c (h ω) ρ z)⁻¹ *
      internalDiam (D (h ω)) (ball z (ρ / 2)) (ball z ρ) := by
    filter_upwards [hYae] with ω hω
    rw [hY'_def]
    simp only
    rw [hω, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [scaleFac, Real.exp_neg, mul_inv]
  have hmeasW : Measurable fun ω => ENNReal.ofReal (c ρ / c r) *
      (ENNReal.ofReal (Real.exp (ξ * X ω)) * Y' ω) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hXm))).mul hY'm)
  refine ⟨hmeasW.aemeasurable.congr (hae.mono fun ω hω => hω.symm), ?_⟩
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  set W : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (ξ * X ω)) * Y' ω with hW_def
  have hWm : Measurable W := (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hXm))).mul hY'm
  rw [show (fun ω => (ENNReal.ofReal (c ρ / c r) * W ω) ^ p) =
      fun ω => ENNReal.ofReal (c ρ / c r) ^ p * W ω ^ p from
    funext fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp0, lintegral_const_mul _ (hWm.pow_const p)]
  rw [hfac, lintegral_congr_ae (hae2.mono fun ω hω => by rw [hω])]
  have hb := hC P h hh ρ hρ z
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  gcongr

/-- Chebyshev's inequality with a `p`-th moment (T:2292) -/
lemma cheb {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f P) {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    P {ω | ENNReal.ofReal t ≤ f ω} ≤ (∫⁻ ω, f ω ^ p ∂P) / ENNReal.ofReal (t ^ p) := by
  refine (measure_mono fun ω (hω : ENNReal.ofReal t ≤ f ω) => ?_).trans
    (meas_ge_le_lintegral_div (hf.pow_const p) (by simp [Real.rpow_pos_of_pos ht])
      ENNReal.ofReal_ne_top)
  show ENNReal.ofReal (t ^ p) ≤ f ω ^ p
  rw [← ENNReal.ofReal_rpow_of_nonneg ht.le hp.le]
  exact ENNReal.rpow_le_rpow hω hp.le

/-- `p = (ξQ − s)/ξ² < 4 dγ/γ²` (T:2296: "always at most `4/(ξγ)` for `s > 0` since `γ < 2`") -/
lemma p_lt (hγ0 : 0 < γ) (hγ2 : γ < 2) {s : ℝ} (hs : 0 < s) :
    (xiGamma γ * Q γ - s) / xiGamma γ ^ 2 < 4 * dGamma γ / γ ^ 2 := by
  have hd : 0 < dGamma γ := DG.dGamma_pos γ
  have hξ : xiGamma γ = γ / dGamma γ := rfl
  rw [hξ, div_lt_div_iff₀ (by positivity) (by positivity), Q]
  have e : (γ / dGamma γ * (2 / γ + γ / 2) - s) * γ ^ 2 =
      (2 + γ ^ 2 / 2) / dGamma γ * γ ^ 2 - s * γ ^ 2 := by field_simp
  rw [e, div_pow, mul_div_assoc', lt_div_iff₀ (by positivity)]
  have h1 : (2 + γ ^ 2 / 2) / dGamma γ * γ ^ 2 * dGamma γ ^ 2 =
      (2 + γ ^ 2 / 2) * dGamma γ * γ ^ 2 := by field_simp
  rw [sub_mul, h1]
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have : 0 < s * γ ^ 2 * dGamma γ ^ 2 := by positivity
  nlinarith [mul_pos hd (by positivity : (0:ℝ) < γ ^ 2)]

end L319
end LQGMetric.DFGPS
