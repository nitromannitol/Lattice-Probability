/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L6Log at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2BridgeLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Cont

/-!
# DZZ Lemma 2.6, first inequality (task P2-DZZPRE2)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 516–538 (Lemma
`lem-continuity-h-eta`). DZZ's proof uses `Var(η_δ(v) − η_δ(u)) = O(log(k + 1))` for
`|v − u| ≤ kδ` (l. 530) together with Lemma 2.5 and Fernique/concentration (the latter two are
`dzz_lemma26_core`, S2Cont). Here:

* `variance_etaInf_sub_log`: `Var(η_δ(u) − η_δ(v)) ≤ 2152 (1 + log(1 + |u − v|/δ))`. Proof (DZZ
  give none): for `D = |u − v| > δ` split the time integral at `D²`; the part `(D², ∞)` is
  Lemma 2.5 at scale `D`, the part `(δ², D²)` has variance `π∫_{δ²}^{D²} p(s; u, u) ds ≤ log(D/δ)`
  at each point (`p ≤ (2πs)⁻¹`). Standard, own elementary write-up.
* `exists_continuous_etaInf`: continuous versions of `η_δ` (Kolmogorov, Lemma 2.5).
* `dzz_lemma26_eta`: **DZZ Lemma 2.6, first inequality**, for continuous versions of `η_δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

/-- `π ‖K^η_I(u)‖² ≤ log(b/a)/2` for `I = (a, b)`, `0 < a ≤ b`. -/
lemma pi_sq_norm_etaKernelL2_Ioo_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (u : ℂ) :
    Real.pi * ‖etaKernelL2 (Ioo a b) u‖ ^ 2 ≤ Real.log (b / a) / 2 := by
  have hI0 : Ioo a b ⊆ Ioi a := Ioo_subset_Ioi_self
  have nu : ∫ p, etaKernel (Ioo a b) u p * etaKernel (Ioo a b) u p =
      ∫ s in Ioo a b, killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel measurableSet_Ioo u)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time u)
      (fun s => killedHeat_nonneg _ _ _ _)
      (lintegral_etaKernel_sq measurableSet_Ioo (hI0.trans (Ioi_subset_Ioi ha.le)) u)
  rw [← real_inner_self_eq_norm_sq, inner_etaKernelL2 measurableSet_Ioo ha hI0, nu]
  have hcont : IntegrableOn (fun s : ℝ => (2 * Real.pi)⁻¹ * s⁻¹) (Ioo a b) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
    exact continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => (ha.trans_le hx.1).ne')
  have hle : ∫ s in Ioo a b, killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u ≤
      ∫ s in Ioo a b, (2 * Real.pi)⁻¹ * s⁻¹ := by
    refine setIntegral_mono_on (integrableOn_killedHeat_eta ha hI0 u) hcont measurableSet_Ioo
      fun s hs => ?_
    have hs0 : 0 < s := ha.trans hs.1
    have h := (killedHeat_le_heatKernel (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u).trans
      (heatKernel_le_inv _ (NNReal.coe_nonneg _) u u)
    rw [Real.coe_toNNReal _ hs0.le, mul_inv] at h
    exact h
  have hint : ∫ s in Ioo a b, (2 * Real.pi)⁻¹ * s⁻¹ = (2 * Real.pi)⁻¹ * Real.log (b / a) := by
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha (ha.trans_le hab)]
  rw [hint] at hle
  have hpi := Real.pi_pos
  calc Real.pi * ∫ s in Ioo a b, killedHeat (openSquare ∩ Metric.ball u (etaRad s)) s.toNNReal u u
      ≤ Real.pi * ((2 * Real.pi)⁻¹ * Real.log (b / a)) := mul_le_mul_of_nonneg_left hle hpi.le
    _ = Real.log (b / a) / 2 := by field_simp

/-- **The log bound** behind DZZ l. 530, kernel form:
`π ‖K^η_δ(u) − K^η_δ(v)‖² ≤ 2152 (1 + log(1 + |u − v|/δ))`. -/
theorem pi_sq_norm_etaKernelL2_sub_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (u v : ℂ) :
    Real.pi * ‖etaKernelL2 (Ioi (δ ^ 2)) u - etaKernelL2 (Ioi (δ ^ 2)) v‖ ^ 2 ≤
      2152 * (1 + Real.log (1 + ‖u - v‖ / δ)) := by
  set D := ‖u - v‖ with hD
  have hpi := Real.pi_pos
  have hlog0 : 0 ≤ Real.log (1 + D / δ) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  -- Lemma 2.5 at scale `δ'` in kernel form
  have L25 : ∀ δ' : ℝ, 0 < δ' → Real.pi * ‖etaKernelL2 (Ioi (δ' ^ 2)) u -
      etaKernelL2 (Ioi (δ' ^ 2)) v‖ ^ 2 ≤ 1076 * D / δ' := fun δ' hδ' => by
    have h := dzz_lemma25_etaField (by norm_num) bridgeShellBound_256 hW hδ' measurableSet_Ioi
      subset_rfl u v
    simp only [etaField] at h
    rw [variance_sqrtPi_sub hW] at h
    norm_num at h
    exact h
  rcases le_or_gt D δ with hDδ | hDδ
  · refine (L25 δ hδ).trans ?_
    have : 1076 * D / δ ≤ 1076 := by rw [div_le_iff₀ hδ]; linarith
    nlinarith
  have hD0 : 0 < D := hδ.trans hDδ
  have hsplit := fun x => etaKernelL2_split (a' := δ ^ 2) (b := D) (by positivity)
    (pow_le_pow_left₀ hδ.le hDδ.le 2) x
  rw [hsplit u, hsplit v]
  set gu := etaKernelL2 (Ioi (D ^ 2)) u
  set gv := etaKernelL2 (Ioi (D ^ 2)) v
  set hu := etaKernelL2 (Ioo (δ ^ 2) (D ^ 2)) u
  set hv := etaKernelL2 (Ioo (δ ^ 2) (D ^ 2)) v
  have e : gu + hu - (gv + hv) = (gu - gv) + (hu - hv) := by abel
  rw [e]
  have n1 : ‖(gu - gv) + (hu - hv)‖ ^ 2 ≤ 2 * ‖gu - gv‖ ^ 2 + 2 * ‖hu - hv‖ ^ 2 := by
    have h := norm_add_le (gu - gv) (hu - hv)
    have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖gu - gv‖ - ‖hu - hv‖)]
  have n2 : ‖hu - hv‖ ^ 2 ≤ 2 * ‖hu‖ ^ 2 + 2 * ‖hv‖ ^ 2 := by
    have h := norm_sub_le hu hv
    have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖hu‖ - ‖hv‖)]
  have g1 := L25 D hD0
  rw [show 1076 * D / D = 1076 by field_simp] at g1
  have hb : Real.log (D ^ 2 / δ ^ 2) / 2 ≤ Real.log (1 + D / δ) := by
    rw [← div_pow, Real.log_pow]
    push_cast
    have : Real.log (D / δ) ≤ Real.log (1 + D / δ) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have h1 := pi_sq_norm_etaKernelL2_Ioo_le (by positivity : 0 < δ ^ 2)
    (pow_le_pow_left₀ hδ.le hDδ.le 2) u
  have h2 := pi_sq_norm_etaKernelL2_Ioo_le (by positivity : 0 < δ ^ 2)
    (pow_le_pow_left₀ hδ.le hDδ.le 2) v
  nlinarith

/-- `π ‖K^η_δ(u) − K^η_δ(v)‖² ≤ 1076 |u − v|/δ` (Lemma 2.5, kernel form). -/
lemma pi_sq_norm_etaKernelL2_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (u v : ℂ) :
    Real.pi * ‖etaKernelL2 (Ioi (δ ^ 2)) u - etaKernelL2 (Ioi (δ ^ 2)) v‖ ^ 2 ≤
      1076 * ‖u - v‖ / δ := by
  have h := dzz_lemma25_etaField (by norm_num) bridgeShellBound_256 hW hδ measurableSet_Ioi
    subset_rfl u v
  simp only [etaField] at h
  rw [variance_sqrtPi_sub hW] at h
  norm_num at h
  exact h

/-- Continuous versions of `η_δ` exist. -/
theorem exists_continuous_etaInf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, Y x =ᵐ[P] etaInf W δ x := by
  have hpi := Real.pi_pos
  obtain ⟨Y, hYc, hYm, hY⟩ := exists_continuous_modification_of_kernel_half hW
    (etaKernelL2 (Ioi (δ ^ 2))) (K := 1076 / (Real.pi * δ)) (by positivity)
    (fun x x' => by
      have h := pi_sq_norm_etaKernelL2_sub_le hW hδ x x'
      have h' := (le_div_iff₀ hδ).mp h
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith) (Real.sqrt Real.pi)
  exact ⟨Y, hYc, hYm, hY⟩

universe u

/-- **DZZ Lemma 2.6, first inequality** (l. 520): for continuous versions `Y` of `η_δ`, uniformly
in `δ > 0`, `k ≥ 1`, `a ≥ 0` and `u ∈ 𝕍`,
`P(max_{v ∈ 𝕍, |v − u| ≤ kδ} |η_δ(v) − η_δ(u)| ≥ a log(k + 1)) ≤ C e^{−a²/C}`. -/
theorem dzz_lemma26_eta :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ δ : ℝ, 0 < δ → ∀ Y : ℂ → Ω → ℝ,
      (∀ ω, Continuous fun x => Y x ω) → (∀ x, Y x =ᵐ[P] etaInf W δ x) →
      ∀ u ∈ ferniqueBox 0 1, ∀ k : ℕ, 1 ≤ k → ∀ a : ℝ, 0 ≤ a →
        P.real {ω | ∃ v ∈ ferniqueBox 0 1, ‖v - u‖ ≤ k * δ ∧
          a * Real.log (k + 1) ≤ |Y v ω - Y u ω|} ≤ C * Real.exp (-a ^ 2 / C) := by
  obtain ⟨C, hC0, hC⟩ := dzz_lemma26_core.{u} (K := 2152) (by norm_num)
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW δ hδ Y hYc hY u _ k hk a ha => ?_⟩
  have := hW.isProbabilityMeasure
  have hYs : ∀ x, Y x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (etaKernelL2 (Ioi (δ ^ 2)) x) ω :=
    hY
  have hsq : ∀ u v, ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P =
      Real.pi * ‖etaKernelL2 (Ioi (δ ^ 2)) u - etaKernelL2 (Ioi (δ ^ 2)) v‖ ^ 2 := by
    intro u v
    have hae : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P] fun ω =>
        (Real.sqrt Real.pi * W (etaKernelL2 (Ioi (δ ^ 2)) u) ω -
          Real.sqrt Real.pi * W (etaKernelL2 (Ioi (δ ^ 2)) v) ω) ^ 2 := by
      filter_upwards [hYs u, hYs v] with ω h1 h2; rw [h1, h2]; ring
    rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
  have h := hC Ω P Y δ hδ
    ((isGaussianProcess_sqrtPi hW (etaKernelL2 (Ioi (δ ^ 2)))).congr fun x => (hYs x).symm)
    (fun v => by rw [integral_congr_ae (hYs v)]; exact integral_sqrtPi hW _) hYc
    (fun u v => by
      rw [hsq]
      refine (pi_sq_norm_etaKernelL2_sub_le hW hδ u v).trans ?_
      have : 0 ≤ ‖u - v‖ / δ := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      nlinarith)
    (fun u v => by rw [hsq]; exact pi_sq_norm_etaKernelL2_sub_log hW hδ u v) u k hk a ha
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) h
  obtain ⟨v, -, hv⟩ := hω
  exact ⟨v, hv⟩

end DZZ
end LQGMetric
