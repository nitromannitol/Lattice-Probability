/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105U1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Mom
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuHat
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Exp
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.8, upper half: the coarse × fine split of `μ_{h^𝕍}(B(w,s))` (D105, packet P2)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.8 (DG:1112–1150), upper
half: DG:1124–1137 use `E μ_h(B_δ(z))^p ≤ δ^{f(p)+o(1)}`, `f(p) = (2+γ²/2)p − γ²p²/2`, then a union
bound. We follow the DZZ scheme (arXiv:1807.00422, (eq-def-tilde-M) and (eq-LQG-positive-moment),
l. 676–688) for the white-noise zero-boundary GFF `h^𝕍` on `𝕍`, at a dyadic scale `δ = 2^{-m}`
with `s ≤ δ ≤ 2s`:

`μ(dz) = CR(z)^{γ²/2} e^{γ h̃_δ(z) − γ²/2 Var h̃_δ(z)} M̃_{γ,δ}(dz)` (`qArea_eq_withDensity_tildeM`),
`M̃_{γ,δ}` independent of `h̃_δ` (`indep_wnSigma_compl`, fine version of `M̃(U)`:
`exists_fine_tildeM_open`), `E (ξ^{-2} M̃(U))^p ≤ C` (`lintegral_tildeM_rpow_le_of_one_lt`).

This file: the fine-measurable version of `M̃(U)` and the product formula
`E (e^{γ h̃_δ(w)} M̃(U))^p = e^{p²γ² Var h̃_δ(w)/2} E M̃(U)^p` (`lintegral_coarse_mul_tildeM`), and
the variance bookkeeping `Var h̃_δ ≤ log δ⁻¹ + c`, `|Var h̃_δ(z) − Var h̃_δ(w)| ≤ c √(log δ⁻¹)`
for `|z − w| ≤ 2δ` (from `dzz_var_compare`, `etaVar_le`, DZZ Lemma 2.5), the pathwise bound
`muHU_ball_le`, the exponent arithmetic `upper_expo_aux`, and the grid union bound
`prob_grid_event_le` (DG:1131–1137; the scheme of `DZZ.prob_grid_light_le` for any events).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace DG

open WhiteNoise DZZ GMCIdent GMCIdent4 GMCIdent5 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`M̃_{γ,δ}(U)` has a fine-measurable version** (`U ⊆ 𝕍` open; monotone limit of
`∫ cutRamp U k dM̃`, each with a fine version, `exists_fine_version_integral_tildeM'`) -/
theorem exists_fine_tildeM_open (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (m : ℕ) {U : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ openSquare) :
    ∃ F : Ω → ℝ≥0∞, Measurable[wnSigma W (coarseSet m)ᶜ] F ∧
      (fun ω => tildeM hW γ m ω U) =ᵐ[P] F := by
  choose Y hYm hY using fun k => exists_fine_version_integral_tildeM' hW hγ hγ2 m
    (continuous_cutRamp U k) (hasCompactSupport_cutRamp U k) (tsupport_cutRamp U k)
  refine ⟨fun ω => ⨆ k, ENNReal.ofReal (Y k ω), ?_, ?_⟩
  · let _ : MeasurableSpace Ω := wnSigma W (coarseSet m)ᶜ
    exact Measurable.iSup fun k => (hYm k).ennreal_ofReal
  · filter_upwards [ae_isVagueLimitOn_bandMeas' hW hγ hγ2 m, ae_all_iff.2 hY] with ω h hk
    rw [← lintegral_indicator_one hU.measurableSet]
    have e : U.indicator (1 : ℂ → ℝ≥0∞) = fun z => ⨆ n, ENNReal.ofReal (cutRamp U n z) :=
      funext fun z => (iSup_cutRamp hU hUV z).symm
    rw [e, lintegral_iSup (f := fun n z => ENNReal.ofReal (cutRamp U n z))
      (fun n => ENNReal.measurable_ofReal.comp (continuous_cutRamp U n).measurable)
      (fun i j hij z => ENNReal.ofReal_le_ofReal (cutRamp_mono U z hij))]
    congr 1; funext k
    rw [hk k]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_of_le_one h.2.1
      (continuous_cutRamp U k) (hasCompactSupport_cutRamp U k) (tsupport_cutRamp U k) fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cutRamp_nonneg U k z)]; exact cutRamp_le_one U k z)
      (Eventually.of_forall (cutRamp_nonneg U k))).symm

lemma aemeasurable_tildeM_open (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (m : ℕ) {U : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ openSquare) :
    AEMeasurable (fun ω => tildeM hW γ m ω U) P := by
  obtain ⟨F, hFm, hF⟩ := exists_fine_tildeM_open hW hγ hγ2 m hU hUV
  exact (hFm.mono (wnSigma_le hW _) le_rfl).aemeasurable.congr hF.symm

omit [MeasurableSpace Ω] in
/-- `h̃_δ(z)` is measurable for the coarse σ-algebra `𝓖_m` -/
lemma measurable_tildeHInf_coarse (m : ℕ) (z : ℂ) :
    Measurable[wnSigma W (coarseSet m)] (tildeHInf W ((2 : ℝ)⁻¹ ^ m) z) :=
  (measurable_wnSigma (supportedIn_wndKernelL2 openSquare measurableSet_Ioi z)).const_mul _

/-- **coarse × fine**: `E (e^{γ h̃_δ(w)} M̃_{γ,δ}(U))^p = e^{p²γ² Var h̃_δ(w)/2} E M̃_{γ,δ}(U)^p`
(independence of `M̃_{γ,δ}` and `h̃_δ`, DZZ l. 676–683) -/
theorem lintegral_coarse_mul_tildeM (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (m : ℕ) {U : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ openSquare) (w : ℂ) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, (ENNReal.ofReal (Real.exp (γ * coarseVer hW m w ω)) * tildeM hW γ m ω U) ^ p ∂P =
      ENNReal.ofReal (Real.exp (p ^ 2 * γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ m) w)) *
        ∫⁻ ω, tildeM hW γ m ω U ^ p ∂P := by
  have := hW.isProbabilityMeasure
  obtain ⟨F, hFm, hF⟩ := exists_fine_tildeM_open hW hγ hγ2 m hU hUV
  set K := wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ m) ^ 2)) w
  set g : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (p * γ * tildeHInf W ((2 : ℝ)⁻¹ ^ m) w ω))
  have hgm : Measurable[wnSigma W (coarseSet m)] g := by
    let _ : MeasurableSpace Ω := wnSigma W (coarseSet m)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_tildeHInf_coarse m w).const_mul _))
  have hae : (fun ω => (ENNReal.ofReal (Real.exp (γ * coarseVer hW m w ω)) *
      tildeM hW γ m ω U) ^ p) =ᵐ[P] fun ω => g ω * F ω ^ p := by
    filter_upwards [(coarseVer_spec hW m).2.2 w, hF] with ω h1 h2
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp, h1, ← h2, ENNReal.ofReal_rpow_of_nonneg
      (Real.exp_pos _).le hp, ← Real.exp_mul]
    congr 3; ring
  rw [lintegral_congr_ae hae, lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (wnSigma_le hW _) (wnSigma_le hW _) (indep_wnSigma_compl hW (coarseSet m)).symm hgm
    (by let _ : MeasurableSpace Ω := wnSigma W (coarseSet m)ᶜ; exact hFm.pow_const p)]
  congr 1
  · have hexp : ∀ ω, Real.exp (p * γ * tildeHInf W ((2 : ℝ)⁻¹ ^ m) w ω) =
        Real.exp ((p * γ * Real.sqrt Real.pi) * W K ω) := by
      intro ω; simp only [tildeHInf, DZZ.wnField, K]; ring_nf
    simp only [g]
    simp_rw [hexp]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_wn hW _ K)
      (Eventually.of_forall fun ω => (Real.exp_pos _).le), integral_exp_wn hW]
    congr 2
    simp only [tildeVar, K]
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
  · exact lintegral_congr_ae (hF.mono fun ω h => by simp only at h ⊢; rw [← h])

/-! ## Variance bookkeeping and the pathwise coarse bound -/

/-- `Var h̃_δ(v) ≤ log δ⁻¹ + c₀`, `δ = 2^{-m}` (`dzz_var_compare` and `etaVar_le`) -/
lemma exists_tildeVar_le : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (m : ℕ) (v : ℂ),
    tildeVar ((2 : ℝ)⁻¹ ^ m) v ≤ Real.log (((2 : ℝ)⁻¹ ^ m)⁻¹) + c₀ := by
  obtain ⟨b₁, hb0, hb⟩ := dzz_var_compare
  refine ⟨4 + b₁, by linarith, fun m v => ?_⟩
  have h := hb m v
  rw [one_div] at h
  have h2 := etaVar_le (ε := (2 : ℝ)⁻¹ ^ m) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) v
  have := (abs_le.1 h).2
  linarith

/-- `Var h̃_δ(v) − Var h̃_δ(w) ≤ 2 √(28 |v − w|/δ) √B` if `Var h̃_δ ≤ B` (DZZ Lemma 2.5, kernel
form, and `‖a‖² − ‖b‖² ≤ ‖a − b‖ (‖a‖ + ‖b‖)`; as `etaVar_sub_le`) -/
lemma tildeVar_sub_le (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {B : ℝ}
    (hB : ∀ v, tildeVar δ v ≤ B) (v w : ℂ) :
    tildeVar δ v - tildeVar δ w ≤ 2 * Real.sqrt (28 * ‖v - w‖ / δ) * Real.sqrt B := by
  set a := wndKernelL2 openSquare (Ioi (δ ^ 2)) v
  set b := wndKernelL2 openSquare (Ioi (δ ^ 2)) w
  have hpi := Real.pi_pos
  set r := Real.sqrt Real.pi
  have hr : r ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hD := pi_sq_norm_tildeHKernel_sub_le hW hδ v w
  have hVa := hB v
  have hVb := hB w
  unfold tildeVar at hVa hVb ⊢
  have hx : r * ‖a - b‖ ≤ Real.sqrt (28 * ‖v - w‖ / δ) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [mul_pow, hr]; exact hD))
  have hy : r * ‖a‖ ≤ Real.sqrt B :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [mul_pow, hr]; exact hVa))
  have hz : r * ‖b‖ ≤ Real.sqrt B :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [mul_pow, hr]; exact hVb))
  have hab : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := norm_sub_norm_le a b
  have e : Real.pi * ‖a‖ ^ 2 - Real.pi * ‖b‖ ^ 2 =
      (r * (‖a‖ - ‖b‖)) * (r * ‖a‖ + r * ‖b‖) := by rw [← hr]; ring
  rw [e]
  have h0 : 0 ≤ r * ‖a‖ + r * ‖b‖ := by positivity
  have h1 : r * (‖a‖ - ‖b‖) ≤ r * ‖a - b‖ := mul_le_mul_of_nonneg_left hab hr0
  have hs0 : 0 ≤ Real.sqrt (28 * ‖v - w‖ / δ) := Real.sqrt_nonneg _
  calc (r * (‖a‖ - ‖b‖)) * (r * ‖a‖ + r * ‖b‖)
      ≤ Real.sqrt (28 * ‖v - w‖ / δ) * (r * ‖a‖ + r * ‖b‖) :=
        mul_le_mul_of_nonneg_right (h1.trans hx) h0
    _ ≤ Real.sqrt (28 * ‖v - w‖ / δ) * (Real.sqrt B + Real.sqrt B) :=
        mul_le_mul_of_nonneg_left (add_le_add hy hz) hs0
    _ = 2 * Real.sqrt (28 * ‖v - w‖ / δ) * Real.sqrt B := by ring

/-- a dyadic scale `δ = 2^{-m}` with `s ≤ δ ≤ 2s` -/
lemma exists_dyadic_between {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    ∃ m : ℕ, s ≤ (2 : ℝ)⁻¹ ^ m ∧ (2 : ℝ)⁻¹ ^ m ≤ 2 * s := by
  classical
  have hex : ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m ≤ 2 * s := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * s by positivity)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    exact ⟨m, hm.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h0 | h1
  · rw [h0, pow_zero]; linarith
  · have hlt : ¬ (2 : ℝ)⁻¹ ^ (Nat.find hex - 1) ≤ 2 * s := Nat.find_min hex (by omega)
    push Not at hlt
    have e : (2 : ℝ)⁻¹ ^ Nat.find hex = (2 : ℝ)⁻¹ ^ (Nat.find hex - 1) * 2⁻¹ := by
      conv_lhs => rw [h1]
      rw [pow_succ]; rfl
    rw [e]; linarith

lemma openSquare_subset_ferniqueBox : openSquare ⊆ ferniqueBox 0 1 := by
  intro z ⟨h1, h2, h3, h4⟩
  simp only [ferniqueBox, Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, zero_add,
    mem_Icc]
  exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

/-- the coarse density at `z` against the coarse field at `w`:
`cDens(z) ≤ e^{γ²/2 (H + D) − γ²/2 Var h̃_δ(w) + γ T} e^{γ h̃_δ(w)}` -/
lemma cDens_le_of (hW : IsWhiteNoise P W) {γ : ℝ} (m : ℕ) (ω : Ω) {z w : ℂ} {H D T : ℝ}
    (hH : hS z z ≤ H) (hD : tildeVar ((2 : ℝ)⁻¹ ^ m) w - tildeVar ((2 : ℝ)⁻¹ ^ m) z ≤ D)
    (hT : coarseVer hW m z ω - coarseVer hW m w ω ≤ T) (hγ : 0 ≤ γ) :
    cDens hW γ m z ω ≤ Real.exp (γ ^ 2 / 2 * (H + D) - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ m) w +
      γ * T) * Real.exp (γ * coarseVer hW m w ω) := by
  unfold cDens wnWeight
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hg2 : 0 ≤ γ ^ 2 / 2 := by positivity
  have e : Real.pi * ‖wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ m) ^ 2)) z‖ ^ 2 =
      tildeVar ((2 : ℝ)⁻¹ ^ m) z := rfl
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hT hγ]

/-- **pathwise coarse × fine bound**: if `cDens ≤ c e^{γ h̃_δ(w)}` on `B(w,s)` then
`μ(B(w,s)) ≤ c · e^{γ h̃_δ(w)} M̃_{γ,δ}(B(w,s))` -/
lemma muHU_ball_le (hW : IsWhiteNoise P W) (γ : ℝ) (m : ℕ) (ω : Ω) {w : ℂ} {s c : ℝ}
    (hc0 : 0 ≤ c)
    (hc : ∀ z ∈ ball w s, cDens hW γ m z ω ≤ c * Real.exp (γ * coarseVer hW m w ω)) :
    muHU W γ ω (ball w s) ≤ ENNReal.ofReal c *
      (ENNReal.ofReal (Real.exp (γ * coarseVer hW m w ω)) * tildeM hW γ m ω (ball w s)) := by
  unfold muHU
  rw [qArea_eq_withDensity_tildeM hW γ m ω, withDensity_apply _ measurableSet_ball]
  calc ∫⁻ z in ball w s, ENNReal.ofReal (cDens hW γ m z ω) ∂tildeM hW γ m ω
      ≤ ∫⁻ z in ball w s, ENNReal.ofReal (c * Real.exp (γ * coarseVer hW m w ω))
          ∂tildeM hW γ m ω :=
        setLIntegral_mono' measurableSet_ball fun z hz => ENNReal.ofReal_le_ofReal (hc z hz)
    _ = _ := by rw [setLIntegral_const, ENNReal.ofReal_mul hc0, mul_assoc]

/-- `b √y ≤ ε y + b²/(4ε)` -/
lemma mul_sqrt_le_lin {b ε y : ℝ} (hε : 0 < ε) (hy : 0 ≤ y) :
    b * Real.sqrt y ≤ ε * y + b ^ 2 / (4 * ε) := by
  have hq : 4 * ε * (b ^ 2 / (4 * ε)) = b ^ 2 := by field_simp
  have hs := Real.sq_sqrt hy
  have key : 4 * ε * (ε * y + b ^ 2 / (4 * ε) - b * Real.sqrt y) =
      (2 * ε * Real.sqrt y - b) ^ 2 := by
    rw [mul_sub, mul_add, hq]
    nth_rewrite 1 [← hs]; ring
  have h4 : 0 < 4 * ε := by linarith
  have := (mul_nonneg_iff_of_pos_left h4).1 (key ▸ sq_nonneg _)
  linarith

/-- Markov in `ℝ≥0∞` with a real threshold: `P[a ≤ X] ≤ a^{-p} E X^p` -/
lemma meas_ofReal_le_rpow {X : Ω → ℝ≥0∞} (hX : AEMeasurable X P) {a p : ℝ} (ha : 0 < a)
    (hp : 0 < p) :
    P {ω | ENNReal.ofReal a ≤ X ω} ≤ ENNReal.ofReal (a ^ (-p)) * ∫⁻ ω, X ω ^ p ∂P := by
  have hsub : {ω | ENNReal.ofReal a ≤ X ω} ⊆ {ω | ENNReal.ofReal (a ^ p) ≤ X ω ^ p} :=
    fun ω h => by
      rw [mem_ofPred_eq, ← ENNReal.ofReal_rpow_of_pos ha]
      exact ENNReal.rpow_le_rpow h hp.le
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div (hX.pow_const p)
    (by simpa using Real.rpow_pos_of_pos ha p) ENNReal.ofReal_ne_top).trans (le_of_eq ?_))
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ha p),
    Real.rpow_neg ha.le]

/-- the exponent bookkeeping of `muHU_ball_upper_tail` (plain real arithmetic) -/
lemma upper_expo_aux {p γ η H c₀ L ℓ V D T ε₁ ε₂ b₁ b₂ cF : ℝ} (hp1 : 1 < p) (hγ : 0 < γ)
    (hη : 0 < η) (hLℓ : L ≤ ℓ) (hV : V ≤ L + c₀) (hD : D ≤ ε₁ * (L + c₀) + b₁ ^ 2 / (4 * ε₁))
    (hT : T ≤ 2 * (ε₂ * L + b₂ ^ 2 / (4 * ε₂) + cF + ε₂ * L))
    (i1 : p * γ ^ 2 / 2 * ε₁ = η / 3) (i2 : p * γ * 2 * ε₂ = η / 3) :
    p * (γ ^ 2 / 2 * (H + D) - γ ^ 2 / 2 * V + γ * T) + p ^ 2 * γ ^ 2 / 2 * V +
        (Real.log 2 - ℓ) * (2 * p) ≤
      ((p ^ 2 - p) * γ ^ 2 / 2 * c₀ + p * γ ^ 2 / 2 * (H + ε₁ * c₀ + b₁ ^ 2 / (4 * ε₁)) +
        p * γ * 2 * (b₂ ^ 2 / (4 * ε₂) + cF) + 2 * p * Real.log 2) +
        -ℓ * ((2 + γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2 - η) := by
  have hpγ : 0 ≤ p * γ ^ 2 / 2 := by positivity
  have hpγ' : 0 ≤ p * γ := by nlinarith
  have hq : 0 ≤ (p ^ 2 - p) * γ ^ 2 / 2 := by
    have : 0 ≤ p ^ 2 - p := by nlinarith
    positivity
  have hVt := mul_le_mul_of_nonneg_left hV hq
  have hD' := mul_le_mul_of_nonneg_left hD hpγ
  have hT' := mul_le_mul_of_nonneg_left hT hpγ'
  have hLl := mul_le_mul_of_nonneg_left hLℓ (add_nonneg hq hη.le)
  have i1L : p * γ ^ 2 / 2 * ε₁ * L = η / 3 * L := by rw [i1]
  have i2L : p * γ * 2 * ε₂ * L = η / 3 * L := by rw [i2]
  linarith

/-! ## Union bound over the grid (DG:1131–1137) -/

/-- **union bound over the grid** `gℤ²` near `u`, for any family of events -/
theorem prob_grid_event_le {E : ℂ → Set Ω} {u : ℂ} {R g A : ℝ} (hR : 0 ≤ R) (hg : 0 < g)
    (hE : ∀ w ∈ closedBall u (R + 3 * g), P (E w) ≤ ENNReal.ofReal A) :
    P {ω | ∃ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ R + 3 * g ∧ ω ∈ E ⟨i * g, j * g⟩} ≤
      ENNReal.ofReal ((2 * ⌈(‖u‖ + (R + 3 * g)) / g⌉ + 1) ^ 2 * A) := by
  set M := ⌈(‖u‖ + (R + 3 * g)) / g⌉
  set F : Finset (ℤ × ℤ) := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M
  set E' : ℤ × ℤ → Set Ω := fun q => if ‖(⟨q.1 * g, q.2 * g⟩ : ℂ) - u‖ ≤ R + 3 * g then
    E ⟨q.1 * g, q.2 * g⟩ else ∅
  have hsub : {ω | ∃ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ R + 3 * g ∧
      ω ∈ E ⟨i * g, j * g⟩} ⊆ ⋃ q ∈ F, E' q := by
    rintro ω ⟨i, j, hd, hm⟩
    obtain ⟨hi, hj⟩ := grid_index_le hg hd
    refine mem_biUnion (x := (i, j)) ?_ ?_
    · simp only [F, Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
      exact ⟨abs_le.1 hi, abs_le.1 hj⟩
    · simp only [E', hd, ite_true]; exact hm
  have hE' : ∀ q ∈ F, P (E' q) ≤ ENNReal.ofReal A := by
    intro q _
    simp only [E']
    split_ifs with hd
    · exact hE _ (by rw [mem_closedBall, dist_eq_norm]; exact hd)
    · simp
  have hcard : (F.card : ℝ) = (2 * M + 1) ^ 2 := by
    have hM : 0 ≤ M := by
      apply Int.ceil_nonneg; exact div_nonneg (by linarith [norm_nonneg u]) hg.le
    simp only [F, Finset.card_product, Int.card_Icc]
    have h0 : 0 ≤ M + 1 - -M := by omega
    have h := Int.toNat_of_nonneg h0
    have h2 : ((((M + 1 - -M).toNat : ℕ) : ℤ) : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by rw [h]
    have h3 : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by
      push_cast at h2; rw [h2]; ring
    rw [Nat.cast_mul, h3]; ring
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le F E').trans ?_)
  refine (Finset.sum_le_sum hE').trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← hcard]
  by_cases hA : 0 ≤ A
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  · push Not at hA
    rw [ENNReal.ofReal_of_nonpos hA.le, mul_zero]; exact zero_le

/-- rpow bookkeeping: `c₀²/(ε^β)² · (C ε^{−q} (2ε^β)^e) = c₀² C 2^e ε^{β(e−2) − q}` -/
lemma upper_rpow_alg {ε β q e c₀ C : ℝ} (hε : 0 < ε) :
    c₀ ^ 2 / (ε ^ β) ^ 2 * (C * ε ^ (-q) * (2 * ε ^ β) ^ e) =
      c₀ ^ 2 * C * 2 ^ e * ε ^ (β * (e - 2) - q) := by
  have h1 : (2 * ε ^ β) ^ e = 2 ^ e * ε ^ (β * e) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
  have h2 : (ε ^ β) ^ 2 = ε ^ (β * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  have h3 : ε ^ (β * (e - 2) - q) = ε ^ (β * e) * ε ^ (-q) / ε ^ (β * 2) := by
    rw [show β * (e - 2) - q = β * e + -q - β * 2 by ring, Real.rpow_sub hε, Real.rpow_add hε]
  have h4 : 0 < ε ^ (β * 2) := Real.rpow_pos_of_pos hε _
  rw [h1, h2, h3]
  field_simp

end DG
end LQGMetric
