/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent6Mom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Aux
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Main
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2GFF
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg2All
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg3Fin

/-!
# DZZ (eq-LQG-positive-moment) for `1 < p < 4/γ²` and (eq-LQG-negative-moment) (P2-GMCID6)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 684–688): for `B ⊆ 𝕍` a square or ball of
diameter `ξ` and `δ ≤ ξ`, `E (ξ^{-2} M̃_{γ,δ}(B))^p ≤ C_{γ,p}` for `0 < p < 4/γ²`
(eq-LQG-positive-moment) and for `p < 0` (eq-LQG-negative-moment). Here `δ = 2^{-m}`:

* **`lintegral_tildeM_rpow_le_of_one_lt`** : `1 < p < 4/γ²`, `U ⊆ 𝕍` open inside a closed ball
  of radius `ξ` (the range `0 < p ≤ 1` is `GMCIdent5.lintegral_tildeM_rpow_le`);
* **`lintegral_tildeM_rpow_le_of_neg`** : `p < 0`, `U ⊆ 𝕍` open containing an open ball of
  radius `ξ`.

Route (Kahane's comparison, Rhodes–Vargas arXiv:1305.6221 Thm 2.11/2.12, Berestycki–Powell
arXiv:2404.16642 Thm 3.23, `T:negmom`): the band density `f_n` is compared, on the square
`a + L[0,1)²` (side `L ≍ ξ`), with the `γ²`-log-correlated reference family
`DGMC.midZ` of a zero-boundary GFF (`lintegral_square_rpow_le`; only the upper bound on the
band covariance is used), whose moments are bounded uniformly
(`LogCorr.exists_uniform_moment`, `LogCorr.exists_uniform_neg_moment`). Then Fatou along the
band approximations `∫ g f_{n+m} dz → ∫ g dM̃` (`ae_tendsto_fineInt`), with `g = cutRamp U k ↑ 1_U`
(positive moments, then `k → ∞`) or `g` a plateau function `1_{B(x, 3ξ/8)} ≤ g ≤ 1_{B(x, ξ)}`
(negative moments), as in `GMCIdent5.lintegral_tildeM_le` and `Neg3`
(`lintegral_qAreaMeasureOn_ball_rpow_lt_top_of_neg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent6

open WhiteNoise DGMC GMCIdent GMCIdent4 GMCIdent5

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

lemma re_affine (a : ℂ) (L : ℝ) (y : ℂ) : (a + (L : ℂ) * y).re = a.re + L * y.re := by simp

lemma im_affine (a : ℂ) (L : ℝ) (y : ℂ) : (a + (L : ℂ) * y).im = a.im + L * y.im := by simp

/-- the square `x − (2ξ, 2ξ) + 4ξ[0,1)²` contains `B̄(x, ξ)` -/
lemma mem_cell0_of_norm_le {x y : ℂ} {ξ : ℝ} (hξ : 0 < ξ)
    (h : ‖x - ⟨2 * ξ, 2 * ξ⟩ + ((4 * ξ : ℝ) : ℂ) * y - x‖ ≤ ξ) : y ∈ cell0 := by
  have h1 := (Complex.abs_re_le_norm _).trans h
  have h2 := (Complex.abs_im_le_norm _).trans h
  simp only [Complex.sub_re, Complex.sub_im, re_affine, im_affine] at h1 h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- the square `x − (ρ/2, ρ/2) + ρ[0,1)²` lies in `B̄(x, ρ)` -/
lemma norm_le_of_mem_cell0 {x y : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hy : y ∈ cell0) :
    ‖x - ⟨ρ / 2, ρ / 2⟩ + (ρ : ℂ) * y - x‖ ≤ ρ := by
  obtain ⟨y1, y2, y3, y4⟩ := hy
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, re_affine, im_affine]
  have e1 : |x.re - ρ / 2 + ρ * y.re - x.re| ≤ ρ / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have e2 : |x.im - ρ / 2 + ρ * y.im - x.im| ≤ ρ / 2 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  linarith

attribute [local irreducible] fineDens in
lemma measurable_sqInt (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) (a : ℂ) (L : ℝ) :
    Measurable fun ω => ∫⁻ y in cell0, ENNReal.ofReal (fineDens W γ m n (a + (L : ℂ) * y) ω) := by
  have hf : Measurable fun q : Ω' × ℂ =>
      ENNReal.ofReal (fineDens W γ m n (a + (L : ℂ) * q.2) q.1) :=
    ENNReal.measurable_ofReal.comp ((measurable_fineDens' hW γ m n).comp
      ((measurable_const.add (measurable_const.mul measurable_snd)).prodMk measurable_fst))
  exact hf.lintegral_prod_right'

attribute [local irreducible] fineDens in
lemma fineDens_meas_z (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) (ω : Ω') :
    Measurable fun z => ENNReal.ofReal (fineDens W γ m n z ω) :=
  ENNReal.measurable_ofReal.comp ((measurable_fineDens' hW γ m n).comp
    (measurable_id.prodMk measurable_const))

lemma ofReal_sq_eq {ξ : ℝ} (hξ : 0 < ξ) (κ : ℝ) (_hκ : 0 ≤ κ) :
    (ENNReal.ofReal ξ ^ 2)⁻¹ * ENNReal.ofReal ((κ * ξ) ^ 2) = ENNReal.ofReal (κ ^ 2) := by
  have h0 : ENNReal.ofReal ξ ^ 2 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hξ).ne'
  have ht : ENNReal.ofReal ξ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hξ.le, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, mul_one]

lemma mul_rpow_of_pos_ne_top {κ : ℝ≥0∞} (h0 : κ ≠ 0) (ht : κ ≠ ⊤) (y : ℝ≥0∞) (p : ℝ) :
    (κ * y) ^ p = κ ^ p * y ^ p := by
  rw [ENNReal.mul_rpow_eq_ite]
  simp [h0, ht]

/-- **DZZ (eq-LQG-positive-moment) for `1 < p < 4/γ²`** -/
theorem lintegral_tildeM_rpow_le_of_one_lt (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {p : ℝ} (hp1 : 1 < p) (hp : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (m : ℕ) (x : ℂ) (ξ : ℝ) (U : Set ℂ), IsOpen U → U ⊆ openSquare →
      U ⊆ closedBall x ξ → (2 : ℝ)⁻¹ ^ m ≤ ξ →
      ∫⁻ ω, ((ENNReal.ofReal ξ ^ 2)⁻¹ * tildeM hW γ m ω U) ^ p ∂P' ≤ C := by
  obtain ⟨Ω₀, _, P₀, X, _, hX⟩ := exists_zeroGFF_openSquare
  obtain ⟨c, hZ⟩ := logCorr_midZ hX γ
  obtain ⟨C₀, hC₀⟩ := hZ.exists_uniform_moment (by positivity) hp1 hp
  set B := ENNReal.ofReal (Real.exp (p * (p - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀)
  have hκ0 : ENNReal.ofReal ((4 : ℝ) ^ 2) ≠ 0 := by simp
  have hκt : ENNReal.ofReal ((4 : ℝ) ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨ENNReal.ofReal ((4 : ℝ) ^ 2) ^ p * B, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) hκt) ENNReal.ofReal_ne_top,
    fun m x ξ U hU hUV hUB hξ => ?_⟩
  have hP := hW.isProbabilityMeasure
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
  set a : ℂ := x - ⟨2 * ξ, 2 * ξ⟩
  set L : ℝ := 4 * ξ
  have hL : 0 < L := by positivity
  have hδL : (2 : ℝ)⁻¹ ^ m ≤ 4 * L := by simp only [L]; linarith
  have hUQ : ∀ y, a + (L : ℂ) * y ∈ U → y ∈ cell0 := fun y hy =>
    mem_cell0_of_norm_le hξ0 (by rw [← dist_eq_norm]; exact hUB hy)
  set S : ℕ → Ω' → ℝ≥0∞ := fun n ω =>
    ∫⁻ y in cell0, ENNReal.ofReal (fineDens W γ m n (a + (L : ℂ) * y) ω)
  set c₀ : ℝ≥0∞ := (ENNReal.ofReal ξ ^ 2)⁻¹
  have hc0 : c₀ ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hξ0).ne')
  have hc16 : c₀ * ENNReal.ofReal (L ^ 2) = ENNReal.ofReal ((4 : ℝ) ^ 2) :=
    ofReal_sq_eq hξ0 4 (by norm_num)
  have hfi : ∀ k n ω, ENNReal.ofReal (fineInt W γ m n (cutRamp U k) ω) ≤
      ENNReal.ofReal (L ^ 2) * S n ω := by
    intro k n ω
    calc ENNReal.ofReal (fineInt W γ m n (cutRamp U k) ω)
        ≤ ∫⁻ z, ENNReal.ofReal (cutRamp U k z * fineDens W γ m n z ω) :=
          ofReal_integral_le_lintegral fun z =>
            mul_nonneg (cutRamp_nonneg U k z) (fineDens_nonneg γ m n z ω)
      _ ≤ ∫⁻ z in U, ENNReal.ofReal (fineDens W γ m n z ω) := by
          rw [← lintegral_indicator hU.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ U
          · rw [indicator_of_mem hz]
            exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (fineDens_nonneg γ m n z ω)
              (cutRamp_le_one U k z))
          · rw [indicator_of_notMem hz, cutRamp, FinArea.ramp_eq_zero k hz, zero_mul, zero_mul,
              ENNReal.ofReal_zero]
      _ ≤ _ := setLIntegral_le_square _ (fineDens_meas_z hW γ m n ω) hU.measurableSet a hL hUQ
  set A : ℕ → Ω' → ℝ≥0∞ := fun k ω => ∫⁻ z, ENNReal.ofReal (cutRamp U k z) ∂(tildeM hW γ m ω)
  have hsup : ∀ ω, tildeM hW γ m ω U = ⨆ k, A k ω := by
    intro ω
    rw [← lintegral_indicator_one hU.measurableSet, ← lintegral_iSup
      (f := fun n z => ENNReal.ofReal (cutRamp U n z))
      (fun n => ENNReal.measurable_ofReal.comp (continuous_cutRamp U n).measurable)
      (fun i j h z => ENNReal.ofReal_le_ofReal (cutRamp_mono U z h))]
    exact lintegral_congr fun z => (iSup_cutRamp hU hUV z).symm
  have hv := ae_isVagueLimitOn_bandMeas' hW hγ hγ2 m
  have hreal : ∀ k, A k =ᵐ[P'] fun ω =>
      ENNReal.ofReal (∫ z, cutRamp U k z ∂(tildeM hW γ m ω)) := by
    intro k
    filter_upwards [hv] with ω h
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_of_le_one h.2.1
      (continuous_cutRamp U k) (hasCompactSupport_cutRamp U k) (tsupport_cutRamp U k) fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cutRamp_nonneg U k z)]; exact cutRamp_le_one U k z)
      (Eventually.of_forall (cutRamp_nonneg U k))).symm
  have hAm : ∀ k, AEMeasurable (A k) P' := by
    intro k
    obtain ⟨Y, hYm, hY⟩ := exists_fine_version_integral_tildeM' hW hγ hγ2 m
      (continuous_cutRamp U k) (hasCompactSupport_cutRamp U k) (tsupport_cutRamp U k)
    exact ((hYm.mono (wnSigma_le hW _) le_rfl).ennreal_ofReal.aemeasurable).congr
      ((hY.fun_comp ENNReal.ofReal).trans (hreal k).symm)
  have hcont : Continuous fun y : ℝ≥0∞ => (c₀ * y) ^ p :=
    ENNReal.continuous_rpow_const.comp (ENNReal.continuous_const_mul hc0)
  have hk : ∀ k, ∫⁻ ω, (c₀ * A k ω) ^ p ∂P' ≤ ENNReal.ofReal ((4 : ℝ) ^ 2) ^ p * B := by
    intro k
    have hlim : ∀ᵐ ω ∂P', (c₀ * A k ω) ^ p ≤
        liminf (fun n => (ENNReal.ofReal ((4 : ℝ) ^ 2) * S (n + m) ω) ^ p) atTop := by
      filter_upwards [hreal k, ae_tendsto_fineInt hW hγ hγ2 m (continuous_cutRamp U k)
        (hasCompactSupport_cutRamp U k) (tsupport_cutRamp U k)] with ω hr ht
      have ht' := (hcont.tendsto _).comp ((ENNReal.continuous_ofReal.tendsto _).comp ht)
      rw [hr, ← ht'.liminf_eq]
      refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
      simp only [Function.comp]
      rw [← hc16, mul_assoc]
      exact ENNReal.rpow_le_rpow (by gcongr; exact hfi k (n + m) ω) (by linarith)
    calc ∫⁻ ω, (c₀ * A k ω) ^ p ∂P'
        ≤ ∫⁻ ω, liminf (fun n => (ENNReal.ofReal ((4 : ℝ) ^ 2) * S (n + m) ω) ^ p) atTop ∂P' :=
          lintegral_mono_ae hlim
      _ ≤ liminf (fun n => ∫⁻ ω, (ENNReal.ofReal ((4 : ℝ) ^ 2) * S (n + m) ω) ^ p ∂P') atTop :=
          lintegral_liminf_le fun n => ((measurable_sqInt hW γ m _ a L).const_mul _).pow_const _
      _ ≤ _ := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          simp_rw [mul_rpow_of_pos_ne_top hκ0 hκt]
          rw [lintegral_const_mul _ ((measurable_sqInt hW γ m _ a L).pow_const _)]
          gcongr
          exact lintegral_square_rpow_le hW γ hZ (Or.inr hp1)
            (fun j => hC₀ j j le_rfl) (Nat.le_add_left m n) a hL hδL
  have hlimk : ∀ ω, (c₀ * tildeM hW γ m ω U) ^ p = liminf (fun k => (c₀ * A k ω) ^ p) atTop := by
    intro ω
    have hmono : Monotone fun k => A k ω := fun i j h =>
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (cutRamp_mono U z h)
    rw [hsup ω]
    exact (((hcont.tendsto _).comp (tendsto_atTop_iSup hmono)).liminf_eq).symm
  calc ∫⁻ ω, (c₀ * tildeM hW γ m ω U) ^ p ∂P'
      = ∫⁻ ω, liminf (fun k => (c₀ * A k ω) ^ p) atTop ∂P' := lintegral_congr hlimk
    _ ≤ liminf (fun k => ∫⁻ ω, (c₀ * A k ω) ^ p ∂P') atTop :=
        lintegral_liminf_le' fun k => ((hAm k).const_mul _).pow_const _
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hk)

end GMCIdent6
end LQGMetric
