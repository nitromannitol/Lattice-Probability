/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D125A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117C

/-!
# D125 packet P-125 (A): the coarse band on a small box, one-sided variance comparison
(P2-DZZ125)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 2537–2545: the coarse band `ĥ^{s_i}_{a⁻¹}` has
variance `O(1) log δ⁻¹` and, on the `O(a²)` cells of the image box, sup `≤ 2 (log δ⁻¹)^{0.9}`
whp. Quantitative form (decision D125, DEC-125 §4 A, B):

* `simMap_image_ferniqueBox_subset`: `θ(𝕍^ξ-box)` lies in an axis box of side `3‖a‖`;
* `dzz_hat_sup_tail_raw`: the proof of `dzz_hat_sup_tail_le` (S5D117A, copied from S2HatTail)
  stopped at the Borell–TIS output `2 e^{M²/(2σ²)} e^{−λ²/(4σ²)}`;
* `dzz_hat_sup_tail_small`: on a box of side `3a`, `a = 2^{−m}`:
  `P(sup |ĥ^1_a| ≥ λ) ≤ 2 e^{18 C_F²} e^{−λ²/(4(m+1))}` (constant independent of `m`);
* `tildeVar_scale_ge`: `Var h̃_{2^{-n}}(z) − Var h̃_{r 2^{-n}}(w) ≤ B` on the `ξ`-box, `r ≤ 1`
  (`tildeVar_sub_etaVar_le`, `etaVar_two_point_le` at `r = 1`, `etaVar_anti`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail WNPush

/-- the small box of side `3‖a‖` containing `θ(ferniqueBox ⟨ξ,ξ⟩ (1 − 2ξ))` -/
def simSmallBox (a b : ℂ) : Set ℂ :=
  ferniqueBox ⟨(simMap a b ⟨1 / 2, 1 / 2⟩).re - 3 * ‖a‖ / 2,
    (simMap a b ⟨1 / 2, 1 / 2⟩).im - 3 * ‖a‖ / 2⟩ (3 * ‖a‖)

lemma simMap_image_ferniqueBox_subset {ξ : ℝ} (hξ : 0 ≤ ξ) (a b : ℂ) :
    simMap a b '' ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) ⊆ simSmallBox a b := by
  rintro _ ⟨z, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
  simp only at h1 h2 h3 h4
  set p : ℂ := ⟨1 / 2, 1 / 2⟩
  have hzp : ‖z - p‖ ≤ 1 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, p]
    have e1 : |z.re - 1 / 2| ≤ 1 / 2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have e2 : |z.im - 1 / 2| ≤ 1 / 2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    linarith
  have hd : ‖simMap a b z - simMap a b p‖ ≤ ‖a‖ := by
    have : simMap a b z - simMap a b p = a * (z - p) := by simp only [simMap]; ring
    rw [this, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg a) hzp
  have hre := (Complex.abs_re_le_norm (simMap a b z - simMap a b p)).trans hd
  have him := (Complex.abs_im_le_norm (simMap a b z - simMap a b p)).trans hd
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have hre' := abs_le.1 hre
  have him' := abs_le.1 him
  have ha := norm_nonneg a
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only <;> linarith [hre'.1, hre'.2, him'.1, him'.2]

/-- `dzz_hat_sup_tail_le` (S5D117A) with the Borell–TIS output kept as it is:
`2 e^{M²/(2σ²)} e^{−λ²/(4σ²)}`, `M = (2s/a) C_F`, `σ² = log(b/a) + 1`. Proof copied. -/
theorem dzz_hat_sup_tail_raw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {x₀ : ℂ} {s : ℝ} (hs : 0 < s) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hY : ∀ x, Y x =ᵐ[P] phi W a b x) :
    ∀ lam : ℝ, 0 ≤ lam →
      P.real {ω | lam ≤ ⨆ v : ferniqueBox x₀ s, |Y v ω|} ≤
        2 * Real.exp (((a / (2 * s))⁻¹ * ferniqueCF) ^ 2 / (2 * (Real.log (b / a) + 1))) *
          Real.exp (-lam ^ 2 / (2 * (2 * (Real.log (b / a) + 1)))) := by
  intro lam hlam
  have hP := hW.isProbabilityMeasure
  set B := ferniqueBox x₀ s
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox x₀ s)
  have : Nonempty B := ⟨⟨x₀, mem_ferniqueBox_self hs.le⟩⟩
  set X : B → Ω → ℝ := fun v => Y v
  have hX : IsGaussianProcess X P :=
    (isGaussianProcess_phi_comp hW a b (fun v : B => (v : ℂ))).congr fun v => (hY v).symm
  have hint0 : ∀ x, ∫ ω, Y x ω ∂P = 0 := fun x => by
    rw [integral_congr_ae (hY x)]; exact integral_phi hW a b x
  have hincY : ∀ u v : ℂ, ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ ‖u - v‖ ^ 2 / a ^ 2 := by
    intro u v
    have hm : AEMeasurable (fun ω => phi W a b v ω - phi W a b u ω) P :=
      ((measurable_phi hW a b v).sub (measurable_phi hW a b u)).aemeasurable
    have h0 : ∫ ω, (phi W a b v ω - phi W a b u ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW a b v).integrable one_le_two)
        ((memLp_phi hW a b u).integrable one_le_two), integral_phi hW, integral_phi hW, sub_zero]
    have hae2 : (fun ω => (Y v ω - Y u ω) ^ 2) =ᵐ[P]
        fun ω => (phi W a b v ω - phi W a b u ω) ^ 2 := by
      filter_upwards [hY u, hY v] with ω h1 h2; rw [h1, h2]
    rw [integral_congr_ae hae2, ← variance_of_integral_eq_zero hm h0,
      norm_sub_rev]
    exact dzz_variance_hat_sub_le hW ha hab v u
  set c : ℝ := a / (2 * s) with hc
  have hc0 : 0 < c := by positivity
  have hincG : ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ u ∈ B, ∀ v ∈ B,
      ∫ ω, (ε * c * Y v ω - ε * c * Y u ω) ^ 2 ∂P ≤ ‖u - v‖ / s := by
    intro ε hε u hu v hv
    have e : (fun ω => (ε * c * Y v ω - ε * c * Y u ω) ^ 2) =
        fun ω => c ^ 2 * (Y v ω - Y u ω) ^ 2 := by
      funext ω; rw [← mul_sub, mul_pow, mul_pow, hε, one_mul]
    rw [e, integral_const_mul]
    have h1 := hincY u v
    have hr := norm_sub_le_of_mem_ferniqueBox hu hv
    have hr0 := norm_nonneg (u - v)
    calc c ^ 2 * ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ c ^ 2 * (‖u - v‖ ^ 2 / a ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      _ = ‖u - v‖ * ‖u - v‖ / (4 * s ^ 2) := by rw [hc]; field_simp; ring
      _ ≤ ‖u - v‖ * (2 * s) / (4 * s ^ 2) := by gcongr
      _ ≤ ‖u - v‖ / s := by
          rw [div_le_div_iff₀ (by positivity) hs]; nlinarith [mul_nonneg hr0 hs.le]
  have hsupG : ∀ (ε : ℝ), ε ^ 2 = 1 →
      Integrable (fun ω => ⨆ v : B, ε * c * Y v ω) P ∧
        ∫ ω, (⨆ v : B, ε * c * Y v ω) ∂P ≤ ferniqueCF := by
    intro ε hε
    refine dzz_lemma23_continuous hs ?_ (fun v _ => ?_) (hincG ε hε)
      (fun ω => (continuous_const.mul (hYc ω)).continuousOn)
    · exact (hX.smul fun _ => ε * c).congr fun v => Eventually.of_forall fun ω => rfl
    · rw [integral_const_mul, hint0, mul_zero]
  have hsup_eq : ∀ (ε : ℝ) ω, (⨆ v : B, ε * Y v ω) = c⁻¹ * ⨆ v : B, ε * c * Y v ω := by
    intro ε ω
    rw [Real.mul_iSup_of_nonneg (inv_nonneg.2 hc0.le)]
    congr 1; funext v; field_simp
  have hYsup : ∀ (ε : ℝ), ε ^ 2 = 1 → Integrable (fun ω => ⨆ v : B, ε * Y v ω) P ∧
      ∫ ω, (⨆ v : B, ε * Y v ω) ∂P ≤ c⁻¹ * ferniqueCF := by
    intro ε hε
    obtain ⟨h1, h2⟩ := hsupG ε hε
    simp_rw [hsup_eq ε]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc0.le)
  obtain ⟨hi1, hM1⟩ := hYsup 1 (by norm_num)
  obtain ⟨hi2, hM2⟩ := hYsup (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hi1 hM1 hi2 hM2
  have hl : 0 ≤ Real.log (b / a) :=
    Real.log_nonneg ((one_le_div ha).2 hab)
  set σ : ℝ := Real.sqrt (Real.log (b / a) + 1)
  have hσ2 : σ ^ 2 = Real.log (b / a) + 1 := Real.sq_sqrt (by linarith)
  have hvar : ∀ v : B, Var[X v; P] ≤ σ ^ 2 := by
    intro v
    rw [hσ2, variance_congr (hY v), variance_phi hW ha hab]
    linarith
  have h := tail_iSup_abs_le_gaussian hX (fun v => hint0 v) (fun ω => (hYc ω).comp
    continuous_subtype_val) hi1 hi2 hM1 hM2 hvar hlam
  rw [hσ2] at h
  exact h

/-- **The coarse band on a box of side `3a`, `a = 2^{−m}`** (DZZ l. 2537–2545 made
quantitative, DEC-125 §4 A): the constant does not depend on `m`, the variance `m + 1` sits in
the exponent. -/
theorem dzz_hat_sup_tail_small {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {m : ℕ} {a : ℝ} (ha : a = (1 / 2 : ℝ) ^ m)
    (x₀ : ℂ) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hY : ∀ x, Y x =ᵐ[P] phi W a 1 x) :
    ∀ lam : ℝ, 0 ≤ lam →
      P.real {ω | lam ≤ ⨆ v : ferniqueBox x₀ (3 * a), |Y v ω|} ≤
        2 * Real.exp (18 * ferniqueCF ^ 2) * Real.exp (-lam ^ 2 / (4 * (m + 1))) := by
  intro lam hlam
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; exact pow_le_one₀ (by norm_num) (by norm_num)
  refine (dzz_hat_sup_tail_raw hW ha0 ha1 (x₀ := x₀) (by positivity) hYc hY lam hlam).trans ?_
  have hlog : Real.log (1 / a) = m * Real.log 2 := by
    rw [ha, one_div, ← inv_pow, Real.log_pow, inv_div, div_one]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set σ2 := Real.log (1 / a) + 1 with hσ2
  have hσ1 : 1 ≤ σ2 := by rw [hσ2, hlog]; nlinarith
  have hσm : σ2 ≤ m + 1 := by rw [hσ2, hlog]; nlinarith
  have hM : (a / (2 * (3 * a)))⁻¹ * ferniqueCF = 6 * ferniqueCF := by
    field_simp; ring
  rw [hM]
  refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
  · rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ferniqueCF]
  · rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity) (by linarith)

/-- **One-sided two-point, two-scale variance comparison** (DEC-125 §4 B):
`Var h̃_{2^{-n}}(z) − Var h̃_{r2^{-n}}(w) ≤ B` for `0 < r ≤ 1` on the `ξ`-box. -/
theorem tildeVar_scale_ge {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (r : ℝ), 0 < r → r ≤ 1 → ∀ z w : ℂ,
      z ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) → w ∈ ferniqueBox ⟨ξ, ξ⟩ (1 - 2 * ξ) →
      tildeVar ((1 / 2 : ℝ) ^ n) z - tildeVar (r * (1 / 2 : ℝ) ^ n) w ≤ B := by
  obtain ⟨B₀, hB₀, h⟩ := etaVar_two_point_le hξ hξ1
  obtain ⟨b₁, hb₁, hv⟩ := tildeVar_sub_etaVar_le
  refine ⟨B₀ + b₁, by positivity, fun n r hr hr1 z w hz hw => ?_⟩
  have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have h1 := hv _ hp z
  have h2 := hv _ (mul_pos hr hp) w
  have h3 := (abs_le.1 (h n 1 one_pos le_rfl z w hz hw)).2
  rw [one_mul, inv_one, Real.log_one, add_zero] at h3
  have h4 : etaVar ((1 / 2 : ℝ) ^ n) w ≤ etaVar (r * (1 / 2 : ℝ) ^ n) w :=
    etaVar_anti (mul_pos hr hp) (mul_le_of_le_one_left hp.le hr1) w
  linarith [h1.1, h1.2, h2.1, h2.2]

end DZZ
end LQGMetric
