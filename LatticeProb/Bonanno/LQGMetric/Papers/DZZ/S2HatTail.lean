/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2HatTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Hat
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# DZZ §2.2: Gaussian tail of `sup |ĥ_a^b|` on a box (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 628–633, proof of Lemma 2.9
`lem-scaling-coupling`): "By `eq-hat-h-continuity` we see that `Var(ĥ_a^1(u) − ĥ_a^1(v)) =
O(|u − v|)` for all `u, v ∈ 𝕍^ξ` … In addition … `Var(ĥ_a^1(u)) = O(1)`. Therefore,
Lemmas 2.1 and 2.3 imply that `P(max_{u ∈ 𝕍^ξ} |ĥ_a^1(u)| ≥ λ) ≤ C e^{−C⁻¹λ²}`."

`dzz_hat_sup_tail` formalizes this for every band `0 < a ≤ b`, every closed box
`ferniqueBox x₀ s` (`𝕍^ξ` is the box `[ξ, 1 − ξ]²`) and every continuous modification `Y` of
`ĥ_a^b` (one exists by `WhiteNoise.exists_continuous_modification_phi`). The step "Lemma 2.1"
is used in its supremum form, the Borell–TIS inequality `SupTail.tail_iSup_abs_le_gaussian`;
"Lemma 2.3" is `SupTail.dzz_lemma23_continuous`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma norm_sub_le_of_mem_ferniqueBox {x₀ u v : ℂ} {s : ℝ} (hu : u ∈ ferniqueBox x₀ s)
    (hv : v ∈ ferniqueBox x₀ s) : ‖u - v‖ ≤ 2 * s := by
  obtain ⟨⟨hu1, hu2⟩, hu3, hu4⟩ := hu
  obtain ⟨⟨hv1, hv2⟩, hv3, hv4⟩ := hv
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : |u.re - v.re| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |u.im - v.im| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- **DZZ, proof of Lemma 2.9 (l. 628–633)**: for `0 < a ≤ b`, a box `ferniqueBox x₀ s` and a
continuous modification `Y` of `ĥ_a^b`, there is `C > 0` with
`P(sup_{v ∈ box} |Y v| ≥ λ) ≤ C e^{−λ²/C}` for all `λ ≥ 0`. -/
theorem dzz_hat_sup_tail (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {x₀ : ℂ} {s : ℝ} (hs : 0 < s) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hY : ∀ x, Y x =ᵐ[P] phi W a b x) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 ≤ lam →
      P.real {ω | lam ≤ ⨆ v : ferniqueBox x₀ s, |Y v ω|} ≤ C * Real.exp (-lam ^ 2 / C) := by
  have hP := hW.isProbabilityMeasure
  set B := ferniqueBox x₀ s
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox x₀ s)
  have : Nonempty B := ⟨⟨x₀, mem_ferniqueBox_self hs.le⟩⟩
  set X : B → Ω → ℝ := fun v => Y v
  have hX : IsGaussianProcess X P :=
    (isGaussianProcess_phi_comp hW a b (fun v : B => (v : ℂ))).congr fun v => (hY v).symm
  have hint0 : ∀ x, ∫ ω, Y x ω ∂P = 0 := fun x => by
    rw [integral_congr_ae (hY x)]; exact integral_phi hW a b x
  -- increments: `E (Y v − Y u)² ≤ |u − v|²/a²` (eq-hat-h-continuity)
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
  -- the rescaled fields `G = c Y`, `G' = -c Y` satisfy the hypothesis of DZZ Lemma 2.3
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
  -- back to `Y` and `-Y`
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
  -- Borell–TIS
  set M : ℝ := c⁻¹ * ferniqueCF
  have hl : 0 ≤ Real.log (b / a) :=
    Real.log_nonneg ((one_le_div ha).2 hab)
  set σ : ℝ := Real.sqrt (Real.log (b / a) + 1)
  have hσ2 : σ ^ 2 = Real.log (b / a) + 1 := Real.sq_sqrt (by linarith)
  have hvar : ∀ v : B, Var[X v; P] ≤ σ ^ 2 := by
    intro v
    rw [hσ2, variance_congr (hY v), variance_phi hW ha hab]
    linarith
  have hσp : 0 < σ ^ 2 := by rw [hσ2]; linarith
  refine ⟨2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) + 4 * σ ^ 2, by positivity, fun lam hlam => ?_⟩
  have h := tail_iSup_abs_le_gaussian hX (fun v => hint0 v) (fun ω => (hYc ω).comp
    continuous_subtype_val) hi1 hi2 hM1 hM2 hvar hlam
  refine h.trans ?_
  set C := 2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) + 4 * σ ^ 2
  have hC1 : 2 * Real.exp (M ^ 2 / (2 * σ ^ 2)) ≤ C := by simp only [C]; linarith
  have hC2 : 2 * (2 * σ ^ 2) ≤ C := by simp only [C]; nlinarith [Real.exp_pos (M ^ 2 / (2 * σ ^ 2))]
  have hexp : Real.exp (-lam ^ 2 / (2 * (2 * σ ^ 2))) ≤ Real.exp (-lam ^ 2 / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity) hC2
  exact mul_le_mul hC1 hexp (Real.exp_pos _).le (by positivity)

end DZZ
end LQGMetric
