/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.Cutoff at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.HarmGrad
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The cut-off harmonic function of MQ Lemma 4.1 and its Dirichlet energy (task P2-MQ)

MQ (Miller–Qian, arXiv:1812.03913, `lqg_geodesics.tex`, proof of Lemma 4.1, l. 566–583): fix
`φ ∈ C_0^∞(B(z, 29r/32))` with `φ ≡ 1` on `B(z, 7r/8)`, and put `g = (𝔥 − 𝔥(z)) φ`; by the
harmonic gradient estimate (MQ (4.1)) `‖g‖_∇ ≤ c(M)` on `E^M_{z,r}`. With general radii
`ρ₁ r < ρ₂ r < r` and centring constant `a` (decision D41):

* `exists_cutoff_harm` : there is `K₀ = K₀(ρ₁, ρ₂, M)` such that for every `z`, `r > 0`, every
  `g` harmonic on `B(z, r)` and every `a` with `|g − a| ≤ M` on `B(z, ρ₂ r)`, some
  `F ∈ C_c^∞(B(z, r))` equals `g − a` on `B(z, ρ₁ r)` and has Dirichlet energy `≤ K₀`.

Proof (MQ's): `F = (g − a) χ(r⁻¹(· − z))` for a fixed bump `χ` equal to `1` on `B(0, ρ₁)` and
supported in `B̄(0, ρ')`, `ρ' = (ρ₁ + ρ₂)/2`; `|∇F| ≤ M ‖∇χ‖_∞ / r + 8M/((ρ₂ − ρ') r)`
(`norm_fderiv_le_of_harmonic`), so `∫ |∇F|² ≤ π ρ'² (8M/(ρ₂ − ρ') + M‖∇χ‖_∞)²`, independent of
`z`, `r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set Filter Topology MeasureTheory

namespace LQGMetric.MQ

/-- **MQ Lemma 4.1, energy step** (l. 566–583, general radii): the cut-off of `g − a`. -/
theorem exists_cutoff_harm {ρ₁ ρ₂ : ℝ} (h0 : 0 < ρ₁) (h12 : ρ₁ < ρ₂) (h2 : ρ₂ < 1) {M : ℝ}
    (hM : 0 < M) :
    ∃ K₀ : ℝ, ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd g (ball z r) → ∀ a : ℝ,
      (∀ w ∈ ball z (ρ₂ * r), |g w - a| ≤ M) →
      ∃ F : ℂ → ℝ, F ∈ QuantumZipper.zeroSpace (ball z r) ∧
        (∀ w ∈ ball z (ρ₁ * r), F w = g w - a) ∧
        QuantumZipper.dirichletEnergyOn (ball z r) F ≤ K₀ := by
  set ρ' := (ρ₁ + ρ₂) / 2 with hρ'
  have hρ1 : ρ₁ < ρ' := by rw [hρ']; linarith
  have hρ2 : ρ' < ρ₂ := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := h0.trans hρ1
  let χ₁ : ContDiffBump (0 : ℂ) := ⟨ρ₁, ρ', h0, hρ1⟩
  have hχ₁s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ₁ : ℂ → ℝ) := χ₁.contDiff
  obtain ⟨C₁, hC₁⟩ := (hχ₁s.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (χ₁.hasCompactSupport.fderiv (𝕜 := ℝ))
  set B0 := 8 * M / (ρ₂ - ρ') + M * C₁ with hB0
  refine ⟨(2 * Real.pi)⁻¹ * (B0 ^ 2 * (ρ' ^ 2 * Real.pi)), ?_⟩
  intro z r hr g hg a hb
  set A : ℂ → ℂ := fun y => r⁻¹ • (y - z) with hAdef
  have hAn : ∀ y, ‖A y‖ = r⁻¹ * ‖y - z‖ := fun y => by
    rw [hAdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
  set χ : ℂ → ℝ := fun y => χ₁ (A y) with hχdef
  have hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hχ₁s.comp hAs
  have hχ1 : ∀ y, ‖y - z‖ ≤ ρ₁ * r → χ y = 1 := fun y hy => by
    refine χ₁.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, hAn, inv_mul_le_iff₀ hr]
    show ‖y - z‖ ≤ r * ρ₁; linarith
  have hχ0 : ∀ y, ρ' * r ≤ ‖y - z‖ → χ y = 0 := fun y hy => by
    refine χ₁.zero_of_le_dist ?_
    rw [dist_zero_right, hAn, le_inv_mul_iff₀ hr]
    show r * ρ' ≤ ‖y - z‖; linarith
  have hχle : ∀ y, |χ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg χ₁.nonneg]; exact χ₁.le_one
  -- derivative of the cut-off
  have hAd : ∀ y, HasFDerivAt A (r⁻¹ • ContinuousLinearMap.id ℝ ℂ) y := fun y =>
    ((hasFDerivAt_id y).sub_const z).const_smul r⁻¹
  have hχd : ∀ y, HasFDerivAt χ ((fderiv ℝ (χ₁ : ℂ → ℝ) (A y)).comp
      (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)) y := fun y =>
    ((hχ₁s.differentiable (by simp)) (A y)).hasFDerivAt.comp y (hAd y)
  have hχdn : ∀ y, ‖(fderiv ℝ (χ₁ : ℂ → ℝ) (A y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖ ≤
      C₁ * r⁻¹ := fun y => by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul (hC₁ _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC₁ (A y)))
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 hr.le) ContinuousLinearMap.norm_id_le
  -- the function `F`
  set F : ℂ → ℝ := fun y => (g y - a) * χ y with hFdef
  have hρ'r : ρ' * r < r := by nlinarith
  have hsub : Function.support F ⊆ closedBall z (ρ' * r) := fun y hy => by
    by_contra hc
    rw [mem_closedBall, dist_eq_norm, not_le] at hc
    exact hy (by simp [hFdef, hχ0 y hc.le])
  have htsub : tsupport F ⊆ closedBall z (ρ' * r) := closure_minimal hsub isClosed_closedBall
  have hev : ∀ y, ρ' * r < ‖y - z‖ → F =ᶠ[𝓝 y] 0 := fun y hy => by
    have ho : IsOpen {y' : ℂ | ρ' * r < ‖y' - z‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    filter_upwards [ho.mem_nhds hy] with y' hy'
    simp [hFdef, hχ0 y' (le_of_lt hy')]
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : ‖y - z‖ < r
    · have hyb : y ∈ ball z r := by rw [mem_ball, dist_eq_norm]; exact hy
      exact (((HarmonicAt.analyticAt (hg y hyb)).contDiffAt).sub contDiffAt_const).mul
        hχs.contDiffAt
    · exact contDiffAt_const.congr_of_eventuallyEq (hev y (by linarith [not_lt.1 hy]))
  set s := (ρ₂ - ρ') * r with hsdef
  have hs : 0 < s := mul_pos (by linarith) hr
  set B := 8 * M / s + M * (C₁ * r⁻¹) with hBdef
  have hBr : B = B0 / r := by
    rw [hBdef, hB0, hsdef]; field_simp
  have hderiv : ∀ y, ‖fderiv ℝ F y‖ ^ 2 ≤ (closedBall z (ρ' * r)).indicator (fun _ => B ^ 2) y := by
    intro y
    by_cases hy : ‖y - z‖ ≤ ρ' * r
    · have hyc : y ∈ closedBall z (ρ' * r) := by rw [mem_closedBall, dist_eq_norm]; exact hy
      rw [indicator_of_mem hyc]
      have hyb : y ∈ ball z r := by rw [mem_ball, dist_eq_norm]; linarith
      have hgd : HasFDerivAt g (fderiv ℝ g y) y :=
        ((HarmonicAt.analyticAt (hg y hyb)).differentiableAt).hasFDerivAt
      have hFd : HasFDerivAt F _ y := (hgd.sub_const a).mul (hχd y)
      rw [hFd.fderiv]
      have hsb : ball y s ⊆ ball z (ρ₂ * r) := by
        intro w hw
        rw [mem_ball, dist_eq_norm] at hw ⊢
        calc ‖w - z‖ ≤ ‖w - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < s + ρ' * r := by linarith
          _ = ρ₂ * r := by rw [hsdef]; ring
      have hsr : ball z (ρ₂ * r) ⊆ ball z r := ball_subset_ball (by nlinarith)
      have hgrad := norm_fderiv_le_of_harmonic hs hM
        (fun w hw => hg w (hsr (hsb hw))) (fun w hw => hb w (hsb hw))
      have hgy : |g y - a| ≤ M := hb y (by rw [mem_ball, dist_eq_norm]; nlinarith)
      have hnorm : ‖(g y - a) • ((fderiv ℝ (χ₁ : ℂ → ℝ) (A y)).comp
          (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)) + χ y • fderiv ℝ g y‖ ≤ B := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hBdef, add_comm (8 * M / s)]
        refine add_le_add ?_ ?_
        · exact mul_le_mul hgy (hχdn y) (norm_nonneg _) hM.le
        · exact (mul_le_mul (hχle y) hgrad (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    · have hyc : y ∉ closedBall z (ρ' * r) := by rw [mem_closedBall, dist_eq_norm]; exact hy
      rw [indicator_of_notMem hyc, (hev y (not_le.1 hy)).fderiv_eq]
      simp
  refine ⟨F, ⟨hFs, ?_, htsub.trans (closedBall_subset_ball hρ'r)⟩, ?_, ?_⟩
  · exact (isCompact_closedBall z (ρ' * r)).of_isClosed_subset (isClosed_tsupport F) htsub
  · intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    simp [hFdef, hχ1 w hw.le]
  · unfold QuantumZipper.dirichletEnergyOn
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (by positivity))
    have hint : Integrable ((closedBall z (ρ' * r)).indicator (fun _ : ℂ => B ^ 2)) := by
      refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
      exact integrableOn_const measure_closedBall_lt_top.ne
    calc ∫ y in ball z r, ‖fderiv ℝ F y‖ ^ 2
        ≤ ∫ y in ball z r, (closedBall z (ρ' * r)).indicator (fun _ => B ^ 2) y :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hint.integrableOn
            (Eventually.of_forall hderiv)
      _ ≤ ∫ y, (closedBall z (ρ' * r)).indicator (fun _ => B ^ 2) y :=
          setIntegral_le_integral hint (Eventually.of_forall fun _ =>
            indicator_nonneg (fun _ _ => sq_nonneg _) _)
      _ = B0 ^ 2 * (ρ' ^ 2 * Real.pi) := by
          rw [integral_indicator_const _ measurableSet_closedBall, measureReal_def,
            Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal, NNReal.coe_real_pi, hBr,
            smul_eq_mul]
          field_simp

end LQGMetric.MQ
