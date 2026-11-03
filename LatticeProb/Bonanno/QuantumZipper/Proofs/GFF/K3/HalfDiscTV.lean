/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.HalfDiscTV at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar

/-!
# Green representation for the half-disc Green function (blueprint GFF-K3, node L3)

For `φ ∈ C²` even across `ℝ` with `tsupport φ ⊆ ball t r` (`t ∈ ℝ`), and `x ∈ ball t r`:

* `integral_neumannH_mul_neg_laplacian`: `∫_ℂ neumannH(w,·)(−Δφ) = 2π(φ w + φ w̄)` (F4 twice);
* `integral_halfDiscGreen_mul_neg_laplacian`: `∫_ℂ halfDiscGreen(x,·)(−Δφ) = 4π φ x` (the Poisson
  term vanishes: by Fubini it is `∫ 2π(φ u + φ ū) dP_x(u)`, and `φ = 0` on the circle);
* `halfDiscGreen_represent`: `(2π)⁻¹ ∫_H halfDiscGreen(x,·)(−Δφ) = φ x` (evenness);
* `halfDiscGreen_energy`: `(2π)⁻² ∫_H ∫_H halfDiscGreen (−Δφ)(−Δφ) = dirichletEnergyOn H φ`.
-/

noncomputable section

open MeasureTheory Filter Set Metric Laplacian
open scoped Real Topology ComplexConjugate ENNReal

namespace QuantumZipper

namespace K3

/-! ## Evenness of `Δφ`, `‖∇φ‖` and of integrals over `H` -/

theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport φ) :
    Δ φ z = 0 := by
  rw [(InnerProductSpace.laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hz)).eq_of_nhds]
  exact congrFun InnerProductSpace.laplacian_const z

theorem laplacian_conj_eq {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (heven : ∀ x, φ (conj x) = φ x)
    (z : ℂ) : Δ φ (conj z) = Δ φ z := by
  set L : ℂ →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ) with hL
  have hφc : φ ∘ L = φ := funext fun x => heven x
  conv_rhs => rw [← hφc]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [L.iteratedFDeriv_comp_right hφ z (by norm_num)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  simp [hL, Complex.conjCLE_apply]

theorem norm_fderiv_conj_eq {φ : ℂ → ℝ} (heven : ∀ x, φ (conj x) = φ x) (z : ℂ) :
    ‖fderiv ℝ φ (conj z)‖ = ‖fderiv ℝ φ z‖ := by
  have hφc : φ ∘ Complex.conjCLE = φ := funext fun x => heven x
  have hL : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp
  have key : ∀ w : ℂ, ‖fderiv ℝ φ w‖ ≤ ‖fderiv ℝ φ (conj w)‖ := fun w => by
    have h := Complex.conjCLE.comp_right_fderiv (𝕜 := ℝ) (f := φ) (x := w)
    rw [hφc] at h
    rw [h]
    calc _ ≤ ‖fderiv ℝ φ (Complex.conjCLE w)‖ * ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ φ (Complex.conjCLE w)‖ * 1 := mul_le_mul_of_nonneg_left hL (norm_nonneg _)
      _ = ‖fderiv ℝ φ (conj w)‖ := by rw [mul_one, Complex.conjCLE_apply]
  refine le_antisymm ?_ (key z)
  have := key (conj z)
  rwa [Complex.conj_conj] at this

theorem measurableSet_H_k3 : MeasurableSet H :=
  measurableSet_lt measurable_const Complex.measurable_im

theorem Hbar_ae_eq_H : (Hbar : Set ℂ) =ᵐ[volume] H := by
  filter_upwards [ae_im_ne_zero] with z hz
  change (0 ≤ z.im) = (0 < z.im)
  exact propext ⟨fun h => lt_of_le_of_ne h (Ne.symm hz), le_of_lt⟩

/-- For an even integrable `g`, `∫_ℂ g = 2 ∫_H g`. -/
theorem integral_eq_two_mul_setIntegral_H {g : ℂ → ℝ} (hg : Integrable g)
    (heven : ∀ z, g (conj z) = g z) : ∫ z, g z = 2 * ∫ z in H, g z := by
  rw [← integral_add_compl measurableSet_H_k3 hg]
  have hmp : MeasurePreserving (Complex.conjLIE : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb g Hᶜ
  have hpre : (Complex.conjLIE : ℂ → ℂ) ⁻¹' Hᶜ = Hbar := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Complex.conjLIE_apply]
    change ¬ (0 < (conj z).im) ↔ 0 ≤ z.im
    rw [Complex.conj_im, not_lt, neg_nonpos]
  rw [← h1, hpre]
  simp only [Complex.conjLIE_apply, heven]
  rw [setIntegral_congr_set Hbar_ae_eq_H]
  ring

/-! ## F4 for `neumannH` -/

theorem neumannH_eq_logs (w y : ℂ) :
    neumannH w y = -(Real.log ‖y - w‖ + Real.log ‖y - conj w‖) := by
  unfold neumannH
  rw [norm_sub_rev w y, norm_sub_conj_comm w y]; ring

theorem integrable_neumannH_mul {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (w : ℂ) : Integrable (fun y => neumannH w y * ψ y) := by
  have e : (fun y => neumannH w y * ψ y) =
      fun y => -(Real.log ‖y - w‖ * ψ y + Real.log ‖y - conj w‖ * ψ y) := by
    funext y; rw [neumannH_eq_logs]; ring
  rw [e]
  exact ((integrable_log_norm_sub_mul_K3 hψ hc w).add
    (integrable_log_norm_sub_mul_K3 hψ hc (conj w))).neg

theorem integral_neumannH_mul_neg_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (w : ℂ) :
    ∫ y, neumannH w y * (-Δ φ y) = 2 * π * (φ w + φ (conj w)) := by
  have h1 := integrable_log_norm_sub_mul_K3 (continuous_laplacian_K3 hφ)
    (hasCompactSupport_laplacian_K3 hc) w
  have h2 := integrable_log_norm_sub_mul_K3 (continuous_laplacian_K3 hφ)
    (hasCompactSupport_laplacian_K3 hc) (conj w)
  have e : (fun y => neumannH w y * (-Δ φ y)) =
      fun y => Real.log ‖y - w‖ * Δ φ y + Real.log ‖y - conj w‖ * Δ φ y := by
    funext y; rw [neumannH_eq_logs]; ring
  rw [e, integral_add h1 h2, integral_log_norm_sub_mul_laplacian hφ hc,
    integral_log_norm_sub_mul_laplacian hφ hc]
  ring

/-! ## A uniform bound for Fubini -/

/-- A continuous cutoff equal to `1` on `closedBall 0 S`. -/
def bumpK3 (S : ℝ) (v : ℂ) : ℝ := max 0 (min 1 (S + 1 - ‖v‖))

theorem continuous_bumpK3 (S : ℝ) : Continuous (bumpK3 S) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

theorem hasCompactSupport_bumpK3 (S : ℝ) : HasCompactSupport (bumpK3 S) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (S + 1)) fun v hv => by
    rw [mem_closedBall_zero_iff, not_le] at hv
    unfold bumpK3
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]

theorem bumpK3_eq_one {S : ℝ} {v : ℂ} (hv : ‖v‖ ≤ S) : bumpK3 S v = 1 := by
  unfold bumpK3
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem lintegral_log_mul_le {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (R : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ w : ℂ, ‖w‖ ≤ R →
      ∫⁻ y, ENNReal.ofReal |Real.log ‖y - w‖ * ψ y| ≤ B := by
  obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hψ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set S := ρ + R
  have hI := integrable_log_norm_sub_mul_K3 (continuous_bumpK3 S) (hasCompactSupport_bumpK3 S) 0
  set g : ℂ → ℝ≥0∞ := fun v => ENNReal.ofReal |Real.log ‖v - 0‖ * bumpK3 S v| with hg
  have hgfin : ∫⁻ v, g v < ⊤ := by
    have := hI.2
    unfold HasFiniteIntegral at this
    simpa only [hg, Real.enorm_eq_ofReal_abs] using this
  refine ⟨ENNReal.ofReal M * ∫⁻ v, g v, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfin,
    fun w hw => ?_⟩
  calc ∫⁻ y, ENNReal.ofReal |Real.log ‖y - w‖ * ψ y| ≤ ∫⁻ y, ENNReal.ofReal M * g (y - w) := by
        refine lintegral_mono fun y => ?_
        rw [hg, ← ENNReal.ofReal_mul hM0]
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases hy : y ∈ tsupport ψ
        · have hy' : ‖y‖ ≤ ρ := by simpa using hρ hy
          have hyw : ‖y - w - 0‖ ≤ S := by
            rw [sub_zero]; exact (norm_sub_le _ _).trans (by linarith)
          rw [sub_zero] at hyw
          rw [bumpK3_eq_one hyw, mul_one, sub_zero, abs_mul, mul_comm M]
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM y) (abs_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, abs_zero]
          positivity
    _ = ENNReal.ofReal M * ∫⁻ v, g v := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun v => g v) w]

theorem integrable_neumannH_prod {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {ν : Measure ℂ} [IsFiniteMeasure ν] {R : ℝ} (hν : ∀ᵐ u ∂ν, ‖u‖ ≤ R) :
    Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2 * ψ p.2) (ν.prod volume) := by
  obtain ⟨B, hB, hBw⟩ := lintegral_log_mul_le hψ hc R
  have hm : Measurable fun p : ℂ × ℂ => neumannH p.1 p.2 * ψ p.2 :=
    measurable_neumannH.mul (hψ.measurable.comp measurable_snd)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hm.enorm.aemeasurable]
  calc ∫⁻ u, ∫⁻ y, ‖neumannH (u, y).1 (u, y).2 * ψ (u, y).2‖ₑ ∂volume ∂ν
      ≤ ∫⁻ _, (B + B) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hν] with u hu
        calc ∫⁻ y, ‖neumannH u y * ψ y‖ₑ
            ≤ ∫⁻ y, (ENNReal.ofReal |Real.log ‖y - u‖ * ψ y| +
                ENNReal.ofReal |Real.log ‖y - conj u‖ * ψ y|) := by
              refine lintegral_mono fun y => ?_
              rw [Real.enorm_eq_ofReal_abs, neumannH_eq_logs]
              refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
              rw [neg_mul, abs_neg, add_mul]
              exact abs_add_le _ _
          _ ≤ B + B := by
              have hmeas : Measurable fun y : ℂ => ENNReal.ofReal |Real.log ‖y - u‖ * ψ y| :=
                (continuous_abs.measurable.comp ((Real.measurable_log.comp
                  (measurable_id.sub measurable_const).norm).mul hψ.measurable)).ennreal_ofReal
              rw [lintegral_add_left' hmeas.aemeasurable]
              exact add_le_add (hBw u hu) (hBw (conj u) (by rwa [Complex.norm_conj]))
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hB, hB⟩) (measure_lt_top _ _)

/-! ## L3: the Green representation -/

theorem hasCompactSupport_of_tsupport_ball {φ : ℂ → ℝ} {t r : ℝ}
    (hsupp : tsupport φ ⊆ ball (t : ℂ) r) : HasCompactSupport φ :=
  (isCompact_closedBall (t : ℂ) r).of_isClosed_subset (isClosed_tsupport φ)
    (hsupp.trans ball_subset_closedBall)

theorem integrable_halfDiscGreen_mul {t r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ ball (t : ℂ) r)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y => halfDiscGreen t r x y * ψ y) ∧
      Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2 * ψ p.2)
        ((halfDiscPoisson t r x).prod volume) := by
  have := isProbabilityMeasure_halfDiscPoisson hr hx
  have hint := integrable_neumannH_prod hψ hc (ν := halfDiscPoisson t r x) (R := |t| + r)
    ((ae_halfDiscPoisson_mem hr x).mono fun u hu => norm_le_of_mem_sphere_k3 hu.1)
  refine ⟨?_, hint⟩
  have e : (fun y => halfDiscGreen t r x y * ψ y) = fun y =>
      neumannH x y * ψ y - ∫ u, neumannH u y * ψ y ∂(halfDiscPoisson t r x) := by
    funext y; rw [integral_mul_const]; unfold halfDiscGreen; ring
  rw [e]
  exact (integrable_neumannH_mul hψ hc x).sub hint.integral_prod_right

/-- `∫_ℂ halfDiscGreen(x, ·)(−Δφ) = 4π φ(x)` for even `φ ∈ C²` supported in the disc. -/
theorem integral_halfDiscGreen_mul_neg_laplacian {t r : ℝ} (hr : 0 < r) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : tsupport φ ⊆ ball (t : ℂ) r)
    (heven : ∀ x, φ (conj x) = φ x) {x : ℂ} (hx : x ∈ ball (t : ℂ) r) :
    ∫ y, halfDiscGreen t r x y * (-Δ φ y) = 4 * π * φ x := by
  have hc := hasCompactSupport_of_tsupport_ball hsupp
  have hDc : Continuous fun y => -Δ φ y := (continuous_laplacian_K3 hφ).neg
  have hDs : HasCompactSupport fun y => -Δ φ y := (hasCompactSupport_laplacian_K3 hc).neg
  have := isProbabilityMeasure_halfDiscPoisson hr hx
  obtain ⟨-, hint⟩ := integrable_halfDiscGreen_mul hr hx hDc hDs
  have e : (fun y => halfDiscGreen t r x y * (-Δ φ y)) = fun y =>
      neumannH x y * (-Δ φ y) - ∫ u, neumannH u y * (-Δ φ y) ∂(halfDiscPoisson t r x) := by
    funext y; rw [integral_mul_const]; unfold halfDiscGreen; ring
  rw [e, integral_sub (integrable_neumannH_mul hDc hDs x) hint.integral_prod_right,
    ← integral_integral_swap (f := fun u y => neumannH u y * (-Δ φ y)) hint,
    integral_neumannH_mul_neg_laplacian hφ hc x]
  have h0 : ∫ u, ∫ y, neumannH u y * (-Δ φ y) ∂volume ∂(halfDiscPoisson t r x) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_halfDiscPoisson_mem hr x] with u hu
    rw [integral_neumannH_mul_neg_laplacian hφ hc u, heven u]
    have hu0 : φ u = 0 := image_eq_zero_of_notMem_tsupport fun h => by
      have h1 := mem_ball_iff_norm.1 (hsupp h)
      have h2 := mem_sphere_iff_norm.1 hu.1
      linarith
    simp [hu0]
  rw [h0, heven x]
  ring

theorem halfDiscGreen_conj_right (t r : ℝ) (x y : ℂ) :
    halfDiscGreen t r x (conj y) = halfDiscGreen t r x y := by
  have hN : ∀ u, neumannH u (conj y) = neumannH u y := fun u => by
    unfold neumannH; rw [Complex.conj_conj]; ring
  unfold halfDiscGreen
  simp only [hN]

/-- **L3 (Green representation).** For `φ ∈ C²` even across `ℝ` with `tsupport φ ⊆ ball t r`
and `x ∈ ball t r`: `(2π)⁻¹ ∫_H halfDiscGreen(x, y)(−Δφ(y)) dy = φ(x)`. -/
theorem halfDiscGreen_represent {t r : ℝ} (hr : 0 < r) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : tsupport φ ⊆ ball (t : ℂ) r) (heven : ∀ x, φ (conj x) = φ x) {x : ℂ}
    (hx : x ∈ ball (t : ℂ) r) :
    (2 * π)⁻¹ * ∫ y in H, halfDiscGreen t r x y * (-Δ φ y) = φ x := by
  have hc := hasCompactSupport_of_tsupport_ball hsupp
  have hDc : Continuous fun y => -Δ φ y := (continuous_laplacian_K3 hφ).neg
  have hDs : HasCompactSupport fun y => -Δ φ y := (hasCompactSupport_laplacian_K3 hc).neg
  obtain ⟨hint, -⟩ := integrable_halfDiscGreen_mul hr hx hDc hDs
  have h2 := integral_eq_two_mul_setIntegral_H hint fun y => by
    simp only [halfDiscGreen_conj_right, laplacian_conj_eq hφ heven]
  rw [integral_halfDiscGreen_mul_neg_laplacian hr hφ hsupp heven hx] at h2
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h3 : ∫ y in H, halfDiscGreen t r x y * (-Δ φ y) = 2 * π * φ x := by linarith
  rw [h3, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `∫_H φ(−Δφ) = ∫_H ‖∇φ‖²` for even compactly supported `φ ∈ C²` (F3′ halved). -/
theorem setIntegral_H_mul_neg_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ x, φ (conj x) = φ x) :
    ∫ x in H, φ x * (-Δ φ x) = ∫ x in H, ‖fderiv ℝ φ x‖ ^ 2 := by
  have hA : Integrable fun x => φ x * (-Δ φ x) :=
    (hφ.continuous.mul (continuous_laplacian_K3 hφ).neg).integrable_of_hasCompactSupport
      hc.mul_right
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hBs : HasCompactSupport fun x => ‖fderiv ℝ φ x‖ ^ 2 :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun A : ℂ →L[ℝ] ℝ => ‖A‖ ^ 2) (by simp)
  have hB : Integrable fun x => ‖fderiv ℝ φ x‖ ^ 2 :=
    ((hφ1.continuous_fderiv one_ne_zero).norm.pow 2).integrable_of_hasCompactSupport hBs
  have e1 := integral_eq_two_mul_setIntegral_H hA fun x => by
    rw [heven, laplacian_conj_eq hφ heven]
  have e2 := integral_eq_two_mul_setIntegral_H hB fun x => by
    rw [norm_fderiv_conj_eq heven]
  have e3 := integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian hφ hc
  have e4 : ∫ x, φ x * (-Δ φ x) = -∫ x, φ x * Δ φ x := by
    rw [← integral_neg]; congr 1; funext x; ring
  linarith

end K3

end QuantumZipper
