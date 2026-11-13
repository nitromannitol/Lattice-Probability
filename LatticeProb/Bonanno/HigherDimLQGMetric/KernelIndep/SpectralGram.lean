/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.SpectralGram at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.SpectralLp
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandVec

/-! The Gram matrix of the spectral vectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd IsLFPPKernel bandVec autoCorr)

theorem coeFn_specVec {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z : Rd d) :
    (specVec κ a b z : ℝ × Rd d → ℝ) =ᵐ[volume] specFun κ a b z := by
  rw [specVec, dite_eq_left (memLp_specFun hd hκ ha hab z)]
  exact MemLp.coeFn_toLp _

private theorem integrable_specFun_mul {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z w : Rd d) :
    Integrable (fun p : ℝ × Rd d => specFun κ a b z p * specFun κ a b w p) volume :=
  (memLp_specFun hd hκ ha hab z).integrable_mul (memLp_specFun hd hκ ha hab w)

private theorem inner_specVec_eq_integral {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (z w : Rd d) :
    inner ℝ (specVec κ a b z) (specVec κ a b w) =
      ∫ p : ℝ × Rd d, specFun κ a b z p * specFun κ a b w p := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_specVec hd hκ ha hab z,
    coeFn_specVec hd hκ ha hab w] with p hz hw
  rw [hz, hw, real_inner_eq_re_inner, RCLike.inner_apply]
  simp only [conj_trivial, mul_comm, RCLike.mul_re, RCLike.re_to_real,
    RCLike.im_to_real, mul_zero, sub_zero]

private def translatedKernelSchwartz {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (x : Rd d) : SchwartzMap (Rd d) ℂ :=
  ((hκ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).comp_homeomorph
    (Homeomorph.addRight x)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hκ.contDiff.comp (contDiff_id.add contDiff_const)))

@[simp] private theorem translatedKernelSchwartz_apply {d : ℕ}
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (x y : Rd d) :
    translatedKernelSchwartz hκ x y = (κ (y + x) : ℂ) := rfl

private theorem fourier_translated_kernel {d : ℕ} (κ : Rd d → ℝ) (x η : Rd d) :
    𝓕 (fun y : Rd d => (κ (y + x) : ℂ)) η =
      Real.fourierChar (inner ℝ x η) •
        𝓕 (fun y : Rd d => (κ y : ℂ)) η := by
  have h := VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ (Rd d))
    (fun y : Rd d => (κ y : ℂ)) x
  have hh := congrFun h η
  simpa only [Real.fourier_eq, VectorFourier.fourierIntegral,
    Function.comp_apply, innerₗ_apply_apply] using hh

private theorem re_inner_fourier_phase (v : ℂ) (r : ℝ) :
    (inner ℂ v (Real.fourierChar r • v)).re = ‖v‖ ^ 2 *
      Real.cos (2 * Real.pi * r) := by
  have hinner : inner ℂ v (Real.fourierChar r • v) =
      (Real.fourierChar r : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Circle.smul_def, inner_smul_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hinner, Real.fourierChar_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

private theorem integrable_inner_schwartz {d : ℕ}
    (f g : SchwartzMap (Rd d) ℂ) :
    Integrable (fun x : Rd d => inner ℂ (f x) (g x)) volume := by
  have hf := f.memLp 2 volume
  have hg := g.memLp 2 volume
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp _) (hg.toLp _)
  apply h.congr
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hfx hgx
  simp [hfx, hgx]

/-- Fourier autocorrelation identity for admissible kernels. -/
theorem ki_autoCorr_eq_integral_fourier {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (x : Rd d) :
    autoCorr κ x = ∫ η : Rd d,
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) η‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x η) := by
  let f := kiKernelSchwartz hκ
  let g := translatedKernelSchwartz hκ x
  have hF := integrable_inner_schwartz (𝓕 f) (𝓕 g)
  have hG := integrable_inner_schwartz f g
  have hp := SchwartzMap.integral_inner_fourier_fourier f g
  have hpr := congrArg Complex.re hp
  have hpr' : (∫ η : Rd d, (inner ℂ ((𝓕 f) η) ((𝓕 g) η)).re) =
      ∫ y : Rd d, (inner ℂ (f y) (g y)).re := by
    calc
      _ = (∫ η : Rd d, inner ℂ ((𝓕 f) η) ((𝓕 g) η)).re := by
        simpa only [RCLike.re_to_complex] using (integral_re hF)
      _ = (∫ y : Rd d, inner ℂ (f y) (g y)).re := hpr
      _ = _ := by simpa only [RCLike.re_to_complex] using (integral_re hG).symm
  have hleft : (∫ η : Rd d, (inner ℂ ((𝓕 f) η) ((𝓕 g) η)).re) =
      ∫ η : Rd d, ‖𝓕 (fun y : Rd d => (κ y : ℂ)) η‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x η) := by
    apply integral_congr_ae
    filter_upwards [] with η
    have hf : (𝓕 f) η = 𝓕 (fun y : Rd d => (κ y : ℂ)) η := by
      congr 1
    have hg : (𝓕 g) η = 𝓕 (fun y : Rd d => (κ (y + x) : ℂ)) η := by
      congr 1
    rw [hf, hg, fourier_translated_kernel κ x η]
    exact re_inner_fourier_phase _ _
  have hright : (∫ y : Rd d, (inner ℂ (f y) (g y)).re) = autoCorr κ x := by
    unfold autoCorr
    apply integral_congr_ae
    filter_upwards [] with y
    simp [f, g, RCLike.inner_apply]
    ring
  exact hright.symm.trans (hpr'.symm.trans hleft)

private theorem specFun_mul_apply {d : ℕ} (κ : Rd d → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (z w : Rd d) (p : ℝ × Rd d) :
    specFun κ a b z p * specFun κ a b w p =
      (Ico (0 : ℝ) 1).indicator (fun _ => bandSpec κ a b p.2 *
        (Real.cos (2 * Real.pi * inner ℝ z p.2) *
          Real.cos (2 * Real.pi * inner ℝ w p.2))) p.1 +
      (Ico (1 : ℝ) 2).indicator (fun _ => bandSpec κ a b p.2 *
        (Real.sin (2 * Real.pi * inner ℝ z p.2) *
          Real.sin (2 * Real.pi * inner ℝ w p.2))) p.1 := by
  have hS : 0 ≤ bandSpec κ a b p.2 := bandSpec_nonneg κ ha p.2
  by_cases h0 : p.1 ∈ Ico (0 : ℝ) 1
  · have h1 : p.1 ∉ Ico (1 : ℝ) 2 := by
      intro h1
      exact (not_lt_of_ge h1.1) h0.2
    simp only [specFun, Set.indicator_of_mem h0, Set.indicator_of_notMem h1, add_zero]
    calc
      _ = (Real.sqrt (bandSpec κ a b p.2)) ^ 2 *
          (Real.cos (2 * Real.pi * inner ℝ z p.2) *
            Real.cos (2 * Real.pi * inner ℝ w p.2)) := by ring
      _ = _ := by rw [Real.sq_sqrt hS]
  · by_cases h1 : p.1 ∈ Ico (1 : ℝ) 2
    · simp only [specFun, Set.indicator_of_notMem h0, Set.indicator_of_mem h1,
        zero_add]
      calc
        _ = (Real.sqrt (bandSpec κ a b p.2)) ^ 2 *
            (Real.sin (2 * Real.pi * inner ℝ z p.2) *
              Real.sin (2 * Real.pi * inner ℝ w p.2)) := by ring
        _ = _ := by rw [Real.sq_sqrt hS]
    · simp [specFun, h0, h1]

private theorem integral_specFun_mul {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (z w : Rd d) :
    (∫ p : ℝ × Rd d, specFun κ a b z p * specFun κ a b w p) =
      ∫ η : Rd d, bandSpec κ a b η *
        Real.cos (2 * Real.pi * inner ℝ (z - w) η) := by
  have hi : Integrable (fun p : ℝ × Rd d =>
      specFun κ a b z p * specFun κ a b w p) (volume.prod volume) :=
    integrable_specFun_mul hd hκ ha hab z w
  have hswap := integral_integral_swap (f := fun s η =>
    specFun κ a b z (s, η) * specFun κ a b w (s, η)) hi
  have hprod := integral_prod _ hi
  have hreorder : (∫ p : ℝ × Rd d,
      specFun κ a b z p * specFun κ a b w p) =
      ∫ η : Rd d, ∫ s : ℝ,
        specFun κ a b z (s, η) * specFun κ a b w (s, η) := by
    exact hprod.trans hswap
  rw [hreorder]
  apply integral_congr_ae
  filter_upwards [] with η
  let A := bandSpec κ a b η *
    (Real.cos (2 * Real.pi * inner ℝ z η) *
      Real.cos (2 * Real.pi * inner ℝ w η))
  let B := bandSpec κ a b η *
    (Real.sin (2 * Real.pi * inner ℝ z η) *
      Real.sin (2 * Real.pi * inner ℝ w η))
  have hA : Integrable ((Ico (0 : ℝ) 1).indicator (fun _ => A)) volume :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)
  have hB : Integrable ((Ico (1 : ℝ) 2).indicator (fun _ => B)) volume :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)
  have hpt : ∀ s : ℝ, specFun κ a b z (s, η) * specFun κ a b w (s, η) =
      (Ico (0 : ℝ) 1).indicator (fun _ => A) s +
      (Ico (1 : ℝ) 2).indicator (fun _ => B) s := by
    intro s
    exact specFun_mul_apply κ ha.le z w (s, η)
  simp_rw [hpt]
  rw [integral_add hA hB]
  have hv0 : (volume.restrict (Ico (0 : ℝ) 1)).real univ = 1 := by norm_num
  have hv1 : (volume.restrict (Ico (1 : ℝ) 2)).real univ = 1 := by norm_num
  simp only [integral_indicator measurableSet_Ico, integral_const, hv0, hv1]
  dsimp [A, B]
  calc
    _ = bandSpec κ a b η *
        (Real.cos (2 * Real.pi * inner ℝ z η) *
          Real.cos (2 * Real.pi * inner ℝ w η) +
          Real.sin (2 * Real.pi * inner ℝ z η) *
            Real.sin (2 * Real.pi * inner ℝ w η)) := by ring
    _ = bandSpec κ a b η *
        Real.cos (2 * Real.pi * inner ℝ z η -
          2 * Real.pi * inner ℝ w η) := by rw [Real.cos_sub]
    _ = _ := by congr 1; rw [inner_sub_left]; ring_nf

private theorem integral_fourier_cos_scaled {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (x : Rd d) :
    (∫ η : Rd d, t ^ (d - 1) *
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x η)) =
      autoCorr κ (t⁻¹ • x) / t := by
  let f : Rd d → ℝ := fun η =>
    ‖𝓕 (fun y : Rd d => (κ y : ℂ)) η‖ ^ 2 *
      Real.cos (2 * Real.pi * inner ℝ (t⁻¹ • x) η)
  have h := Measure.integral_comp_smul (volume : Measure (Rd d)) f t
  rw [finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos ht _))] at h
  simp only [smul_eq_mul] at h
  have hphase : ∀ η : Rd d,
      inner ℝ (t⁻¹ • x) (t • η) = inner ℝ x η := by
    intro η
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hsc : (fun η : Rd d => f (t • η)) =
      fun η => ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x η) := by
    funext η
    simp only [f, hphase η]
  rw [hsc] at h
  have hmass := ki_autoCorr_eq_integral_fourier hκ (t⁻¹ • x)
  change autoCorr κ (t⁻¹ • x) = ∫ η : Rd d, f η at hmass
  rw [← hmass] at h
  have hp : t ^ d = t ^ (d - 1) * t := by
    calc
      t ^ d = t ^ (d - 1 + 1) := by rw [Nat.sub_add_cancel hd]
      _ = t ^ (d - 1) * t := by rw [pow_add, pow_one]
  have hp' : t ^ (d - 1) = t ^ d / t := (eq_div_iff ht.ne').2 hp.symm
  have hshape : (fun η : Rd d => t ^ (d - 1) *
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x η)) =
      (fun η => t ^ (d - 1) *
        (‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
          Real.cos (2 * Real.pi * inner ℝ x η))) := by
    funext η
    ring
  rw [hshape, integral_const_mul, hp']
  calc
    t ^ d / t * ∫ η : Rd d,
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x η)
        = (t ^ d * ∫ η : Rd d,
            ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
              Real.cos (2 * Real.pi * inner ℝ x η)) / t := by ring
    _ = autoCorr κ (t⁻¹ • x) / t := by
      rw [h]
      field_simp [ht.ne', ne_of_gt (pow_pos ht d)]

private theorem integral_bandSpec_cos {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (x : Rd d) :
    (∫ η : Rd d, bandSpec κ a b η *
      Real.cos (2 * Real.pi * inner ℝ x η)) =
      ∫ t in Ioo a b, autoCorr κ (t⁻¹ • x) / t := by
  have hbase := integrable_specIntegrand hd hκ ha hab
  change Integrable (fun p : ℝ × Rd d => p.1 ^ (d - 1) *
    ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (p.1 • p.2)‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod volume) at hbase
  have hcos : Measurable (fun p : ℝ × Rd d =>
      Real.cos (2 * Real.pi * inner ℝ x p.2)) := by fun_prop
  have hjoint : Integrable (fun p : ℝ × Rd d => p.1 ^ (d - 1) *
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (p.1 • p.2)‖ ^ 2 *
        Real.cos (2 * Real.pi * inner ℝ x p.2))
      ((volume.restrict (Ioo a b)).prod volume) := by
    refine hbase.mul_bdd (c := 1) hcos.aestronglyMeasurable ?_
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs] using
      (Real.abs_cos_le_one (2 * Real.pi * inner ℝ x p.2))
  have hswap := integral_integral_swap (f := fun t η => t ^ (d - 1) *
    ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
      Real.cos (2 * Real.pi * inner ℝ x η)) hjoint
  have hleft : (∫ η : Rd d, bandSpec κ a b η *
      Real.cos (2 * Real.pi * inner ℝ x η)) =
      ∫ η : Rd d, ∫ t in Ioo a b, t ^ (d - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
          Real.cos (2 * Real.pi * inner ℝ x η) := by
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [bandSpec, integral_mul_const]
  calc
    _ = ∫ η : Rd d, ∫ t in Ioo a b, t ^ (d - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
            Real.cos (2 * Real.pi * inner ℝ x η) := hleft
    _ = ∫ t in Ioo a b, ∫ η : Rd d, t ^ (d - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • η)‖ ^ 2 *
            Real.cos (2 * Real.pi * inner ℝ x η) := hswap.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact integral_fourier_cos_scaled hd hκ (ha.trans ht.1) x

/-- **KI-1.** Spectral and white-noise band vectors have identical Gram matrices. -/
theorem inner_specVec {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z w : Rd d) :
    inner ℝ (specVec κ a b z) (specVec κ a b w) =
      inner ℝ (bandVec κ a b z) (bandVec κ a b w) := by
  rw [inner_specVec_eq_integral hd hκ ha hab,
    integral_specFun_mul hd hκ ha hab,
    integral_bandSpec_cos hd hκ ha hab,
    HigherDimLFPP.inner_bandVec hκ ha ha]
  simp

end HigherDimLQGMetric
