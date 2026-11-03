/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.Polar at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Polar Green identities (GFF-K3 foundations F1, F1′, F3, F4)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.F.

* `integral_fderiv_radial_eq_circle` (F1): for `φ ∈ C¹_c(ℂ)` and `r ≥ 0`,
  `∫ ⟪∇φ(x), (x−c)/|x−c|²⟫ 1{|x−c|>r} dx = −2π ∫ φ d(circleUnif c r)`.
* `integral_fderiv_radial_eq_circle_foldH` (F1′): the same for `f ∘ foldH`, `f ∈ C¹_c(ℂ)`.
* `integral_gradInner_eq_neg_integral_mul_laplacian`, `integral_norm_fderiv_sq_eq` (F3).
* `integral_log_norm_sub_mul_laplacian` (F4): `∫ log‖z − w‖ Δφ z = 2π φ w`.

The core is `polar_green_core`: polar coordinates around `c`, Fubini, and the fundamental
theorem of calculus along each ray (with countably many exceptional radii).
-/

noncomputable section

open MeasureTheory Filter Set Metric Laplacian
open scoped Real Topology

namespace QuantumZipper

namespace K3

/-! ## Circle parametrizations -/

theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp only [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem continuous_circleMap_uncurry (c : ℂ) :
    Continuous (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
  unfold circleMap; fun_prop

theorem hasDerivAt_circleMap_radius (c : ℂ) (θ ρ : ℝ) :
    HasDerivAt (fun t : ℝ => circleMap c t θ) (circleMap 0 1 θ) ρ := by
  have h := ((hasDerivAt_id ρ).ofReal_comp.mul_const (Complex.exp (θ * Complex.I))).const_add c
  simpa [circleMap] using h

theorem norm_circleMap_sub_center (c : ℂ) (R θ : ℝ) : ‖circleMap c R θ - c‖ = |R| := by
  simp [circleMap]

/-- `circleUnif c r` in terms of the `(-π, π)` parametrization used by polar coordinates. -/
theorem integral_circleUnif_eq {g : ℂ → ℝ} (hg : Continuous g) (c : ℂ) (r : ℝ) :
    ∫ w, g w ∂(circleUnif c r) = (2 * π)⁻¹ * ∫ θ in Ioo (-π) π, g (circleMap c r θ) := by
  unfold circleUnif
  rw [integral_smul_measure,
    integral_map (measurable_circleMap c r).aemeasurable hg.aestronglyMeasurable,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have h := ((periodic_circleMap c r).comp g).intervalIntegral_add_eq (-π) 0
  have h1 : -π + 2 * π = π := by ring
  rw [h1, zero_add] at h
  exact h.symm

/-! ## The core polar identity -/

/-- Polar first-order Green identity, abstract form: `g` continuous, vanishing outside
`closedBall c M`, and `g'` a bounded measurable "derivative" of `g` along a.e. ray from `c`
(off countably many radii). -/
theorem polar_green_core {g : ℂ → ℝ} {g' : ℂ → (ℂ →L[ℝ] ℝ)} (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hg : Continuous g) {M : ℝ} (hgM : ∀ x, M < ‖x - c‖ → g x = 0)
    (hg'M : ∀ x, M < ‖x - c‖ → g' x = 0) (hg'm : Measurable g') {C : ℝ}
    (hC : ∀ x, ‖g' x‖ ≤ C)
    (hderiv : ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)), ∃ s : Set ℝ, s.Countable ∧
      ∀ ρ, r < ρ → ρ ∉ s → HasDerivAt (fun t => g (circleMap c t θ))
        (g' (circleMap c ρ θ) (circleMap 0 1 θ)) ρ) :
    ∫ x, (if r < ‖x - c‖ then g' x ((x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ)) else 0) =
      -∫ θ in Ioo (-π) π, g (circleMap c r θ) := by
  set F : ℝ × ℝ → ℝ := fun p => g' (circleMap c p.1 p.2) (circleMap 0 1 p.2) with hFdef
  have hcm := continuous_circleMap_uncurry c
  have hFm : Measurable F := by
    have h1 : Measurable fun p : ℝ × ℝ => g' (circleMap c p.1 p.2) := hg'm.comp hcm.measurable
    have h2 : Measurable fun p : ℝ × ℝ => circleMap 0 1 p.2 :=
      ((continuous_circleMap 0 1).comp continuous_snd).measurable
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)).continuous.measurable.comp
      (h1.prodMk h2)
  have hFb : ∀ p, ‖F p‖ ≤ C := by
    intro p
    refine ((g' _).le_opNorm _).trans ?_
    rw [norm_circleMap_zero, abs_one, mul_one]; exact hC _
  have hFz : ∀ p : ℝ × ℝ, M < |p.1| → F p = 0 := by
    intro p hp
    simp only [hFdef]
    rw [hg'M _ (by rwa [norm_circleMap_sub_center])]; simp
  set R : ℝ := max M r + 1 with hRdef
  have hRM : M < R := by rw [hRdef]; linarith [le_max_left M r]
  have hRr : r < R := by rw [hRdef]; linarith [le_max_right M r]
  -- Step 1: translate and pass to polar coordinates.
  rw [← integral_add_right_eq_self _ c]
  simp only [add_sub_cancel_right]
  rw [← Complex.integral_comp_polarCoord_symm]
  have hpt : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hstep : ∀ p ∈ polarCoord.target,
      p.1 • (if r < ‖Complex.polarCoord.symm p‖ then
        g' (Complex.polarCoord.symm p + c)
          (Complex.polarCoord.symm p / ((‖Complex.polarCoord.symm p‖ ^ 2 : ℝ) : ℂ)) else 0) =
      (Ioi r ×ˢ (univ : Set ℝ)).indicator F p := by
    intro p hp
    rw [hpt] at hp
    have hp1 : 0 < p.1 := hp.1
    rw [polarCoord_symm_eq_circleMap, norm_circleMap_zero, abs_of_pos hp1]
    by_cases hrp : r < p.1
    · simp only [hrp, ↓reduceIte]
      rw [indicator_of_mem (by exact ⟨hrp, mem_univ _⟩)]
      have e1 : circleMap 0 p.1 p.2 + c = circleMap c p.1 p.2 := by
        simp [circleMap, add_comm]
      have e2 : circleMap 0 p.1 p.2 / ((p.1 ^ 2 : ℝ) : ℂ) = p.1⁻¹ • circleMap 0 1 p.2 := by
        simp only [circleMap, zero_add, Complex.real_smul]
        have : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp1.ne'
        push_cast
        field_simp
      rw [e1, e2, map_smul, smul_smul, mul_inv_cancel₀ hp1.ne', one_smul]
    · simp only [hrp, ↓reduceIte]
      rw [indicator_of_notMem (by exact fun h => hrp h.1), smul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hstep,
    setIntegral_indicator (measurableSet_Ioi.prod MeasurableSet.univ)]
  have hset : polarCoord.target ∩ (Ioi r ×ˢ (univ : Set ℝ)) = Ioi r ×ˢ Ioo (-π) π := by
    rw [hpt, prod_inter_prod, Ioi_inter_Ioi, inter_univ,
      max_eq_right hr]
  rw [hset]
  -- Step 2: integrability and Fubini.
  have hint : IntegrableOn F (Ioi r ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hS : IntegrableOn F (Ioc r R ×ˢ Ioo (-π) π) (volume.prod volume) := by
      refine Measure.integrableOn_of_bounded ?_ hFm.aestronglyMeasurable
        (Eventually.of_forall hFb)
      rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    refine hS.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro p ⟨⟨hp1, hp2⟩, hpS⟩
    apply hFz
    have : R < p.1 := by
      by_contra h
      exact hpS ⟨⟨hp1, not_lt.mp h⟩, hp2⟩
    rw [abs_of_pos (hr.trans_lt hp1)]; linarith
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  rw [integral_integral_swap (f := fun x y => F (x, y)) hint, ← integral_neg]
  -- Step 3: the fundamental theorem of calculus on each ray.
  refine integral_congr_ae ?_
  filter_upwards [hderiv] with θ hθ
  obtain ⟨s, hs, hd⟩ := hθ
  have hFθm : Measurable fun ρ => F (ρ, θ) := hFm.comp (measurable_id.prodMk measurable_const)
  have hgR : g (circleMap c R θ) = 0 := by
    apply hgM
    rw [norm_circleMap_sub_center, abs_of_pos (hr.trans_lt hRr)]
    exact hRM
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun ρ hρ => hFz _ ?_), ← intervalIntegral.integral_of_le hRr.le]
  · rw [integral_eq_of_hasDerivAt_off_countable_of_le (fun t => g (circleMap c t θ))
      (fun ρ => F (ρ, θ)) hRr.le hs, hgR, zero_sub]
    · exact (hg.comp (hcm.comp (Continuous.prodMk_left θ))).continuousOn
    · intro ρ hρ
      exact hd ρ hρ.1.1 hρ.2
    · have hIoc : IntegrableOn (fun ρ => F (ρ, θ)) (Ioc r R) volume :=
        Measure.integrableOn_of_bounded (by simp) hFθm.aestronglyMeasurable
          (Eventually.of_forall fun ρ => hFb _)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hRr.le).mpr hIoc
  · obtain ⟨h1, h2⟩ := hρ
    have : R < ρ := by
      by_contra h
      exact h2 ⟨h1, not_lt.mp h⟩
    rw [abs_of_pos (hr.trans_lt (h1 : r < ρ))]; linarith

/-! ## F1 -/

theorem exists_radius_of_hasCompactSupport {f : ℂ → ℝ} (hc : HasCompactSupport f) (c : ℂ) :
    ∃ M, ∀ x, M < ‖x - c‖ → x ∉ tsupport f := by
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall c
  refine ⟨M, fun x hx hxs => ?_⟩
  have := hM hxs
  rw [mem_closedBall, dist_eq_norm] at this
  linarith

/-- **F1.** Polar first-order Green identity. -/
theorem integral_fderiv_radial_eq_circle {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x, (if r < ‖x - c‖ then fderiv ℝ φ x ((x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ)) else 0) =
      -(2 * Real.pi) * ∫ w, φ w ∂(circleUnif c r) := by
  obtain ⟨M, hM⟩ := exists_radius_of_hasCompactSupport hc c
  have hdc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hdc
  rw [polar_green_core c hr hφ.continuous (M := M)
      (fun x hx => image_eq_zero_of_notMem_tsupport (hM x hx))
      (fun x hx => Function.notMem_support.mp fun h => hM x hx (support_fderiv_subset ℝ h))
      hdc.measurable hC ?_, integral_circleUnif_eq hφ.continuous]
  · field_simp
  · refine Eventually.of_forall fun θ => ⟨∅, countable_empty, fun ρ _ _ => ?_⟩
    exact ((hφ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt ρ
      (hasDerivAt_circleMap_radius c θ ρ)

/-! ## F1′: the folded variant -/

theorem foldH_eq_mk' (w : ℂ) : foldH w = (w.re : ℂ) + ((|w.im| : ℝ) : ℂ) * Complex.I := by
  unfold foldH
  split_ifs with h
  · apply Complex.ext <;> simp [abs_of_nonneg h]
  · apply Complex.ext <;> simp [abs_of_neg (not_le.mp h)]

theorem continuous_foldH_K3 : Continuous foldH := by
  rw [show foldH = fun w : ℂ => (w.re : ℂ) + ((|w.im| : ℝ) : ℂ) * Complex.I from
    funext foldH_eq_mk']
  fun_prop

theorem norm_foldH_K3 (w : ℂ) : ‖foldH w‖ = ‖w‖ := by
  unfold foldH; split_ifs <;> simp

/-- The a.e. derivative of `f ∘ foldH`. -/
def foldDeriv (f : ℂ → ℝ) (x : ℂ) : ℂ →L[ℝ] ℝ :=
  if 0 < x.im then fderiv ℝ f x
  else (fderiv ℝ f ((starRingEnd ℂ) x)).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem hasFDerivAt_comp_foldH {f : ℂ → ℝ} (hf : Differentiable ℝ f) {x : ℂ} (hx : x.im ≠ 0) :
    HasFDerivAt (f ∘ foldH) (foldDeriv f x) x := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hne : ¬ 0 < x.im := not_lt.mpr hlt.le
    simp only [foldDeriv, hne, ↓reduceIte]
    have h := (hf ((starRingEnd ℂ) x)).hasFDerivAt.comp x Complex.conjCLE.hasFDerivAt
    refine h.congr_of_eventuallyEq ?_
    have hopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
    filter_upwards [hopen.mem_nhds hlt] with z hz
    simp only [Function.comp, foldH, not_le.mpr (show z.im < 0 from hz), ↓reduceIte]
  · simp only [foldDeriv, hgt, ↓reduceIte]
    refine (hf x).hasFDerivAt.congr_of_eventuallyEq ?_
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds hgt] with z hz
    simp only [Function.comp, foldH, le_of_lt (show 0 < z.im from hz), ↓reduceIte]

theorem ae_im_ne_zero : ∀ᵐ x : ℂ, x.im ≠ 0 := by
  have h : volume ((LinearMap.ker Complex.imLm : Submodule ℝ ℂ) : Set ℂ) = 0 := by
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    have : Complex.I ∈ LinearMap.ker Complex.imLm := htop ▸ Submodule.mem_top
    simp at this
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with x hx
  intro h0
  exact hx (by simp [h0])

/-- **F1′.** The polar Green identity for the folded function `f ∘ foldH`. -/
theorem integral_fderiv_radial_eq_circle_foldH {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x, (if r < ‖x - c‖ then fderiv ℝ (f ∘ foldH) x ((x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ))
      else 0) = -(2 * Real.pi) * ∫ w, (f ∘ foldH) w ∂(circleUnif c r) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨M0, hM0⟩ := exists_radius_of_hasCompactSupport hc 0
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hdc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hgcont : Continuous (f ∘ foldH) := hf.continuous.comp continuous_foldH_K3
  have hfar : ∀ x : ℂ, M0 + ‖c‖ < ‖x - c‖ → M0 < ‖x‖ := by
    intro x hx
    have := norm_sub_le x c
    have := norm_le_insert' x c
    linarith [norm_sub_norm_le x c, norm_nonneg c, abs_norm_sub_norm_le x c,
      norm_sub_le x c, norm_add_le (x - c) c]
  have hfz : ∀ y : ℂ, M0 < ‖y‖ → fderiv ℝ f y = 0 := fun y hy =>
    Function.notMem_support.mp fun h => hM0 y (by simpa using hy) (support_fderiv_subset ℝ h)
  rw [integral_congr_ae (g := fun x => if r < ‖x - c‖ then
      foldDeriv f x ((x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ)) else 0) ?_]
  · rw [polar_green_core c hr hgcont (M := M0 + ‖c‖) ?_ ?_ ?_ (C := C) ?_ ?_,
      integral_circleUnif_eq hgcont]
    · field_simp
    · intro x hx
      have h1 : M0 < ‖foldH x - 0‖ := by
        rw [sub_zero, norm_foldH_K3]
        exact hfar x hx
      show f (foldH x) = 0
      exact image_eq_zero_of_notMem_tsupport (hM0 _ h1)
    · intro x hx
      have h1 := hfar x hx
      unfold foldDeriv
      split_ifs
      · exact hfz x h1
      · rw [hfz _ (by rwa [Complex.norm_conj])]; rfl
    · unfold foldDeriv
      refine Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im)
        hdc.measurable ?_
      exact ((hdc.comp Complex.continuous_conj).clm_comp continuous_const).measurable
    · intro x
      unfold foldDeriv
      split_ifs
      · exact hC x
      · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        have h1 : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simp
        calc ‖fderiv ℝ f ((starRingEnd ℂ) x)‖ * ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖
            ≤ C * 1 := mul_le_mul (hC _) h1 (norm_nonneg _) hC0
          _ = C := mul_one C
    · have h0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0} : Set ℝ) :=
        measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae h0] with θ hθ hθ0
      have hsin : Real.sin θ ≠ 0 := fun h =>
        hθ0 ((Real.sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2).mp h)
      have him : ∀ ρ : ℝ, (circleMap c ρ θ).im = c.im + ρ * Real.sin θ := by
        intro ρ; simp [circleMap, Complex.exp_ofReal_mul_I_im]
      refine ⟨{ρ | (circleMap c ρ θ).im = 0}, ?_, fun ρ _ hρ => ?_⟩
      · refine Set.Subsingleton.countable fun a ha b hb => ?_
        simp only [mem_ofPred_eq, him] at ha hb
        have : (a - b) * Real.sin θ = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hsin
      · exact HasFDerivAt.comp_hasDerivAt (l := f ∘ foldH) (f := fun t => circleMap c t θ) ρ
          (hasFDerivAt_comp_foldH hfd hρ) (hasDerivAt_circleMap_radius c θ ρ)
  · filter_upwards [ae_im_ne_zero] with x hx
    simp only [(hasFDerivAt_comp_foldH hfd hx).fderiv]

/-! ## F3: integration by parts -/

theorem clm_complex_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem contDiff_fderiv_apply_K3 {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (v : ℂ) :
    ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) :=
  (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- `Δφ = ∂₁∂₁φ + ∂_I∂_Iφ`. -/
theorem laplacian_eq_fderiv_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    Δ φ z = fderiv ℝ (fun y => fderiv ℝ φ y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z Complex.I := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have e : ∀ v : ℂ, fderiv ℝ (fun y => fderiv ℝ φ y v) z v = fderiv ℝ (fderiv ℝ φ) z v v := by
    intro v
    rw [fderiv_clm_apply (hd z) (differentiableAt_const v)]
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, e, e]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem continuous_laplacian_K3 {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (Δ φ) := by
  rw [show Δ φ = fun z => fderiv ℝ (fun y => fderiv ℝ φ y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) z Complex.I from
    funext (laplacian_eq_fderiv_fderiv hφ)]
  exact (((contDiff_fderiv_apply_K3 hφ 1).continuous_fderiv one_ne_zero).clm_apply
    continuous_const).add
    (((contDiff_fderiv_apply_K3 hφ _).continuous_fderiv one_ne_zero).clm_apply continuous_const)

theorem hasCompactSupport_laplacian_K3 {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (Δ φ) := by
  refine hc.mono' fun z hz => ?_
  by_contra h
  apply hz
  rw [(InnerProductSpace.laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp h)).eq_of_nhds]
  exact congrFun InnerProductSpace.laplacian_const z

/-- One-direction integration by parts. -/
theorem integral_mul_fderiv_fderiv_eq_neg {u φ : ℂ → ℝ} (hu : ContDiff ℝ 1 u)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (v : ℂ) :
    ∫ z, u z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v =
      -∫ z, fderiv ℝ u z v * fderiv ℝ φ z v := by
  set g : ℂ → ℝ := fun y => fderiv ℝ φ y v with hgdef
  have hg1 : ContDiff ℝ 1 g := contDiff_fderiv_apply_K3 hφ v
  have hgc : HasCompactSupport g := hc.fderiv_apply (𝕜 := ℝ) v
  have hg'c : HasCompactSupport (fun z => fderiv ℝ g z v) := hgc.fderiv_apply (𝕜 := ℝ) v
  have hg'cont : Continuous (fun z => fderiv ℝ g z v) :=
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hu' : Continuous (fun z => fderiv ℝ u z v) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h : ∫ x, ContinuousLinearMap.mul ℝ ℝ (u x) (fderiv ℝ g x v) =
      -∫ x, ContinuousLinearMap.mul ℝ ℝ (fderiv ℝ u x v) (g x) := by
    have i1 : Integrable (fun x => fderiv ℝ u x v * g x) :=
      (hu'.mul hg1.continuous).integrable_of_hasCompactSupport hgc.mul_left
    have i2 : Integrable (fun x => u x * fderiv ℝ g x v) :=
      (hu.continuous.mul hg'cont).integrable_of_hasCompactSupport hg'c.mul_left
    have i3 : Integrable (fun x => u x * g x) :=
      (hu.continuous.mul hg1.continuous).integrable_of_hasCompactSupport hgc.mul_left
    apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    · simpa only [ContinuousLinearMap.mul_apply'] using i1
    · simpa only [ContinuousLinearMap.mul_apply'] using i2
    · simpa only [ContinuousLinearMap.mul_apply'] using i3
    · exact fun x _ => ((hu.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v
    · exact fun x _ => ((hg1.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v
  simpa only [ContinuousLinearMap.mul_apply'] using h

/-- **F3.** `∫ ⟪∇u, ∇φ⟫ = -∫ u Δφ` for `u ∈ C¹`, `φ ∈ C²_c`. -/
theorem integral_gradInner_eq_neg_integral_mul_laplacian {u φ : ℂ → ℝ} (hu : ContDiff ℝ 1 u)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ z, gradInner u φ z = -∫ z, u z * Δ φ z := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hint : ∀ v, Integrable (fun z => fderiv ℝ u z v * fderiv ℝ φ z v) := fun v =>
    (((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v).mul_left
  have hint2 : ∀ v, Integrable (fun z => u z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v) :=
    fun v => (hu.continuous.mul (((contDiff_fderiv_apply_K3 hφ v).continuous_fderiv
      one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v).mul_left
  simp only [gradInner, laplacian_eq_fderiv_fderiv hφ, mul_add]
  rw [integral_add (hint 1) (hint _), integral_add (hint2 1) (hint2 _),
    integral_mul_fderiv_fderiv_eq_neg hu hφ hc, integral_mul_fderiv_fderiv_eq_neg hu hφ hc]
  ring

/-- **F3′.** `∫ ‖∇φ‖² = -∫ φ Δφ` for `φ ∈ C²_c`. -/
theorem integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ z, ‖fderiv ℝ φ z‖ ^ 2 = -∫ z, φ z * Δ φ z := by
  simp only [norm_fderiv_sq_eq_gradInner]
  exact integral_gradInner_eq_neg_integral_mul_laplacian (hφ.of_le (by norm_num)) hφ hc

/-! ## F4: the planar Green formula -/

/-- The truncated logarithm `log max(r, ‖z − w‖)`. -/
def truncLog (w : ℂ) (r : ℝ) (z : ℂ) : ℝ := Real.log (max r ‖z - w‖)

theorem lipschitzWith_truncLog (w : ℂ) {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal r⁻¹) (truncLog w r) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)]
  have := abs_log_max_sub_le z z' w hr
  unfold truncLog
  calc _ ≤ ‖z - z'‖ / r := this
    _ = r⁻¹ * ‖z - z'‖ := by ring

theorem hasFDerivAt_truncLog_of_lt (w : ℂ) {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : r < ‖x - w‖) :
    HasFDerivAt (truncLog w r) ((1 / 2 : ℝ) • ((‖x - w‖ ^ 2)⁻¹ •
      (2 • (innerSL ℝ (x - w)).comp (ContinuousLinearMap.id ℝ ℂ)))) x := by
  have hne : ‖x - w‖ ^ 2 ≠ 0 := (pow_pos (hr.trans hx) 2).ne'
  have h := (((hasFDerivAt_id x).sub_const w).norm_sq.log hne).const_smul (1 / 2 : ℝ)
  refine h.congr_of_eventuallyEq ?_
  have hopen : IsOpen {z : ℂ | r < ‖z - w‖} := isOpen_lt continuous_const (by fun_prop)
  filter_upwards [hopen.mem_nhds hx] with z hz
  have hz' : r < ‖z - w‖ := hz
  simp only [truncLog, max_eq_right hz'.le, id, Pi.smul_apply, smul_eq_mul, Real.log_pow]
  push_cast; ring

theorem truncLog_lineDeriv_combo (w : ℂ) {r : ℝ} (hr : 0 < r) (L : ℂ →L[ℝ] ℝ) {x : ℂ}
    (hx : ‖x - w‖ ≠ r) :
    lineDeriv ℝ (truncLog w r) x 1 * L 1 + lineDeriv ℝ (truncLog w r) x Complex.I * L Complex.I =
      if r < ‖x - w‖ then L ((x - w) / ((‖x - w‖ ^ 2 : ℝ) : ℂ)) else 0 := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · simp only [not_lt.mpr hlt.le, ↓reduceIte]
    have hloc : truncLog w r =ᶠ[𝓝 x] fun _ => Real.log r := by
      have hopen : IsOpen {z : ℂ | ‖z - w‖ < r} := isOpen_lt (by fun_prop) continuous_const
      filter_upwards [hopen.mem_nhds hlt] with z hz
      have hz' : ‖z - w‖ < r := hz
      simp only [truncLog, max_eq_left hz'.le]
    have hd : HasFDerivAt (truncLog w r) (0 : ℂ →L[ℝ] ℝ) x :=
      (hasFDerivAt_const _ _).congr_of_eventuallyEq hloc
    rw [(hd.hasLineDerivAt 1).lineDeriv, (hd.hasLineDerivAt Complex.I).lineDeriv]
    simp
  · simp only [hgt, ↓reduceIte]
    have hd := hasFDerivAt_truncLog_of_lt w hr hgt
    have hpos : 0 < ‖x - w‖ := hr.trans hgt
    rw [(hd.hasLineDerivAt 1).lineDeriv, (hd.hasLineDerivAt Complex.I).lineDeriv,
      clm_complex_apply L ((x - w) / _), Complex.div_ofReal_re, Complex.div_ofReal_im]
    simp [Complex.inner]
    field_simp

theorem abs_truncLog_le (w z : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hz : 0 < ‖z - w‖) :
    |truncLog w r z| ≤ |Real.log ‖z - w‖| := by
  unfold truncLog
  rcases le_total r ‖z - w‖ with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, abs_of_nonpos (Real.log_nonpos hr.le hr1),
      abs_of_nonpos (Real.log_nonpos hz.le (h.trans hr1))]
    linarith [Real.log_le_log hz h]

theorem integrable_log_norm_sub_mul_K3 {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (w : ℂ) :
    Integrable (fun z => Real.log ‖z - w‖ * ψ z) := by
  obtain ⟨M, hM⟩ := exists_radius_of_hasCompactSupport hc w
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hlogm : Measurable fun z : ℂ => Real.log ‖z - w‖ :=
    Real.measurable_log.comp (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
  have hN : Integrable (fun z : ℂ => max (-Real.log ‖z - w‖) 0) := by
    refine ⟨(hlogm.neg.max measurable_const).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_)
      ((admissible_lintegral_logNeg_sub w).trans_lt admissible_lintegral_logNeg_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_max_right _ _)]
    rcases le_total (-Real.log ‖y - w‖) 0 with hy | hy
    · rw [max_eq_right hy, ENNReal.ofReal_of_nonpos hy, ENNReal.ofReal_zero]
    · rw [max_eq_left hy]
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hc
  set L := max (Real.log M) 0 with hL
  refine Integrable.mono' ((hN.const_mul C).add (hψi.norm.const_mul L))
    (hlogm.mul hψ.measurable).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport ψ
  · have hzM : ‖z - w‖ ≤ M := not_lt.mp fun h => hM z h hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hlog : |Real.log ‖z - w‖| ≤ max (-Real.log ‖z - w‖) 0 + L := by
      rcases le_or_gt ‖z - w‖ 1 with h1 | h1
      · rw [abs_of_nonpos (Real.log_nonpos (norm_nonneg _) h1)]
        linarith [le_max_left (-Real.log ‖z - w‖) 0, le_max_right (Real.log M) 0]
      · rw [abs_of_pos (Real.log_pos h1)]
        have : Real.log ‖z - w‖ ≤ Real.log M := Real.log_le_log (by linarith) hzM
        linarith [le_max_left (Real.log M) 0, le_max_right (-Real.log ‖z - w‖) 0]
    have hψz : |ψ z| ≤ C := by simpa [Real.norm_eq_abs] using hC z
    have h2 := mul_le_mul_of_nonneg_left hψz (le_max_right (-Real.log ‖z - w‖) 0)
    have h3 := mul_le_mul_of_nonneg_right hlog (abs_nonneg (ψ z))
    have hL0 : 0 ≤ L := le_max_right _ _
    simp only [Pi.add_apply, Real.norm_eq_abs]
    nlinarith
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, norm_zero]
    exact add_nonneg (mul_nonneg hC0 (le_max_right _ _))
      (mul_nonneg (le_max_right _ _) (norm_nonneg _))

/-- For `r > 0`: `∫ log max(r, ‖z − w‖) Δφ z = 2π ∫ φ d(circleUnif w r)`. -/
theorem integral_truncLog_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ z, truncLog w r z * Δ φ z = 2 * π * ∫ x, φ x ∂(circleUnif w r) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  set ℓ := truncLog w r with hℓdef
  have hℓc : Continuous ℓ := (lipschitzWith_truncLog w hr).continuous
  have key : ∀ v : ℂ, ∫ z, ℓ z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v =
      -∫ z, lineDeriv ℝ ℓ z v * fderiv ℝ φ z v := by
    intro v
    set g : ℂ → ℝ := fun y => fderiv ℝ φ y v with hgdef
    have hg1 : ContDiff ℝ 1 g := contDiff_fderiv_apply_K3 hφ v
    have hgc : HasCompactSupport g := hc.fderiv_apply (𝕜 := ℝ) v
    obtain ⟨D, hD⟩ := hg1.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) (lipschitzWith_truncLog w hr) hD hgc v
    have hneg : ∀ x, lineDeriv ℝ g x (-v) = -fderiv ℝ g x v := fun x => by
      rw [((hg1.differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
    rw [h]
    simp only [hneg, neg_mul, integral_neg, neg_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hint1 : ∀ v, Integrable (fun z => ℓ z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v) :=
    fun v => (hℓc.mul (((contDiff_fderiv_apply_K3 hφ v).continuous_fderiv
      one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v).mul_left
  have hint2 : ∀ v, Integrable (fun z => lineDeriv ℝ ℓ z v * fderiv ℝ φ z v) := by
    intro v
    have hm : Measurable fun z => lineDeriv ℝ ℓ z v := measurable_lineDeriv hℓc
    refine Integrable.bdd_mul (c := r⁻¹ * ‖v‖) ?_ hm.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    · exact ((hφ1.continuous_fderiv one_ne_zero).clm_apply
        continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) v)
    · have := norm_lineDeriv_le_of_lipschitz ℝ (lipschitzWith_truncLog w hr) (x₀ := z) (v := v)
      rwa [Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)] at this
  simp only [laplacian_eq_fderiv_fderiv hφ, mul_add]
  rw [integral_add (hint1 1) (hint1 _), key, key, ← neg_add, ← integral_add (hint2 1) (hint2 _)]
  have hae : (fun z => lineDeriv ℝ ℓ z 1 * fderiv ℝ φ z 1 +
      lineDeriv ℝ ℓ z Complex.I * fderiv ℝ φ z Complex.I) =ᵐ[volume]
      fun z => if r < ‖z - w‖ then fderiv ℝ φ z ((z - w) / ((‖z - w‖ ^ 2 : ℝ) : ℂ)) else 0 := by
    have hs : volume (sphere w r) = 0 := Measure.addHaar_sphere volume w r
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs] with z hz
    exact truncLog_lineDeriv_combo w hr _ (by simpa [mem_sphere, dist_eq_norm] using hz)
  rw [integral_congr_ae hae, integral_fderiv_radial_eq_circle hφ1 hc w hr.le]
  ring

/-- **F4.** The planar Green formula `∫ log‖z − w‖ Δφ z = 2π φ(w)` for `φ ∈ C²_c`. -/
theorem integral_log_norm_sub_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (w : ℂ) :
    ∫ z, Real.log ‖z - w‖ * Δ φ z = 2 * Real.pi * φ w := by
  have hΔc := continuous_laplacian_K3 hφ
  have hΔs : HasCompactSupport (Δ φ) := hasCompactSupport_laplacian_K3 hc
  have hint := integrable_log_norm_sub_mul_K3 hΔc hΔs w
  have hw : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ({w} : Set ℂ) :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton w)
  have h1 : Tendsto (fun r => ∫ z, truncLog w r z * Δ φ z) (𝓝[>] 0)
      (𝓝 (∫ z, Real.log ‖z - w‖ * Δ φ z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖Real.log ‖z - w‖ * Δ φ z‖) ?_ ?_ hint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ((lipschitzWith_truncLog w hr).continuous.mul hΔc).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
      filter_upwards [hw] with z hz
      have hpos : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_truncLog_le w z hr.1 hr.2.le hpos) (abs_nonneg _)
    · filter_upwards [hw] with z hz
      have hpos : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
      simp only [truncLog, max_eq_right hr.2.le]
  have h2 : (fun r => ∫ z, truncLog w r z * Δ φ z) =ᶠ[𝓝[>] 0]
      fun r => 2 * π * ∫ x, φ x ∂(circleUnif w r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact integral_truncLog_mul_laplacian hφ hc w hr
  have h3 : Tendsto (fun r => 2 * π * ∫ x, φ x ∂(circleUnif w r)) (𝓝[>] 0)
      (𝓝 (2 * π * φ w)) := by
    refine Tendsto.const_mul _ ?_
    simp_rw [integral_circleUnif_eq hφ.continuous]
    have hvol : ∫ θ in Ioo (-π) π, φ (circleMap w 0 θ) = 2 * π * φ w := by
      simp only [circleMap_zero_radius, Function.const_apply, setIntegral_const, smul_eq_mul]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
      ring
    have hφw : φ w = (2 * π)⁻¹ * ∫ θ in Ioo (-π) π, φ (circleMap w 0 θ) := by
      rw [hvol]; field_simp
    rw [hφw]
    refine Tendsto.const_mul _ ?_
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall fun r =>
        (hφ.continuous.comp (continuous_circleMap w r)).aestronglyMeasurable)
      (Eventually.of_forall fun r => Eventually.of_forall fun θ => hC _)
      (integrable_const C) (Eventually.of_forall fun θ => ?_)
    have hcont : Continuous fun r : ℝ => φ (circleMap w r θ) :=
      hφ.continuous.comp ((continuous_circleMap_uncurry w).comp
        (continuous_id.prodMk continuous_const))
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (h1.congr' h2) h3

end K3

end QuantumZipper
