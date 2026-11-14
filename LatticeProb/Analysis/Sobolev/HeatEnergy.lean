import LatticeProb.Analysis.Sobolev.Defs
import Mathlib

/-!
# The heat-kernel form of the Gaussian-damped Fourier energy

For `g ∈ L¹(ℝ^d)` and `t > 0`, the Gaussian-damped Fourier energy of `g`
`∫ exp(-4π²t‖ξ‖²) ‖𝓕g ξ‖² dξ` equals the heat-kernel double integral
`∫∫ g y g y' p_t(y - y') dy dy'` with `p_t(z) = (4πt)^{-d/2} exp(-‖z‖²/(4t))`
(`heatEnergy_eq`). Mathlib's Fourier transform uses the character `e^{-2πi⟪x, ξ⟫}`, so the
Fourier transform of `p_t` is `exp(-4π²t‖ξ‖²)` (`fourier_gaussian_eq_heatKernel`).

The proof writes `‖𝓕g ξ‖² = 𝓕g ξ · conj (𝓕g ξ)` as a double integral of `g y g y'` against the
character `e^{-2πi⟪y - y', ξ⟫}`, multiplies by the Gaussian, exchanges the order of integration
(the integrand is absolutely integrable because `g` is) and evaluates the `ξ`-integral by the Fourier
transform of the Gaussian.
-/

open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace LatticeProb.Sobolev

/-- The heat kernel `(4πt)^{-d/2} exp(-‖z‖²/(4t))`, whose Fourier transform is
`exp(-4π²t‖ξ‖²)`. -/
noncomputable def heatKernel (d : ℕ) (t : ℝ) (z : Space d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))

theorem heatKernel_nonneg (d : ℕ) {t : ℝ} (ht : 0 < t) (z : Space d) : 0 ≤ heatKernel d t z := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

theorem heatKernel_le (d : ℕ) {t : ℝ} (ht : 0 < t) (z : Space d) :
    heatKernel d t z ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
  unfold heatKernel
  have h1 : Real.exp (-‖z‖ ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖z‖]) (by positivity)
  have h2 : 0 ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem continuous_heatKernel (d : ℕ) (t : ℝ) : Continuous (heatKernel d t) := by
  unfold heatKernel
  fun_prop

/-- The Fourier transform of the Gaussian `exp(-4π²t‖ξ‖²)` is the heat kernel. -/
theorem fourier_gaussian_eq_heatKernel (d : ℕ) {t : ℝ} (ht : 0 < t) (w : Space d) :
    𝓕 (fun ξ : Space d => ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) w =
      (heatKernel d t w : ℂ) := by
  have hb : 0 < (((4 * Real.pi ^ 2 * t : ℝ)) : ℂ).re := by
    simp only [Complex.ofReal_re]
    positivity
  have h := fourier_gaussian_innerProductSpace (V := Space d) hb w
  have hfun : (fun ξ : Space d => ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) =
      fun v : Space d => Complex.exp (-(((4 * Real.pi ^ 2 * t : ℝ)) : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext ξ
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun, h, finrank_euclideanSpace_fin]
  have hπ : (Real.pi : ℂ) / (((4 * Real.pi ^ 2 * t : ℝ)) : ℂ) = (((4 * Real.pi * t)⁻¹ : ℝ) : ℂ) := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
  have hexp : ((d : ℂ) / 2) = ((((d : ℝ) / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hπ, hexp, ← Complex.ofReal_cpow (by positivity)]
  have hr : ((4 * Real.pi * t)⁻¹) ^ ((d : ℝ) / 2) = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1
    ring
  have he : Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (((4 * Real.pi ^ 2 * t : ℝ)) : ℂ)) =
      ((Real.exp (-‖w‖ ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
  rw [he, hr]
  unfold heatKernel
  push_cast
  ring


/-- The character `ξ ↦ e^{-2πi⟪x, ξ⟫}`. -/
noncomputable def phase {d : ℕ} (x ξ : Space d) : ℂ :=
  Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

theorem norm_phase {d : ℕ} (x ξ : Space d) : ‖phase x ξ‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_phase (d : ℕ) : Continuous fun p : Space d × Space d => phase p.1 p.2 := by
  unfold phase
  fun_prop

theorem phase_mul_phase {d : ℕ} (x y ξ : Space d) :
    phase x ξ * phase y ξ = phase (x + y) ξ := by
  unfold phase
  rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, inner_add_left]
  congr 3
  ring

theorem conj_phase {d : ℕ} (x ξ : Space d) : (starRingEnd ℂ) (phase x ξ) = phase (-x) ξ := by
  unfold phase
  rw [← Complex.exp_conj, inner_neg_left]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem fourier_eq_phase {d : ℕ} (f : Space d → ℂ) (ξ : Space d) :
    𝓕 f ξ = ∫ x, phase x ξ * f x := by
  rw [Real.fourier_eq']
  simp [phase, smul_eq_mul]

theorem phase_swap {d : ℕ} (x ξ : Space d) : phase x ξ = phase ξ x := by
  unfold phase
  rw [real_inner_comm]


theorem continuous_phase_left (d : ℕ) (ξ : Space d) : Continuous fun x : Space d => phase x ξ := by
  unfold phase
  fun_prop

/-- `‖𝓕g ξ‖² = 𝓕g ξ · conj (𝓕g ξ)` as a double integral against the character. -/
theorem sq_norm_fourier_eq {d : ℕ} {g : Space d → ℝ} (hg : Integrable g) (ξ : Space d) :
    (((‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 : ℝ)) : ℂ) =
      ∫ p : Space d × Space d, (g p.1 : ℂ) * (g p.2 : ℂ) * phase (p.1 - p.2) ξ
        ∂(volume.prod volume) := by
  have hG : Integrable (fun x : Space d => (g x : ℂ)) := hg.ofReal
  have hA : Integrable (fun x : Space d => phase x ξ * (g x : ℂ)) :=
    hG.bdd_mul (c := 1) (continuous_phase_left d ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (norm_phase x ξ).le)
  have hB : Integrable (fun x : Space d => phase (-x) ξ * (g x : ℂ)) :=
    hG.bdd_mul (c := 1) ((continuous_phase_left d ξ).comp continuous_neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (norm_phase (-x) ξ).le)
  have h1 : 𝓕 (fun x => (g x : ℂ)) ξ = ∫ x, phase x ξ * (g x : ℂ) := fourier_eq_phase _ ξ
  have h2 : (starRingEnd ℂ) (𝓕 (fun x => (g x : ℂ)) ξ) = ∫ x, phase (-x) ξ * (g x : ℂ) := by
    rw [h1, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [map_mul, conj_phase, Complex.conj_ofReal]
  have h3 : (((‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 : ℝ)) : ℂ) =
      𝓕 (fun x => (g x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (g x : ℂ)) ξ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [h3, h2, h1,
    ← integral_prod_mul (μ := volume) (ν := volume) (fun x => phase x ξ * (g x : ℂ))
      (fun y => phase (-y) ξ * (g y : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [sub_eq_add_neg, ← phase_mul_phase]
  ring


/-- The Gaussian `exp(-4π²t‖ξ‖²)` is integrable. -/
theorem integrable_gaussian_weight (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Space d => ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) := by
  have hb : 0 < (((4 * Real.pi ^ 2 * t : ℝ)) : ℂ).re := by
    simp only [Complex.ofReal_re]
    positivity
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Space d) hb 0 0
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The heat-kernel form of the Gaussian-damped Fourier energy of an integrable function. -/
theorem heatEnergy_eq : ∀ (d : ℕ) (t : ℝ), 0 < t → ∀ g : Space d → ℝ, Integrable g →
    ∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 =
      ∫ y : Space d, ∫ y' : Space d, g y * g y' * heatKernel d t (y - y') := by
  intro d t ht g hg
  apply Complex.ofReal_injective
  have hG : Integrable (fun x : Space d => (g x : ℂ)) := hg.ofReal
  have hrint := integrable_gaussian_weight d ht
  have hint3 : Integrable (Function.uncurry fun (ξ : Space d) (p : Space d × Space d) =>
      ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        ((g p.1 : ℂ) * (g p.2 : ℂ) * phase (p.1 - p.2) ξ))
      (volume.prod (volume.prod volume)) := by
    have h := hrint.mul_prod (hG.mul_prod hG)
    have hmeas : AEStronglyMeasurable
        (fun z : Space d × (Space d × Space d) => phase (z.2.1 - z.2.2) z.1)
        (volume.prod (volume.prod volume)) := by
      have : Continuous fun z : Space d × (Space d × Space d) => phase (z.2.1 - z.2.2) z.1 := by
        unfold phase
        fun_prop
      exact this.aestronglyMeasurable
    have h' := h.bdd_mul (c := 1) hmeas
      (Filter.Eventually.of_forall fun z => (norm_phase _ _).le)
    refine h'.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry]
    ring
  have e1 : (((∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
      ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 : ℝ)) : ℂ) =
      ∫ ξ : Space d, ∫ p : Space d × Space d,
        ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
          ((g p.1 : ℂ) * (g p.2 : ℂ) * phase (p.1 - p.2) ξ) ∂(volume.prod volume) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [Complex.ofReal_mul, sq_norm_fourier_eq hg ξ, ← integral_const_mul]
  have e3 : ∀ p : Space d × Space d, ∫ ξ : Space d,
      ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        ((g p.1 : ℂ) * (g p.2 : ℂ) * phase (p.1 - p.2) ξ) =
      (g p.1 : ℂ) * (g p.2 : ℂ) * (heatKernel d t (p.1 - p.2) : ℂ) := by
    intro p
    have hpt : ∀ ξ : Space d, ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        ((g p.1 : ℂ) * (g p.2 : ℂ) * phase (p.1 - p.2) ξ) =
        ((g p.1 : ℂ) * (g p.2 : ℂ)) *
          (phase ξ (p.1 - p.2) * ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) := by
      intro ξ
      rw [phase_swap (p.1 - p.2) ξ]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, ← fourier_eq_phase
      (fun ξ : Space d => ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) (p.1 - p.2),
      fourier_gaussian_eq_heatKernel d ht]
  have hint : Integrable (fun p : Space d × Space d =>
      g p.1 * g p.2 * heatKernel d t (p.1 - p.2)) (volume.prod volume) := by
    have h := hg.mul_prod hg
    have hmeas : AEStronglyMeasurable (fun p : Space d × Space d => heatKernel d t (p.1 - p.2))
        (volume.prod volume) :=
      ((continuous_heatKernel d t).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    have h' := h.bdd_mul (c := (4 * Real.pi * t) ^ (-(d : ℝ) / 2)) hmeas
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg d ht _)]
        exact heatKernel_le d ht _)
    refine h'.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only
    ring
  rw [e1, integral_integral_swap hint3]
  simp_rw [e3]
  have e4 : ∫ y : Space d, ∫ y' : Space d, g y * g y' * heatKernel d t (y - y') =
      ∫ p : Space d × Space d, g p.1 * g p.2 * heatKernel d t (p.1 - p.2)
        ∂(volume.prod volume) := (integral_prod _ hint).symm
  rw [e4, ← integral_complex_ofReal]
  push_cast
  rfl

end LatticeProb.Sobolev
