import LatticeProb.WhiteNoise
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The heat kernel of `(2d)⁻¹ Δ`

The heat kernel `heatKernel d τ x` of the operator `L = (2d)⁻¹ Δ` on `Fin d → ℝ` is the product over
the coordinates of one-dimensional Gaussians of variance `τ / d`, and `0` for `τ ≤ 0`. We prove that it
solves the heat equation `∂_τ Φ = L Φ` for `τ > 0` (`heatKernel_hasDerivAt`), has integral one
(`integral_heatKernel`), is smooth on `{τ > 0}` (`contDiffOn_heatKernel`), and is an approximate
identity as `τ → 0⁺` (`tendsto_integral_heatKernel_mul`).

The product structure (`heatKernel_of_pos`, `heatKernel_update`) and the one-dimensional derivative
formulas are public so that bounds on the derivatives of the kernel can reuse them.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff
open LatticeProb.WhiteNoise

namespace LatticeProb.Heat

/-- The heat kernel of `∂_τ - (2d)⁻¹ Δ`: a product of one-dimensional Gaussians of variance `τ / d`,
and `0` for `τ ≤ 0`. -/
noncomputable def heatKernel (d : ℕ) (τ : ℝ) (x : Fin d → ℝ) : ℝ :=
  if 0 < τ then ∏ i : Fin d, ((2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2) *
    Real.exp (-(d : ℝ) * x i ^ 2 / (2 * τ))) else 0

/-- The one-dimensional Gaussian factor of the heat kernel. -/
noncomputable def heatKernel1 (d : ℕ) (τ y : ℝ) : ℝ :=
  (2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2) * Real.exp (-(d : ℝ) * y ^ 2 / (2 * τ))

theorem heatKernel_of_pos {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (x : Fin d → ℝ) :
    heatKernel d τ x = ∏ i, heatKernel1 d τ (x i) := by
  simp [heatKernel, heatKernel1, hτ]

theorem heatKernel_of_nonpos {d : ℕ} {τ : ℝ} (hτ : τ ≤ 0) (x : Fin d → ℝ) :
    heatKernel d τ x = 0 := by
  simp [heatKernel, not_lt.mpr hτ]

theorem heatKernel1_pos {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    0 < heatKernel1 d τ y := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  unfold heatKernel1
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem heatKernel_nonneg {d : ℕ} (hd : 1 ≤ d) (τ : ℝ) (x : Fin d → ℝ) : 0 ≤ heatKernel d τ x := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [heatKernel_of_nonpos hτ]
  · rw [heatKernel_of_pos hτ]
    exact Finset.prod_nonneg fun i _ => (heatKernel1_pos hd hτ _).le

theorem heatKernel_update {d : ℕ} {τ : ℝ} (hτ : 0 < τ) (x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    heatKernel d τ (Function.update x i t) =
      heatKernel1 d τ t * ∏ j ∈ Finset.univ.erase i, heatKernel1 d τ (x j) := by
  rw [heatKernel_of_pos hτ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

section OneDim

variable {d : ℕ}

theorem hasDerivAt_heatKernel1_y (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    HasDerivAt (heatKernel1 d τ) (-((d : ℝ) * y / τ) * heatKernel1 d τ y) y := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : HasDerivAt (fun y : ℝ => -(d : ℝ) * y ^ 2 / (2 * τ)) (-(d : ℝ) * (2 * y) / (2 * τ)) y := by
    have := ((hasDerivAt_pow 2 y).const_mul (-(d : ℝ))).div_const (2 * τ)
    simpa using this
  have h3 := (h1.exp).const_mul ((2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2))
  unfold heatKernel1
  convert h3 using 1
  field_simp

theorem hasDerivAt_heatKernel1_y_y (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    HasDerivAt (fun y => -((d : ℝ) * y / τ) * heatKernel1 d τ y)
      (((d : ℝ) ^ 2 * y ^ 2 / τ ^ 2 - d / τ) * heatKernel1 d τ y) y := by
  have h0 : HasDerivAt (fun y : ℝ => (d : ℝ) * y / τ) ((d : ℝ) / τ) y := by
    simpa using ((hasDerivAt_id y).const_mul (d : ℝ)).div_const τ
  have h1 := h0.neg
  have h2 := h1.mul (hasDerivAt_heatKernel1_y hd hτ y)
  convert h2 using 1
  simp only [Pi.neg_apply]
  ring

theorem hasDerivAt_heatKernel1_tau (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    HasDerivAt (fun s => heatKernel1 d s y)
      (((d : ℝ) * y ^ 2 / (2 * τ ^ 2) - 1 / (2 * τ)) * heatKernel1 d τ y) τ := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hp : HasDerivAt (fun s : ℝ => 2 * Real.pi * s / d) (2 * Real.pi / d) τ := by
    have := ((hasDerivAt_id τ).const_mul (2 * Real.pi)).div_const (d : ℝ)
    simpa using this
  have hp0 : 2 * Real.pi * τ / d ≠ 0 := by positivity
  have h1 := hp.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hp0)
  have he : HasDerivAt (fun s : ℝ => -(d : ℝ) * y ^ 2 / (2 * s))
      ((d : ℝ) * y ^ 2 / (2 * τ ^ 2)) τ := by
    have h := (hasDerivAt_inv hτ.ne').const_mul (-(d : ℝ) * y ^ 2 / 2)
    have hfun : (fun s : ℝ => -(d : ℝ) * y ^ 2 / (2 * s)) =
        fun s => (-(d : ℝ) * y ^ 2 / 2) * s⁻¹ := by
      funext s
      ring
    rw [hfun]
    convert h using 1
    field_simp
  have h2 := h1.mul he.exp
  unfold heatKernel1
  convert h2 using 1
  rw [Real.rpow_sub_one hp0]
  field_simp
  ring

end OneDim

/-- The heat kernel solves the heat equation `∂_τ Φ = (2d)⁻¹ Δ Φ` for `τ > 0`. -/
theorem heatKernel_hasDerivAt {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (x : Fin d → ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun s => heatKernel d s x) (contOp d (heatKernel d τ) x) τ := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hprod : HasDerivAt (fun s => ∏ i : Fin d, heatKernel1 d s (x i))
      (∑ i : Fin d, (∏ j ∈ Finset.univ.erase i, heatKernel1 d τ (x j)) •
        (((d : ℝ) * x i ^ 2 / (2 * τ ^ 2) - 1 / (2 * τ)) * heatKernel1 d τ (x i))) τ :=
    HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => heatKernel1 d s (x i))
      (fun i _ => hasDerivAt_heatKernel1_tau hd hτ (x i))
  have hev : (fun s => ∏ i : Fin d, heatKernel1 d s (x i)) =ᶠ[𝓝 τ] fun s => heatKernel d s x := by
    filter_upwards [Ioi_mem_nhds hτ] with s hs
    exact (heatKernel_of_pos hs x).symm
  refine (hprod.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  unfold contOp lap
  have hinner : ∀ i : Fin d, deriv (fun s => deriv (fun t => heatKernel d τ (Function.update x i t)) s)
      (x i) = (((d : ℝ) ^ 2 * x i ^ 2 / τ ^ 2 - d / τ) * heatKernel1 d τ (x i)) *
        ∏ j ∈ Finset.univ.erase i, heatKernel1 d τ (x j) := by
    intro i
    have hf : (fun t => heatKernel d τ (Function.update x i t)) =
        fun t => heatKernel1 d τ t * ∏ j ∈ Finset.univ.erase i, heatKernel1 d τ (x j) :=
      funext fun t => heatKernel_update hτ x i t
    have hg : (fun s => deriv (fun t => heatKernel d τ (Function.update x i t)) s) =
        fun s => (-((d : ℝ) * s / τ) * heatKernel1 d τ s) *
          ∏ j ∈ Finset.univ.erase i, heatKernel1 d τ (x j) := by
      funext s
      rw [hf]
      exact ((hasDerivAt_heatKernel1_y hd hτ s).mul_const _).deriv
    rw [hg]
    exact ((hasDerivAt_heatKernel1_y_y hd hτ (x i)).mul_const _).deriv
  simp only [hinner, smul_eq_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp


theorem heatKernel1_eq_const_mul_gaussian {d : ℕ} {τ : ℝ} (y : ℝ) :
    heatKernel1 d τ y = (2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2) *
      Real.exp (-((d : ℝ) / (2 * τ)) * y ^ 2) := by
  unfold heatKernel1
  rw [show -(d : ℝ) * y ^ 2 / (2 * τ) = -((d : ℝ) / (2 * τ)) * y ^ 2 by ring]

theorem integrable_heatKernel1 {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (heatKernel1 d τ) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hb : 0 < (d : ℝ) / (2 * τ) := by positivity
  have h := (integrable_exp_neg_mul_sq hb).const_mul ((2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2))
  have hfun : heatKernel1 d τ = fun y => (2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2) *
      Real.exp (-((d : ℝ) / (2 * τ)) * y ^ 2) := funext heatKernel1_eq_const_mul_gaussian
  rw [hfun]
  exact h

theorem integral_heatKernel1 {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    ∫ y : ℝ, heatKernel1 d τ y = 1 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hp : 0 < 2 * Real.pi * τ / d := by positivity
  have hfun : heatKernel1 d τ = fun y => (2 * Real.pi * τ / d) ^ (-(1 : ℝ) / 2) *
      Real.exp (-((d : ℝ) / (2 * τ)) * y ^ 2) := funext heatKernel1_eq_const_mul_gaussian
  rw [hfun, integral_const_mul, integral_gaussian]
  have h2 : Real.pi / ((d : ℝ) / (2 * τ)) = 2 * Real.pi * τ / d := by field_simp
  rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_add hp]
  norm_num

theorem integrable_heatKernel {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (heatKernel d τ) := by
  have hfun : heatKernel d τ = fun x : Fin d → ℝ => ∏ i, heatKernel1 d τ (x i) :=
    funext (heatKernel_of_pos hτ)
  have h := Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun _ => heatKernel1 d τ) fun _ => integrable_heatKernel1 hd hτ
  rw [hfun, volume_pi]
  exact h

/-- The heat kernel has integral one. -/
theorem integral_heatKernel {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : Fin d → ℝ, heatKernel d τ x = 1 := by
  have hfun : heatKernel d τ = fun x : Fin d → ℝ => ∏ i, heatKernel1 d τ (x i) :=
    funext (heatKernel_of_pos hτ)
  rw [hfun, integral_fintype_prod_volume_eq_prod (fun _ : Fin d => heatKernel1 d τ)]
  simp [integral_heatKernel1 hd hτ]

/-- The heat kernel is smooth on `{τ > 0}`. -/
theorem contDiffOn_heatKernel {d : ℕ} (hd : 1 ≤ d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | 0 < p.1} := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) =>
      ∏ i : Fin d, heatKernel1 d p.1 (p.2 i)) {p | 0 < p.1} := by
    refine contDiffOn_prod fun i _ => ?_
    have hfst : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => p.1) := contDiff_fst
    have hsnd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => p.2 i) :=
      (contDiff_apply ℝ ℝ i).comp contDiff_snd
    unfold heatKernel1
    refine ContDiffOn.mul ?_ ?_
    · refine ContDiffOn.rpow_const_of_ne ?_ fun p hp => ?_
      · exact ((contDiff_const.mul hfst).div_const (d : ℝ)).contDiffOn
      · have : 0 < p.1 := hp
        positivity
    · refine Real.contDiff_exp.comp_contDiffOn ?_
      refine ContDiffOn.div ?_ ?_ fun p hp => ?_
      · exact (contDiff_const.mul (hsnd.pow 2)).contDiffOn
      · exact (contDiff_const.mul hfst).contDiffOn
      · have : 0 < p.1 := hp
        positivity
  refine h.congr fun p hp => ?_
  have hp' : 0 < p.1 := hp
  exact heatKernel_of_pos hp' p.2

theorem continuous_heatKernel1 (d : ℕ) (τ : ℝ) : Continuous (heatKernel1 d τ) := by
  unfold heatKernel1
  fun_prop

theorem continuous_heatKernel {d : ℕ} {τ : ℝ} (hτ : 0 < τ) : Continuous (heatKernel d τ) := by
  have hfun : heatKernel d τ = fun x : Fin d → ℝ => ∏ i, heatKernel1 d τ (x i) :=
    funext (heatKernel_of_pos hτ)
  rw [hfun]
  exact continuous_finsetProd _ fun i _ => (continuous_heatKernel1 d τ).comp (continuous_apply i)

theorem heatKernel1_scale {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (z : ℝ) :
    heatKernel1 d τ (Real.sqrt (τ / d) * z) * Real.sqrt (τ / d) = heatKernel1 d (d : ℝ) z := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have ha0 : 0 < τ / (d : ℝ) := by positivity
  have hτa : 2 * Real.pi * τ / d = 2 * Real.pi * (τ / d) := by ring
  have hdd : 2 * Real.pi * (d : ℝ) / d = 2 * Real.pi := by field_simp
  have h1 : (τ / (d : ℝ)) ^ (-(1 : ℝ) / 2) * Real.sqrt (τ / d) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha0]
    norm_num
  have hexp : -(d : ℝ) * (Real.sqrt (τ / d) * z) ^ 2 / (2 * τ) = -(d : ℝ) * z ^ 2 / (2 * d) := by
    rw [mul_pow, Real.sq_sqrt ha0.le]
    field_simp
  unfold heatKernel1
  rw [hτa, hdd, hexp, Real.mul_rpow (by positivity) ha0.le]
  calc (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (τ / (d : ℝ)) ^ (-(1 : ℝ) / 2) *
        Real.exp (-(d : ℝ) * z ^ 2 / (2 * d)) * Real.sqrt (τ / d)
      = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * ((τ / (d : ℝ)) ^ (-(1 : ℝ) / 2) * Real.sqrt (τ / d)) *
        Real.exp (-(d : ℝ) * z ^ 2 / (2 * d)) := by ring
    _ = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(d : ℝ) * z ^ 2 / (2 * d)) := by
        rw [h1]
        ring

theorem heatKernel_scale {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (z : Fin d → ℝ) :
    heatKernel d τ (Real.sqrt (τ / d) • z) * Real.sqrt (τ / d) ^ d = heatKernel d (d : ℝ) z := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [heatKernel_of_pos hτ, heatKernel_of_pos hd']
  have hpow : Real.sqrt (τ / d) ^ d = ∏ _i : Fin d, Real.sqrt (τ / d) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simpa using heatKernel1_scale hd hτ (z i)

theorem integral_heatKernel_mul_eq {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ)
    (G : (Fin d → ℝ) → ℝ) :
    ∫ y : Fin d → ℝ, heatKernel d τ y * G y =
      ∫ z : Fin d → ℝ, heatKernel d (d : ℝ) z * G (Real.sqrt (τ / d) • z) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hσ : 0 < Real.sqrt (τ / d) := Real.sqrt_pos.mpr (by positivity)
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Fin d → ℝ)))
    (fun y : Fin d → ℝ => heatKernel d τ y * G y) (Real.sqrt (τ / d))
  have hfr : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hfr, abs_of_pos (inv_pos.mpr (pow_pos hσ d)), smul_eq_mul] at h
  have h2 : ∫ y : Fin d → ℝ, heatKernel d τ y * G y =
      Real.sqrt (τ / d) ^ d * ∫ z : Fin d → ℝ, heatKernel d τ (Real.sqrt (τ / d) • z) *
        G (Real.sqrt (τ / d) • z) := by
    rw [h]
    field_simp
  rw [h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← heatKernel_scale hd hτ z]
  ring

/-- The heat kernel is an approximate identity as `τ → 0⁺`. -/
theorem tendsto_integral_heatKernel_mul {d : ℕ} (hd : 1 ≤ d) {g : (Fin d → ℝ) → ℝ}
    (hg : Continuous g) (hgb : ∃ M, ∀ x, |g x| ≤ M) (x : Fin d → ℝ) :
    Tendsto (fun τ => ∫ y : Fin d → ℝ, heatKernel d τ y * g (x - y)) (𝓝[>] 0) (𝓝 (g x)) := by
  obtain ⟨M, hM⟩ := hgb
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hΨint : Integrable (heatKernel d (d : ℝ)) := integrable_heatKernel hd hd'
  have hΨ1 : ∫ z, heatKernel d (d : ℝ) z = 1 := integral_heatKernel hd hd'
  have hσ : Tendsto (fun τ : ℝ => Real.sqrt (τ / d)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun τ : ℝ => Real.sqrt (τ / d)) (𝓝 0) (𝓝 (Real.sqrt (0 / d))) :=
      ((continuous_id.div_const _).sqrt).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun τ : ℝ => ∫ z : Fin d → ℝ,
      heatKernel d (d : ℝ) z * g (x - Real.sqrt (τ / d) • z)) (𝓝[>] 0)
      (𝓝 (∫ z : Fin d → ℝ, heatKernel d (d : ℝ) z * g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => heatKernel d (d : ℝ) z * M) ?_ ?_ (hΨint.mul_const M) ?_
    · exact Eventually.of_forall fun τ => (show Continuous (fun z : Fin d → ℝ =>
        heatKernel d (d : ℝ) z * g (x - Real.sqrt (τ / d) • z)) from
        (continuous_heatKernel hd').mul
          (hg.comp (show Continuous (fun z : Fin d → ℝ => x - Real.sqrt (τ / d) • z) by
            fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun τ => Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hd _ _)]
      exact mul_le_mul_of_nonneg_left (hM _) (heatKernel_nonneg hd _ _)
    · refine Eventually.of_forall fun z => ?_
      refine tendsto_const_nhds.mul ?_
      have h1 : Tendsto (fun τ : ℝ => x - Real.sqrt (τ / d) • z) (𝓝[>] 0) (𝓝 (x - (0 : ℝ) • z)) :=
        tendsto_const_nhds.sub (hσ.smul_const z)
      rw [zero_smul, sub_zero] at h1
      exact (hg.tendsto x).comp h1
  have hint : ∫ z : Fin d → ℝ, heatKernel d (d : ℝ) z * g x = g x := by
    rw [integral_mul_const, hΨ1, one_mul]
  rw [hint] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (integral_heatKernel_mul_eq hd hτ (fun y => g (x - y))).symm

end LatticeProb.Heat
