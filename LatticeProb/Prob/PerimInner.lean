import Mathlib

/-!
# Inner (max-coordinate) part of the Gaussian layer bound for orthants

Let `Φ` be the cdf of `gaussianReal 0 1` (`perimPhi`), `φ = gaussianPDFReal 0 1` and
`F(u) = ∏ⱼ Φ(u + hⱼ)` (`perimF`).  This file proves:

* `Φ` is `C^∞`, `Φ' = φ`, `0 < Φ < 1` (`perimPhi_contDiff`, `perimPhi_hasDerivAt`,
  `perimPhi_pos`, `perimPhi_lt_one`);
* the Gaussian hazard bound `φ(x) ≤ (1 + max x 0) · (1 - Φ(x))` (`perim_pdf_le_hazard`);
* `F'(u) = ∑ⱼ φ(u + hⱼ) ∏_{i ≠ j} Φ(u + hᵢ)` (`perimF_hasDerivAt`);
* `F'(u) ≤ (1 + √(2 log m)) + e / √(2π) ≤ 3 + √(2 log m)` (`perimF_deriv_le`,
  `perimF_deriv_le_three`) and the Lipschitz form `F(b) - F(a) ≤ (3 + √(2 log m)) (b - a)`
  (`perimF_sub_le`);
* the probabilistic reading `γ {x | ∀ j, x j ≤ h j + b} = F(b)` and the inner layer bound
  `γ {b-box} \ {a-box} ≤ (3 + √(2 log m)) (b - a)` for `a < b`
  (`perim_stdGaussian_box`, `perim_stdGaussian_inner_layer_le`).
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Real ContDiff

/-- The cumulative distribution function `Φ` of the standard Gaussian. -/
noncomputable def perimPhi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

theorem perim_gaussianPDFReal_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  rw [gaussianPDFReal_def]
  simp

theorem perim_continuous_pdf : Continuous (gaussianPDFReal 0 1) := by
  have : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) :=
    funext perim_gaussianPDFReal_eq
  rw [this]; fun_prop

theorem perimPhi_eq_integral (x : ℝ) :
    perimPhi x = ∫ t in Iic x, gaussianPDFReal 0 1 t := by
  unfold perimPhi
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg fun t => gaussianPDFReal_nonneg 0 1 t)]

theorem perimPhi_eq_add (x : ℝ) :
    perimPhi x = perimPhi 0 + ∫ t in (0 : ℝ)..x, gaussianPDFReal 0 1 t := by
  have hi := integrable_gaussianPDFReal 0 1
  rw [perimPhi_eq_integral, perimPhi_eq_integral,
    ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  ring

theorem perimPhi_hasDerivAt (x : ℝ) : HasDerivAt perimPhi (gaussianPDFReal 0 1 x) x := by
  have h := (perim_continuous_pdf.integral_hasStrictDerivAt 0 x).hasDerivAt
  have h2 := h.const_add (perimPhi 0)
  have : perimPhi = fun y => perimPhi 0 + ∫ t in (0 : ℝ)..y, gaussianPDFReal 0 1 t :=
    funext perimPhi_eq_add
  rw [this]; exact h2


theorem perim_pdf_pos (x : ℝ) : 0 < gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x one_ne_zero

theorem perim_pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hfun : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) :=
    funext perim_gaussianPDFReal_eq
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x := by
    refine (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv ?_
    simp
    ring
  rw [hfun]
  refine (h1.exp.const_mul (√(2 * π))⁻¹).congr_deriv ?_
  ring

theorem perim_pdf_contDiff : ContDiff ℝ ∞ (gaussianPDFReal 0 1) := by
  have : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) :=
    funext perim_gaussianPDFReal_eq
  rw [this]
  fun_prop

theorem perimPhi_deriv (x : ℝ) : deriv perimPhi x = gaussianPDFReal 0 1 x :=
  (perimPhi_hasDerivAt x).deriv

theorem perimPhi_differentiable : Differentiable ℝ perimPhi :=
  fun x => (perimPhi_hasDerivAt x).differentiableAt

theorem perimPhi_contDiff : ContDiff ℝ ∞ perimPhi := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨perimPhi_differentiable, ?_⟩
  have : deriv perimPhi = gaussianPDFReal 0 1 := funext perimPhi_deriv
  rw [this]
  exact perim_pdf_contDiff

theorem perimPhi_strictMono : StrictMono perimPhi :=
  strictMono_of_deriv_pos fun x => by rw [perimPhi_deriv]; exact perim_pdf_pos x

theorem perimPhi_pos (x : ℝ) : 0 < perimPhi x :=
  lt_of_le_of_lt (cdf_nonneg _ _) (perimPhi_strictMono (by linarith : x - 1 < x))

theorem perimPhi_lt_one (x : ℝ) : perimPhi x < 1 :=
  lt_of_lt_of_le (perimPhi_strictMono (by linarith : x < x + 1)) (cdf_le_one _ _)

theorem perimPhi_tendsto_atTop : Tendsto perimPhi atTop (𝓝 1) := tendsto_cdf_atTop _

theorem perimPhi_zero : perimPhi 0 = 1 / 2 := by
  have hi := integrable_gaussianPDFReal 0 1
  have h1 : (∫ t in Iic (0 : ℝ), gaussianPDFReal 0 1 t) +
      (∫ t in (Iic (0 : ℝ))ᶜ, gaussianPDFReal 0 1 t) = 1 :=
    (integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hi).trans
      (integral_gaussianPDFReal_eq_one 0 one_ne_zero)
  rw [compl_Iic] at h1
  have h2 : (∫ t in Ioi (0 : ℝ), gaussianPDFReal 0 1 t) =
      ∫ t in Iic (0 : ℝ), gaussianPDFReal 0 1 t := by
    have := integral_comp_neg_Ioi (0 : ℝ) (gaussianPDFReal 0 1)
    rw [neg_zero] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [perim_gaussianPDFReal_eq, neg_sq]
  rw [perimPhi_eq_integral]
  linarith


/-- The auxiliary function `a ↦ Φ̄(a) - φ(a)/(1+a)` of the hazard bound. -/
noncomputable def perimHaz (a : ℝ) : ℝ := (1 - perimPhi a) - gaussianPDFReal 0 1 a * (1 + a)⁻¹

theorem perimHaz_hasDerivAt {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt perimHaz (-(a * gaussianPDFReal 0 1 a) / (1 + a) ^ 2) a := by
  have h1pos : (1 + a) ≠ 0 := by positivity
  have hd1 : HasDerivAt (fun y : ℝ => 1 + y) 1 a := by
    simpa using (hasDerivAt_id a).const_add 1
  have hinv := hd1.inv h1pos
  have hprod := (perim_pdf_hasDerivAt a).mul hinv
  have hsub := ((perimPhi_hasDerivAt a).const_sub 1).sub hprod
  refine hsub.congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp
  ring

theorem perimHaz_antitoneOn : AntitoneOn perimHaz (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact fun a ha => (perimHaz_hasDerivAt ha).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ici] at ha
    exact (perimHaz_hasDerivAt (le_of_lt ha)).differentiableAt.differentiableWithinAt
  · intro a ha
    rw [interior_Ici] at ha
    rw [(perimHaz_hasDerivAt (le_of_lt ha)).deriv]
    have := perim_pdf_pos a
    have h2 : 0 < (1 + a) ^ 2 := by have : 0 < a := ha; positivity
    have : 0 ≤ a * gaussianPDFReal 0 1 a := by have : 0 < a := ha; positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le

theorem perimHaz_tendsto : Tendsto perimHaz atTop (𝓝 0) := by
  have h1 : Tendsto (fun a => 1 - perimPhi a) atTop (𝓝 0) := by
    simpa using perimPhi_tendsto_atTop.const_sub 1
  have h2 : Tendsto (fun a : ℝ => gaussianPDFReal 0 1 a * (1 + a)⁻¹) atTop (𝓝 0) := by
    have hc : Tendsto (fun a : ℝ => (√(2 * π))⁻¹ * (1 + a)⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun a : ℝ => (1 + a)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
      simpa using this.const_mul (√(2 * π))⁻¹
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with a ha
      have := perim_pdf_pos a
      positivity
    · filter_upwards [eventually_ge_atTop 0] with a ha
      have h1a : 0 < (1 + a)⁻¹ := by positivity
      refine mul_le_mul_of_nonneg_right ?_ h1a.le
      rw [perim_gaussianPDFReal_eq]
      have : Real.exp (-(a ^ 2) / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg a]
      calc (√(2 * π))⁻¹ * Real.exp (-(a ^ 2) / 2) ≤ (√(2 * π))⁻¹ * 1 := by gcongr
        _ = (√(2 * π))⁻¹ := mul_one _
  have h := h1.sub h2
  rw [sub_zero] at h
  exact h

/-- The Gaussian hazard bound for nonnegative arguments. -/
theorem perim_pdf_le_mul_survival_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    gaussianPDFReal 0 1 x ≤ (1 + x) * (1 - perimPhi x) := by
  have h0 : 0 ≤ perimHaz x := by
    refine le_of_tendsto perimHaz_tendsto ?_
    filter_upwards [eventually_ge_atTop x] with a ha
    exact perimHaz_antitoneOn hx (le_trans hx ha) ha
  have h1pos : 0 < 1 + x := by linarith
  unfold perimHaz at h0
  have : gaussianPDFReal 0 1 x * (1 + x)⁻¹ ≤ 1 - perimPhi x := by linarith
  calc gaussianPDFReal 0 1 x = (gaussianPDFReal 0 1 x * (1 + x)⁻¹) * (1 + x) := by
        field_simp
    _ ≤ (1 - perimPhi x) * (1 + x) := by gcongr
    _ = (1 + x) * (1 - perimPhi x) := mul_comm _ _


theorem perim_pdf_le_inv_sqrt (x : ℝ) : gaussianPDFReal 0 1 x ≤ (√(2 * π))⁻¹ := by
  rw [perim_gaussianPDFReal_eq]
  have : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg x]
  calc (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) ≤ (√(2 * π))⁻¹ * 1 := by gcongr
    _ = (√(2 * π))⁻¹ := mul_one _

theorem perim_two_le_sqrt : (2 : ℝ) ≤ √(2 * π) := by
  rw [Real.le_sqrt' (by norm_num)]
  nlinarith [Real.pi_gt_three]

theorem perim_inv_sqrt_le_half : (√(2 * π))⁻¹ ≤ 1 / 2 := by
  have h := perim_two_le_sqrt
  rw [one_div]
  exact inv_anti₀ (by norm_num) h

/-- **Gaussian hazard bound.** `φ(x) ≤ (1 + max x 0) · Φ̄(x)` for every real `x`. -/
theorem perim_pdf_le_hazard (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (1 + max x 0) * (1 - perimPhi x) := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
    exact perim_pdf_le_mul_survival_of_nonneg hx
  · rw [max_eq_right hx]
    have h1 : perimPhi x ≤ 1 / 2 := by
      rw [← perimPhi_zero]; exact perimPhi_strictMono.monotone hx
    have h2 := perim_pdf_le_inv_sqrt x
    have h3 := perim_inv_sqrt_le_half
    linarith


/-- The cdf of the maximum coordinate: `F(u) = ∏ⱼ Φ(u + hⱼ)`. -/
noncomputable def perimF {m : ℕ} (h : Fin m → ℝ) (u : ℝ) : ℝ := ∏ j, perimPhi (u + h j)

/-- The derivative of `F`: `F'(u) = ∑ⱼ φ(u + hⱼ) ∏_{i ≠ j} Φ(u + hᵢ)`. -/
theorem perimF_hasDerivAt {m : ℕ} (h : Fin m → ℝ) (u : ℝ) :
    HasDerivAt (perimF h)
      (∑ j, gaussianPDFReal 0 1 (u + h j) * ∏ i ∈ Finset.univ.erase j, perimPhi (u + h i)) u := by
  classical
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun v => perimPhi (v + h j)) (gaussianPDFReal 0 1 (u + h j)) u := by
    intro j _
    have := (perimPhi_hasDerivAt (u + h j)).comp_add_const u (h j)
    simpa using this
  have := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin m))) hj
  refine this.congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]

theorem perimF_deriv {m : ℕ} (h : Fin m → ℝ) (u : ℝ) :
    deriv (perimF h) u =
      ∑ j, gaussianPDFReal 0 1 (u + h j) * ∏ i ∈ Finset.univ.erase j, perimPhi (u + h i) :=
  (perimF_hasDerivAt h u).deriv

theorem perimF_differentiable {m : ℕ} (h : Fin m → ℝ) : Differentiable ℝ (perimF h) :=
  fun u => (perimF_hasDerivAt h u).differentiableAt


theorem perimPhi_one_sub_nonneg (x : ℝ) : 0 ≤ 1 - perimPhi x := by
  linarith [perimPhi_lt_one x]

theorem perimPhi_one_sub_le_one (x : ℝ) : 1 - perimPhi x ≤ 1 := by
  linarith [perimPhi_pos x]

theorem perimPhi_le_exp (x : ℝ) : perimPhi x ≤ Real.exp (-(1 - perimPhi x)) := by
  have := Real.add_one_le_exp (-(1 - perimPhi x))
  linarith

theorem perim_prod_erase_le {m : ℕ} (h : Fin m → ℝ) (u : ℝ) (j : Fin m) :
    ∏ i ∈ Finset.univ.erase j, perimPhi (u + h i) ≤
      Real.exp (1 - ∑ i, (1 - perimPhi (u + h i))) := by
  classical
  have h1 : ∏ i ∈ Finset.univ.erase j, perimPhi (u + h i) ≤
      ∏ i ∈ Finset.univ.erase j, Real.exp (-(1 - perimPhi (u + h i))) :=
    Finset.prod_le_prod (fun i _ => (perimPhi_pos _).le) (fun i _ => perimPhi_le_exp _)
  rw [← Real.exp_sum] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => 1 - perimPhi (u + h i))
    (Finset.mem_univ j)
  rw [Finset.sum_neg_distrib]
  have h3 := perimPhi_one_sub_le_one (u + h j)
  linarith

theorem perim_pdf_le_of_nonneg_le {τ a : ℝ} (hτ : 0 ≤ τ) (hτa : τ ≤ a) :
    gaussianPDFReal 0 1 a ≤ gaussianPDFReal 0 1 τ := by
  rw [perim_gaussianPDFReal_eq, perim_gaussianPDFReal_eq]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  nlinarith

theorem perim_pdf_le_split {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (1 + τ) * (1 - perimPhi x) + gaussianPDFReal 0 1 τ := by
  have hτ0 := perim_pdf_pos τ
  have hS := perimPhi_one_sub_nonneg x
  rcases le_or_gt x τ with hx | hx
  · have h1 := perim_pdf_le_hazard x
    have h2 : (1 + max x 0) ≤ 1 + τ := by
      have : max x 0 ≤ τ := max_le hx hτ
      linarith
    have h3 : (1 + max x 0) * (1 - perimPhi x) ≤ (1 + τ) * (1 - perimPhi x) :=
      mul_le_mul_of_nonneg_right h2 hS
    linarith
  · have h1 := perim_pdf_le_of_nonneg_le hτ hx.le
    have h2 : 0 ≤ (1 + τ) * (1 - perimPhi x) := by positivity
    linarith

/-- The derivative bound for a general threshold `τ ≥ 0`. -/
theorem perimF_deriv_le_general {m : ℕ} (h : Fin m → ℝ) (u : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    deriv (perimF h) u ≤ (1 + τ) + Real.exp 1 * (m * gaussianPDFReal 0 1 τ) := by
  classical
  set T : ℝ := ∑ i, (1 - perimPhi (u + h i)) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => perimPhi_one_sub_nonneg _
  have hτ0 := perim_pdf_pos τ
  have hA : deriv (perimF h) u ≤ Real.exp (1 - T) * ∑ j, gaussianPDFReal 0 1 (u + h j) := by
    rw [perimF_deriv, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm (Real.exp (1 - T))]
    exact mul_le_mul_of_nonneg_left (perim_prod_erase_le h u j) (perim_pdf_pos _).le
  have hC : ∑ j, gaussianPDFReal 0 1 (u + h j) ≤ (1 + τ) * T + m * gaussianPDFReal 0 1 τ := by
    calc ∑ j, gaussianPDFReal 0 1 (u + h j)
        ≤ ∑ j, ((1 + τ) * (1 - perimPhi (u + h j)) + gaussianPDFReal 0 1 τ) :=
          Finset.sum_le_sum fun j _ => perim_pdf_le_split hτ _
      _ = (1 + τ) * T + m * gaussianPDFReal 0 1 τ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
  have hE0 : 0 < Real.exp (1 - T) := Real.exp_pos _
  have hD1 : Real.exp (1 - T) * T ≤ 1 := by
    have h1 : T ≤ Real.exp (T - 1) := by
      have := Real.add_one_le_exp (T - 1); linarith
    calc Real.exp (1 - T) * T ≤ Real.exp (1 - T) * Real.exp (T - 1) :=
          mul_le_mul_of_nonneg_left h1 hE0.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hD2 : Real.exp (1 - T) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  calc deriv (perimF h) u ≤ Real.exp (1 - T) * ∑ j, gaussianPDFReal 0 1 (u + h j) := hA
    _ ≤ Real.exp (1 - T) * ((1 + τ) * T + m * gaussianPDFReal 0 1 τ) :=
        mul_le_mul_of_nonneg_left hC hE0.le
    _ = (1 + τ) * (Real.exp (1 - T) * T) + (m * gaussianPDFReal 0 1 τ) * Real.exp (1 - T) := by
        ring
    _ ≤ (1 + τ) * 1 + (m * gaussianPDFReal 0 1 τ) * Real.exp 1 := by
        gcongr
    _ = (1 + τ) + Real.exp 1 * (m * gaussianPDFReal 0 1 τ) := by ring


theorem perim_mul_pdf_sqrt_log_le (m : ℕ) :
    (m : ℝ) * gaussianPDFReal 0 1 (√(2 * Real.log m)) ≤ (√(2 * π))⁻¹ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < m := by linarith
    have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1
    have hsq : (√(2 * Real.log m)) ^ 2 = 2 * Real.log m := Real.sq_sqrt (by positivity)
    rw [perim_gaussianPDFReal_eq, hsq]
    have : Real.exp (-(2 * Real.log m) / 2) = (m : ℝ)⁻¹ := by
      rw [show -(2 * Real.log m) / 2 = -Real.log m by ring, Real.exp_neg, Real.exp_log hmpos]
    rw [this]
    field_simp
    exact le_rfl

/-- **Theorem IN (derivative form).**  For every `m`, `h` and `u`,
`F'(u) ≤ (1 + √(2 log m)) + e / √(2π)`. -/
theorem perimF_deriv_le {m : ℕ} (h : Fin m → ℝ) (u : ℝ) :
    deriv (perimF h) u ≤ (1 + √(2 * Real.log m)) + Real.exp 1 * (√(2 * π))⁻¹ := by
  have h1 := perimF_deriv_le_general h u (Real.sqrt_nonneg (2 * Real.log m))
  have h2 := perim_mul_pdf_sqrt_log_le m
  have h3 : Real.exp 1 * ((m : ℝ) * gaussianPDFReal 0 1 (√(2 * Real.log m))) ≤
      Real.exp 1 * (√(2 * π))⁻¹ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
  linarith

theorem perim_exp_one_mul_inv_sqrt_le : Real.exp 1 * (√(2 * π))⁻¹ ≤ 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := perim_inv_sqrt_le_half
  have h3 : (0 : ℝ) ≤ (√(2 * π))⁻¹ := by positivity
  calc Real.exp 1 * (√(2 * π))⁻¹ ≤ 2.7182818286 * (1 / 2) := by
        apply mul_le_mul h1.le h2 h3 (by norm_num)
    _ ≤ 2 := by norm_num

/-- **Theorem IN (derivative form, clean constant).** `F'(u) ≤ 3 + √(2 log m)`. -/
theorem perimF_deriv_le_three {m : ℕ} (h : Fin m → ℝ) (u : ℝ) :
    deriv (perimF h) u ≤ 3 + √(2 * Real.log m) := by
  have := perimF_deriv_le h u
  have := perim_exp_one_mul_inv_sqrt_le
  linarith

/-- **Theorem IN (Lipschitz form).**  For `a ≤ b`, `F(b) - F(a) ≤ (3 + √(2 log m)) (b - a)`. -/
theorem perimF_sub_le {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a ≤ b) :
    perimF h b - perimF h a ≤ (3 + √(2 * Real.log m)) * (b - a) :=
  image_sub_le_mul_sub_of_deriv_le (perimF_differentiable h) (perimF_deriv_le_three h) hab


/-- The same Lipschitz bound with the threshold `max m 2` of the packet statement. -/
theorem perimF_sub_le_max {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a ≤ b) :
    perimF h b - perimF h a ≤ (3 + √(2 * Real.log (max m 2 : ℕ))) * (b - a) := by
  refine (perimF_sub_le h hab).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr hab)
  have hlog : Real.log m ≤ Real.log (max m 2 : ℕ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast le_max_left m 2)
  have := Real.sqrt_le_sqrt (by linarith : 2 * Real.log m ≤ 2 * Real.log (max m 2 : ℕ))
  linarith

/-- The set `{x | ∀ j, x j ≤ h j + b}` of the product space is the box `∏ⱼ (-∞, hⱼ + b]`. -/
theorem perim_pi_box_eq {m : ℕ} (h : Fin m → ℝ) (b : ℝ) :
    {x : Fin m → ℝ | ∀ j, x j ≤ h j + b} = Set.pi Set.univ fun j => Iic (h j + b) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]

theorem perim_pi_box_measurableSet {m : ℕ} (h : Fin m → ℝ) (b : ℝ) :
    MeasurableSet {x : Fin m → ℝ | ∀ j, x j ≤ h j + b} := by
  rw [perim_pi_box_eq]
  exact MeasurableSet.univ_pi fun j => measurableSet_Iic

/-- **Probabilistic reading of `F`** (product Gaussian measure): the standard Gaussian measure of
the box `{x | ∀ j, x j ≤ h j + b}` is `F(b)`. -/
theorem perim_pi_box {m : ℕ} (h : Fin m → ℝ) (b : ℝ) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1) {x | ∀ j, x j ≤ h j + b} =
      ENNReal.ofReal (perimF h b) := by
  rw [perim_pi_box_eq, Measure.pi_pi]
  unfold perimF
  rw [ENNReal.ofReal_prod_of_nonneg fun j _ => (perimPhi_pos _).le]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← ofReal_cdf (gaussianReal 0 1) (h j + b), add_comm]
  rfl

theorem perim_euclid_box_measurableSet {m : ℕ} (h : Fin m → ℝ) (b : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin m) | ∀ j, x j ≤ h j + b} := by
  have : {x : EuclideanSpace ℝ (Fin m) | ∀ j, x j ≤ h j + b} =
      ⋂ j, {x : EuclideanSpace ℝ (Fin m) | x j ≤ h j + b} := by
    ext x; simp
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_le (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable measurable_const

/-- **Probabilistic reading of `F`** (standard Gaussian on `EuclideanSpace ℝ (Fin m)`):
for every real `b` (in particular for `b ≤ 0`),
`γ {x | ∀ j, x j ≤ h j + b} = F(b)`. -/
theorem perim_stdGaussian_box {m : ℕ} (h : Fin m → ℝ) (b : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | ∀ j, x j ≤ h j + b} =
      ENNReal.ofReal (perimF h b) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
    (perim_euclid_box_measurableSet h b)]
  exact perim_pi_box h b


theorem perim_sdiff_le_of_values {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B : Set α}
    (hAB : A ⊆ B) (hA : MeasurableSet A) {x y c : ℝ} (hy0 : 0 ≤ y)
    (hA' : μ A = ENNReal.ofReal y) (hB : μ B = ENNReal.ofReal x) (hc : x - y ≤ c) :
    μ (B \ A) ≤ ENNReal.ofReal c := by
  rw [measure_sdiff hAB hA.nullMeasurableSet (by rw [hA']; exact ENNReal.ofReal_ne_top),
    hA', hB, ← ENNReal.ofReal_sub x hy0]
  exact ENNReal.ofReal_le_ofReal hc

theorem perim_box_subset {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a ≤ b) :
    {x : Fin m → ℝ | ∀ j, x j ≤ h j + a} ⊆ {x | ∀ j, x j ≤ h j + b} :=
  fun _ hx j => (hx j).trans (by linarith)

theorem perim_euclid_box_subset {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a ≤ b) :
    {x : EuclideanSpace ℝ (Fin m) | ∀ j, x j ≤ h j + a} ⊆ {x | ∀ j, x j ≤ h j + b} :=
  fun _ hx j => (hx j).trans (by linarith)

theorem perimF_nonneg {m : ℕ} (h : Fin m → ℝ) (u : ℝ) : 0 ≤ perimF h u :=
  Finset.prod_nonneg fun _ _ => (perimPhi_pos _).le

theorem perimF_le_one {m : ℕ} (h : Fin m → ℝ) (u : ℝ) : perimF h u ≤ 1 :=
  Finset.prod_le_one (fun _ _ => (perimPhi_pos _).le) fun _ _ => (perimPhi_lt_one _).le

/-- **Inner-layer bound (product Gaussian measure).**  For `a < b` (no sign condition), the
Gaussian mass of the layer between the boxes `{x ≤ h + a}` and `{x ≤ h + b}` is at most
`(3 + √(2 log m)) (b - a)`. -/
theorem perim_pi_inner_layer_le {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a < b) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        ({x | ∀ j, x j ≤ h j + b} \ {x | ∀ j, x j ≤ h j + a}) ≤
      ENNReal.ofReal ((3 + √(2 * Real.log m)) * (b - a)) :=
  perim_sdiff_le_of_values (perim_box_subset h hab.le) (perim_pi_box_measurableSet h a)
    (perimF_nonneg h a) (perim_pi_box h a) (perim_pi_box h b) (perimF_sub_le h hab.le)

/-- **Inner-layer bound (standard Gaussian on `EuclideanSpace ℝ (Fin m)`).**  For `a < b`
(no sign condition), `γ {x | ∀ j, x j ≤ h j + b} - γ {x | ∀ j, x j ≤ h j + a}` is at most
`(3 + √(2 log m)) (b - a)`, written as the mass of the layer between the two boxes. -/
theorem perim_stdGaussian_inner_layer_le {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m))
        ({x | ∀ j, x j ≤ h j + b} \ {x | ∀ j, x j ≤ h j + a}) ≤
      ENNReal.ofReal ((3 + √(2 * Real.log m)) * (b - a)) :=
  perim_sdiff_le_of_values (perim_euclid_box_subset h hab.le)
    (perim_euclid_box_measurableSet h a) (perimF_nonneg h a) (perim_stdGaussian_box h a)
    (perim_stdGaussian_box h b) (perimF_sub_le h hab.le)

/-- The same inner-layer bound in the subtractive form `γ(B_b) ≤ γ(B_a) + L (b - a)`. -/
theorem perim_stdGaussian_box_le_add {m : ℕ} (h : Fin m → ℝ) {a b : ℝ} (hab : a < b) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {x | ∀ j, x j ≤ h j + b} ≤
      stdGaussian (EuclideanSpace ℝ (Fin m)) {x | ∀ j, x j ≤ h j + a} +
        ENNReal.ofReal ((3 + √(2 * Real.log m)) * (b - a)) := by
  rw [perim_stdGaussian_box, perim_stdGaussian_box,
    ← ENNReal.ofReal_add (perimF_nonneg h a)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hab.le))]
  exact ENNReal.ofReal_le_ofReal (by linarith [perimF_sub_le h hab.le])

end LatticeProb
