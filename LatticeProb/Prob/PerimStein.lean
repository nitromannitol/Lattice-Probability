import Mathlib

namespace LatticeProb

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ### The one-dimensional Stein lemma on a half line -/

/-- The standard Gaussian density in closed form. -/
theorem perim_phi_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- The derivative of the standard Gaussian density: `φ'(z) = -z φ(z)`. -/
theorem perim_hasDerivAt_phi (z : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-z * gaussianPDFReal 0 1 z) z := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-z) z := by
    have := (hasDerivAt_pow 2 z).const_mul (-1 / 2 : ℝ)
    have h' : (fun y : ℝ => -y ^ 2 / 2) = fun y => (-1 / 2) * y ^ 2 := by
      funext y; ring
    rw [h']
    refine this.congr_deriv ?_
    norm_num
    ring
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) :=
    funext perim_phi_eq
  rw [this]
  refine h2.congr_deriv ?_
  beta_reduce
  ring


/-- Pointwise domination of a polynomially weighted Gaussian density. -/
theorem perim_pow_phi_le (k : ℕ) (z : ℝ) :
    (1 + |z|) ^ k * gaussianPDFReal 0 1 z ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (2 ^ (k - 1) *
      (Real.exp (-(1 / 2) * z ^ 2) + |z| ^ k * Real.exp (-(1 / 2) * z ^ 2))) := by
  have hφ : gaussianPDFReal 0 1 z
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * z ^ 2) := by
    rw [perim_phi_eq]; congr 2; ring
  rw [hφ]
  have := add_pow_le (zero_le_one' ℝ) (abs_nonneg z) k
  rw [one_pow] at this
  have hE := Real.exp_pos (-(1 / 2) * z ^ 2)
  have hs : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  calc (1 + |z|) ^ k * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * z ^ 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * ((1 + |z|) ^ k * Real.exp (-(1 / 2) * z ^ 2)) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * ((2 ^ (k - 1) * (1 + |z| ^ k))
          * Real.exp (-(1 / 2) * z ^ 2)) := by gcongr
    _ = _ := by ring

/-- Polynomially weighted Gaussian densities are integrable. -/
theorem perim_integrable_pow_phi (k : ℕ) :
    Integrable (fun z : ℝ => (1 + |z|) ^ k * gaussianPDFReal 0 1 z) := by
  have h1 : Integrable (fun z : ℝ => Real.exp (-(1 / 2) * z ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have h2 : Integrable (fun z : ℝ => |z| ^ k * Real.exp (-(1 / 2) * z ^ 2)) := by
    have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (k : ℝ))
      (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)).norm
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, Real.rpow_natCast, abs_pow]
  have h3 := ((h1.add h2).const_mul ((2 : ℝ) ^ (k - 1))).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  refine h3.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((by fun_prop : Measurable fun z : ℝ => (1 + |z|) ^ k)).aestronglyMeasurable.mul
      (measurable_gaussianPDFReal 0 1).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _))]
    exact perim_pow_phi_le k z

/-- Polynomially weighted Gaussian densities vanish at `+∞`. -/
theorem perim_tendsto_pow_phi (k : ℕ) :
    Tendsto (fun z : ℝ => (1 + |z|) ^ k * gaussianPDFReal 0 1 z) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => Real.exp (-(1 / 2) * z ^ 2)) atTop (𝓝 0) := by
    have := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1 / 2) (by norm_num) 0
    simp only [Real.rpow_zero, one_mul] at this
    exact this.mono_left atTop_le_cocompact
  have h2 : Tendsto (fun z : ℝ => |z| ^ k * Real.exp (-(1 / 2) * z ^ 2)) atTop (𝓝 0) := by
    have := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1 / 2) (by norm_num) (k : ℝ)
    simp only [Real.rpow_natCast] at this
    exact this.mono_left atTop_le_cocompact
  have h3 := ((h1.add h2).const_mul ((2 : ℝ) ^ (k - 1))).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [add_zero, mul_zero, mul_zero] at h3
  refine squeeze_zero (fun z => ?_) (fun z => perim_pow_phi_le k z) ?_
  · exact mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _)
  · simpa using h3

/-- Integrability on a measurable set from a polynomial-times-Gaussian bound. -/
theorem perim_integrableOn_of_bound {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s)) {B : ℝ} {k : ℕ}
    (hb : ∀ z ∈ s, |f z| ≤ B * ((1 + |z|) ^ k * gaussianPDFReal 0 1 z)) :
    IntegrableOn f s := by
  refine Integrable.mono' (((perim_integrable_pow_phi k).const_mul B).integrableOn) hf ?_
  filter_upwards [ae_restrict_mem hs] with z hz
  rw [Real.norm_eq_abs]
  exact hb z hz

/-- `|z - h| ≤ (2 + |h|) (1 + |z|)`. -/
theorem perim_abs_sub_le (h z : ℝ) : |z - h| ≤ (2 + |h|) * (1 + |z|) := by
  have h1 : |z - h| ≤ |z| + |h| := abs_sub z h
  have h2 : 0 ≤ |z| := abs_nonneg z
  have h3 : 0 ≤ |h| := abs_nonneg h
  nlinarith

/-- **One-dimensional half-line Stein lemma (L1).**  For `H` differentiable on `(h, ∞)`,
continuous at `h` from the right, with `H` and `H'` of polynomial growth,
`∫_{z>h} (z (z - h) - 1) H(z) φ(z) dz = ∫_{z>h} (z - h) H'(z) φ(z) dz`. -/
theorem perim_stein_half_line {h : ℝ} {H H' : ℝ → ℝ}
    (hd : ∀ z, h < z → HasDerivAt H (H' z) z) (hH'm : Measurable H')
    (h0 : ContinuousWithinAt H (Ici h) h) {C : ℝ} {k : ℕ}
    (hH : ∀ z, h < z → |H z| ≤ C * (1 + |z|) ^ k)
    (hH' : ∀ z, h < z → |H' z| ≤ C * (1 + |z|) ^ k) :
    ∫ z in Ioi h, (z * (z - h) - 1) * H z * gaussianPDFReal 0 1 z
      = ∫ z in Ioi h, (z - h) * H' z * gaussianPDFReal 0 1 z := by
  set φ : ℝ → ℝ := gaussianPDFReal 0 1 with hφdef
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => gaussianPDFReal_nonneg _ _ _
  have hφc : Continuous φ :=
    continuous_iff_continuousAt.2 fun z => (perim_hasDerivAt_phi z).continuousAt
  have hHc : ContinuousOn H (Ioi h) := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  set A : ℝ := 2 + |h| with hA
  have hA0 : 0 ≤ A := by positivity
  have hC0 : 0 ≤ C := by
    have := hH (h + 1) (by linarith)
    have h2 : 0 < (1 + |h + 1|) ^ k := by positivity
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg (H (h + 1))]
  -- bounds
  have hb1 : ∀ z ∈ Ioi h, |H z * φ z| ≤ C * ((1 + |z|) ^ k * φ z) := by
    intro z hz
    rw [abs_mul, abs_of_nonneg (hφ0 z)]
    calc |H z| * φ z ≤ (C * (1 + |z|) ^ k) * φ z :=
          mul_le_mul_of_nonneg_right (hH z hz) (hφ0 z)
      _ = _ := by ring
  have hb2 : ∀ z ∈ Ioi h, |(z - h) * H' z * φ z| ≤ (A * C) * ((1 + |z|) ^ (k + 1) * φ z) := by
    intro z hz
    rw [abs_mul, abs_mul, abs_of_nonneg (hφ0 z)]
    have h1 := perim_abs_sub_le h z
    have h2 := hH' z hz
    calc |z - h| * |H' z| * φ z ≤ (A * (1 + |z|)) * (C * (1 + |z|) ^ k) * φ z :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (hφ0 z)
      _ = _ := by ring
  have hb3 : ∀ z ∈ Ioi h, |(z * (z - h)) * H z * φ z|
      ≤ (A * C) * ((1 + |z|) ^ (k + 2) * φ z) := by
    intro z hz
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hφ0 z)]
    have h1 := perim_abs_sub_le h z
    have h2 := hH z hz
    have h3 : |z| ≤ 1 + |z| := by linarith
    calc |z| * |z - h| * |H z| * φ z
        ≤ ((1 + |z|) * (A * (1 + |z|))) * (C * (1 + |z|) ^ k) * φ z :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h3 h1 (abs_nonneg _) (by positivity))
            h2 (abs_nonneg _) (by positivity)) (hφ0 z)
      _ = _ := by ring
  -- integrability
  have hiH : IntegrableOn (fun z => H z * φ z) (Ioi h) :=
    perim_integrableOn_of_bound measurableSet_Ioi
      ((hHc.mul hφc.continuousOn).aestronglyMeasurable measurableSet_Ioi) hb1
  have hiH' : IntegrableOn (fun z => (z - h) * H' z * φ z) (Ioi h) :=
    perim_integrableOn_of_bound measurableSet_Ioi
      ((((measurable_id.sub_const h).mul hH'm).mul
        (measurable_gaussianPDFReal 0 1)).aestronglyMeasurable) hb2
  have hiG : IntegrableOn (fun z => (z * (z - h)) * H z * φ z) (Ioi h) :=
    perim_integrableOn_of_bound measurableSet_Ioi
      ((((continuous_id.mul (continuous_id.sub continuous_const)).continuousOn.mul hHc).mul
        hφc.continuousOn).aestronglyMeasurable measurableSet_Ioi) hb3
  -- integration by parts
  have hu : ∀ z ∈ Ioi h, HasDerivAt (fun z => (z - h) * H z) (H z + (z - h) * H' z) z := by
    intro z hz
    have := ((hasDerivAt_id z).sub_const h).mul (hd z hz)
    exact this.congr_deriv (by simp)
  have hv : ∀ z ∈ Ioi h, HasDerivAt (fun z => -φ z) (z * φ z) z := by
    intro z _
    have := (perim_hasDerivAt_phi z).neg
    exact this.congr_deriv (by rw [hφdef]; ring)
  have hzero : Tendsto ((fun z => (z - h) * H z) * (fun z => -φ z)) (𝓝[>] h) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ => z - h) (𝓝[>] h) (𝓝 0) := by
      have : Tendsto (fun z : ℝ => z - h) (𝓝 h) (𝓝 (h - h)) :=
        (continuous_id.sub continuous_const).tendsto h
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[>] h) (𝓝 (H h)) :=
      h0.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h3 : Tendsto (fun z => -φ z) (𝓝[>] h) (𝓝 (-φ h)) :=
      (hφc.neg.tendsto h).mono_left nhdsWithin_le_nhds
    have h4 := (h1.mul h2).mul h3
    rw [zero_mul, zero_mul] at h4
    exact h4
  have hinf : Tendsto ((fun z => (z - h) * H z) * (fun z => -φ z)) atTop (𝓝 0) := by
    have hlim := (perim_tendsto_pow_phi (k + 1)).const_mul (A * C)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop h] with z hz
    rw [Real.norm_eq_abs]
    simp only [Pi.mul_apply]
    rw [mul_neg, abs_neg, abs_mul, abs_mul, abs_of_nonneg (hφ0 z)]
    have h1 := perim_abs_sub_le h z
    have h2 := hH z hz
    calc |z - h| * |H z| * φ z ≤ (A * (1 + |z|)) * (C * (1 + |z|) ^ k) * φ z :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) (hφ0 z)
      _ = _ := by ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := h) (a' := 0) (b' := 0) hu hv
    (by
      have : (fun z => (z - h) * H z) * (fun z => z * φ z)
          = fun z => (z * (z - h)) * H z * φ z := by funext z; simp only [Pi.mul_apply]; ring
      rw [this]; exact hiG)
    (by
      have : (fun z => H z + (z - h) * H' z) * (fun z => -φ z)
          = fun z => -(H z * φ z) - (z - h) * H' z * φ z := by
        funext z; simp only [Pi.mul_apply]; ring
      rw [this]; exact (hiH.neg).sub hiH')
    hzero hinf
  have e1 : ∫ z in Ioi h, (z * (z - h) - 1) * H z * φ z
      = ∫ z in Ioi h, ((z * (z - h)) * H z * φ z - H z * φ z) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
    ring
  rw [e1, integral_sub hiG hiH]
  have e2 : ∫ x in Ioi h, (x - h) * H x * (x * φ x) = ∫ z in Ioi h, z * (z - h) * H z * φ z := by
    refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
    ring
  have e3 : ∫ x in Ioi h, (H x + (x - h) * H' x) * -φ x
      = -(∫ z in Ioi h, H z * φ z) - ∫ z in Ioi h, (z - h) * H' z * φ z := by
    have : ∀ x, (H x + (x - h) * H' x) * -φ x = -(H x * φ x) - (x - h) * H' x * φ x :=
      fun x => by ring
    simp_rw [this]
    have hneg : IntegrableOn (fun x => -(H x * φ x)) (Ioi h) := hiH.neg
    rw [integral_sub hneg hiH', integral_neg]
  rw [e2, e3] at hibp
  linarith


/-- **Gaussian form of (L1).**  The same identity with integrals against `gaussianReal 0 1`. -/
theorem perim_stein_gauss {h : ℝ} {H H' : ℝ → ℝ}
    (hd : ∀ z, h < z → HasDerivAt H (H' z) z) (hH'm : Measurable H')
    (h0 : ContinuousWithinAt H (Ici h) h) {C : ℝ} {k : ℕ}
    (hH : ∀ z, h < z → |H z| ≤ C * (1 + |z|) ^ k)
    (hH' : ∀ z, h < z → |H' z| ≤ C * (1 + |z|) ^ k) :
    ∫ z, (if h < z then (z * (z - h) - 1) * H z else 0) ∂(gaussianReal 0 1)
      = ∫ z, (if h < z then (z - h) * H' z else 0) ∂(gaussianReal 0 1) := by
  have key := perim_stein_half_line hd hH'm h0 hH hH'
  have conv : ∀ g : ℝ → ℝ, ∫ z, (if h < z then g z else 0) ∂(gaussianReal 0 1)
      = ∫ z in Ioi h, g z * gaussianPDFReal 0 1 z := by
    intro g
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : h < z
    · simp [hz, mul_comm]
    · simp [hz]
  rw [conv (fun z => (z * (z - h) - 1) * H z), conv (fun z => (z - h) * H' z)]
  exact key

/-- Integration over the product, splitting off coordinate `j`. -/
theorem perim_integral_split {n : ℕ} (j : Fin (n + 1)) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) :
    ∫ x, f x ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
      = ∫ y, ∫ z, f (Function.update (j.insertNth 0 y) j z) ∂(gaussianReal 0 1)
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) j
  have hmp' := hmp.symm
  rw [← hmp'.integral_comp' f]
  have hint : Integrable (fun w => f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ)
      j).symm w)) ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
    hmp'.integrable_comp_of_integrable hf
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]


/-! ### Polynomial growth on the Gaussian product -/

/-- Integrability of a function against `gaussianReal 0 1` from the Lebesgue integrability of the
function times the density. -/
theorem perim_integrable_pow_gaussianReal (q : ℕ) :
    Integrable (fun z : ℝ => (1 + |z|) ^ q) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  refine (perim_integrable_pow_phi q).congr (Eventually.of_forall fun z => ?_)
  simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), mul_comm]

section Weights

variable {m : ℕ}

/-- The polynomial weight `∏ᵢ (1 + |xᵢ|)^q`. -/
noncomputable def perimW (q : ℕ) (x : Fin m → ℝ) : ℝ := ∏ i, (1 + |x i|) ^ q

theorem perimW_pos (q : ℕ) (x : Fin m → ℝ) : 0 < perimW q x :=
  Finset.prod_pos fun i _ => by positivity

theorem perimW_one_le (q : ℕ) (x : Fin m → ℝ) : 1 ≤ perimW q x := by
  unfold perimW
  calc (1 : ℝ) = ∏ _i : Fin m, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ =>
        one_le_pow₀ (by linarith [abs_nonneg (x i)])

theorem perimW_zero (x : Fin m → ℝ) : perimW 0 x = 1 := by simp [perimW]

theorem perimW_add (q r : ℕ) (x : Fin m → ℝ) :
    perimW (q + r) x = perimW q x * perimW r x := by
  simp [perimW, pow_add, Finset.prod_mul_distrib]

theorem perimW_mono {q r : ℕ} (hqr : q ≤ r) (x : Fin m → ℝ) : perimW q x ≤ perimW r x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqr
  rw [perimW_add]
  have := perimW_one_le d x
  have := perimW_pos q x
  nlinarith

theorem perimW_update (q : ℕ) (x : Fin m → ℝ) (j : Fin m) (z : ℝ) :
    perimW q (Function.update x j z)
      = (1 + |z|) ^ q * ∏ i ∈ Finset.univ.erase j, (1 + |x i|) ^ q := by
  unfold perimW
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem perimW_coord_le (x : Fin m → ℝ) (i : Fin m) : 1 + |x i| ≤ perimW 1 x := by
  have h1 := perimW_update 1 x i (x i)
  rw [Function.update_eq_self] at h1
  rw [h1, pow_one]
  have : 1 ≤ ∏ i ∈ Finset.univ.erase i, (1 + |x i|) ^ 1 :=
    calc (1 : ℝ) = ∏ _i ∈ Finset.univ.erase i, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun k _ =>
          one_le_pow₀ (by linarith [abs_nonneg (x k)])
  nlinarith [abs_nonneg (x i)]

theorem perimW_integrable (q : ℕ) :
    Integrable (perimW (m := m) q) (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
  Integrable.fintype_prod (f := fun _ z => (1 + |z|) ^ q)
    (fun _ => perim_integrable_pow_gaussianReal q)

theorem perimW_measurable (q : ℕ) : Measurable (perimW (m := m) q) := by
  unfold perimW
  fun_prop

end Weights


section Poly

variable {m : ℕ}

/-- `F` has polynomial growth of degree `q` in the sense `|F x| ≤ C ∏ᵢ (1 + |xᵢ|)^q`. -/
def PerimPoly (q : ℕ) (F : (Fin m → ℝ) → ℝ) : Prop := ∃ C : ℝ, ∀ x, |F x| ≤ C * perimW q x

theorem PerimPoly.mono {q r : ℕ} (hqr : q ≤ r) {F : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F) :
    PerimPoly r F := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨|C|, fun x => (hC x).trans ?_⟩
  calc C * perimW q x ≤ |C| * perimW q x :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (perimW_pos q x).le
    _ ≤ |C| * perimW r x :=
        mul_le_mul_of_nonneg_left (perimW_mono hqr x) (abs_nonneg C)

theorem PerimPoly.of_abs_le {q : ℕ} {F G : (Fin m → ℝ) → ℝ} (hG : PerimPoly q G)
    (h : ∀ x, |F x| ≤ |G x|) : PerimPoly q F := by
  obtain ⟨C, hC⟩ := hG
  exact ⟨C, fun x => (h x).trans (hC x)⟩

theorem PerimPoly.add {q : ℕ} {F G : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F) (hG : PerimPoly q G) :
    PerimPoly q (fun x => F x + G x) := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨D, hD⟩ := hG
  exact ⟨C + D, fun x => (abs_add_le _ _).trans (by rw [add_mul]; exact add_le_add (hC x) (hD x))⟩

theorem PerimPoly.neg {q : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F) :
    PerimPoly q (fun x => -F x) := by
  obtain ⟨C, hC⟩ := hF
  exact ⟨C, fun x => by rw [abs_neg]; exact hC x⟩

theorem PerimPoly.sub {q : ℕ} {F G : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F) (hG : PerimPoly q G) :
    PerimPoly q (fun x => F x - G x) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem PerimPoly.const_mul {q : ℕ} {F : (Fin m → ℝ) → ℝ} (c : ℝ) (hF : PerimPoly q F) :
    PerimPoly q (fun x => c * F x) := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨|c| * C, fun x => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

theorem PerimPoly.mul {q r : ℕ} {F G : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F)
    (hG : PerimPoly r G) : PerimPoly (q + r) (fun x => F x * G x) := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨D, hD⟩ := hG
  refine ⟨C * D, fun x => ?_⟩
  rw [abs_mul, perimW_add]
  calc |F x| * |G x| ≤ (C * perimW q x) * (D * perimW r x) :=
        mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
    _ = _ := by ring

theorem PerimPoly.sum {q : ℕ} {ι : Type*} (s : Finset ι) {F : ι → (Fin m → ℝ) → ℝ}
    (hF : ∀ i ∈ s, PerimPoly q (F i)) : PerimPoly q (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using h1.add h2

theorem perimPoly_bdd {F : (Fin m → ℝ) → ℝ} {B : ℝ} (h : ∀ x, |F x| ≤ B) : PerimPoly 0 F :=
  ⟨B, fun x => by rw [perimW_zero, mul_one]; exact h x⟩

theorem perimPoly_const (c : ℝ) : PerimPoly (m := m) 0 (fun _ => c) :=
  perimPoly_bdd (B := |c|) fun _ => le_rfl

theorem perimPoly_coord (i : Fin m) : PerimPoly 1 (fun x : Fin m → ℝ => x i) :=
  ⟨1, fun x => by
    have := perimW_coord_le x i
    rw [one_mul]
    linarith [abs_nonneg (x i)]⟩

theorem PerimPoly.integrable {q : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F)
    (hm : AEStronglyMeasurable F (Measure.pi fun _ : Fin m => gaussianReal 0 1)) :
    Integrable F (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  obtain ⟨C, hC⟩ := hF
  refine ((perimW_integrable q).const_mul C).mono' hm (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hC x

end Poly


/-! ### The functionals `p_j`, `N²`, `k`, `g_j`, `V` -/

section Defs

variable {m : ℕ}

/-- `p_j(x) = (x_j - h_j)₊`. -/
noncomputable def perimP (h : Fin m → ℝ) (j : Fin m) (x : Fin m → ℝ) : ℝ := max (x j - h j) 0

/-- `N²(x) = ∑ⱼ p_j(x)²`. -/
noncomputable def perimN2 (h : Fin m → ℝ) (x : Fin m → ℝ) : ℝ := ∑ j, perimP h j x ^ 2

/-- `k(x) = #{j | h_j < x_j}`. -/
noncomputable def perimK (h : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ((Finset.univ.filter fun j => h j < x j).card : ℝ)

/-- `g_j(x) = 1{h_j < x_j} (x_j p_j(x) - 1)`. -/
noncomputable def perimG (h : Fin m → ℝ) (j : Fin m) (x : Fin m → ℝ) : ℝ :=
  if h j < x j then x j * perimP h j x - 1 else 0

/-- `V(x) = ∑ⱼ g_j(x)`. -/
noncomputable def perimV (h : Fin m → ℝ) (x : Fin m → ℝ) : ℝ := ∑ j, perimG h j x

/-- `⟨h, p⟩`. -/
noncomputable def perimHP (h : Fin m → ℝ) (x : Fin m → ℝ) : ℝ := ∑ j, h j * perimP h j x

theorem perimP_nonneg (h : Fin m → ℝ) (j : Fin m) (x : Fin m → ℝ) : 0 ≤ perimP h j x :=
  le_max_right _ _

theorem perimN2_nonneg (h : Fin m → ℝ) (x : Fin m → ℝ) : 0 ≤ perimN2 h x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem perimP_of_lt (h : Fin m → ℝ) (j : Fin m) {x : Fin m → ℝ} (hx : h j < x j) :
    perimP h j x = x j - h j := max_eq_left (by linarith)

theorem perimP_of_le (h : Fin m → ℝ) (j : Fin m) {x : Fin m → ℝ} (hx : x j ≤ h j) :
    perimP h j x = 0 := max_eq_right (by linarith)

theorem perimK_eq (h : Fin m → ℝ) (x : Fin m → ℝ) :
    perimK h x = ∑ j, if h j < x j then (1 : ℝ) else 0 := by
  unfold perimK
  rw [Finset.card_filter]
  push_cast
  rfl

theorem perimP_measurable (h : Fin m → ℝ) (j : Fin m) : Measurable (perimP h j) := by
  unfold perimP
  fun_prop

theorem perimN2_measurable (h : Fin m → ℝ) : Measurable (perimN2 h) := by
  unfold perimN2
  exact Finset.measurable_sum _ fun j _ => (perimP_measurable h j).pow_const 2

theorem perimG_measurable (h : Fin m → ℝ) (j : Fin m) : Measurable (perimG h j) := by
  unfold perimG
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
    (((measurable_pi_apply j).mul (perimP_measurable h j)).sub_const 1) measurable_const

theorem perimV_measurable (h : Fin m → ℝ) : Measurable (perimV h) := by
  unfold perimV
  exact Finset.measurable_sum _ fun j _ => perimG_measurable h j

theorem perimHP_measurable (h : Fin m → ℝ) : Measurable (perimHP h) := by
  unfold perimHP
  exact Finset.measurable_sum _ fun j _ => (perimP_measurable h j).const_mul _

theorem perimK_measurable (h : Fin m → ℝ) : Measurable (perimK h) := by
  have : perimK h = fun x => ∑ j, if h j < x j then (1 : ℝ) else 0 := funext (perimK_eq h)
  rw [this]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
      measurable_const measurable_const

/-- `V = N² + ⟨h, p⟩ - k`, pointwise. -/
theorem perimV_eq (h : Fin m → ℝ) (x : Fin m → ℝ) :
    perimV h x = perimN2 h x + perimHP h x - perimK h x := by
  rw [perimK_eq]
  unfold perimV perimN2 perimHP
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold perimG
  by_cases hj : h j < x j
  · rw [if_pos hj, if_pos hj, perimP_of_lt h j hj]; ring
  · rw [if_neg hj, if_neg hj, perimP_of_le h j (not_lt.mp hj)]; ring

theorem perimP_poly (h : Fin m → ℝ) (j : Fin m) : PerimPoly 1 (perimP h j) := by
  refine ⟨1 + |h j|, fun x => ?_⟩
  have h1 := perimW_coord_le x j
  have h2 : |perimP h j x| ≤ |x j - h j| := by
    unfold perimP
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have h3 : |x j - h j| ≤ |x j| + |h j| := abs_sub _ _
  have h4 := abs_nonneg (x j)
  have h5 := abs_nonneg (h j)
  have h6 := perimW_pos 1 x
  nlinarith

theorem perimN2_poly (h : Fin m → ℝ) : PerimPoly 2 (perimN2 h) := by
  unfold perimN2
  refine PerimPoly.sum _ fun j _ => ?_
  have := (perimP_poly h j).mul (perimP_poly h j)
  simpa [sq] using this

theorem perimG_poly (h : Fin m → ℝ) (j : Fin m) : PerimPoly 2 (perimG h j) := by
  have h1 : PerimPoly 2 (fun x : Fin m → ℝ => x j * perimP h j x - 1) :=
    (((perimPoly_coord j).mul (perimP_poly h j)).sub
      ((perimPoly_const (m := m) 1).mono (Nat.zero_le 2)))
  refine h1.of_abs_le fun x => ?_
  unfold perimG
  split_ifs
  · exact le_rfl
  · simp

theorem perimV_poly (h : Fin m → ℝ) : PerimPoly 2 (perimV h) := by
  unfold perimV
  exact PerimPoly.sum _ fun j _ => perimG_poly h j

theorem perimHP_poly (h : Fin m → ℝ) : PerimPoly 1 (perimHP h) := by
  unfold perimHP
  exact PerimPoly.sum _ fun j _ => (perimP_poly h j).const_mul _

theorem perimK_poly (h : Fin m → ℝ) : PerimPoly 0 (perimK h) := by
  refine perimPoly_bdd (B := m) fun x => ?_
  unfold perimK
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

end Defs


/-! ### Coordinatewise integration by parts on the product space -/

/-- **Coordinate Stein identity.**  Integration by parts in the coordinate `j` against the
Gaussian, on the half space `{h_j < x_j}`. -/
theorem perim_coord_stein {m : ℕ} (h : Fin m → ℝ) (j : Fin m) {F F' : (Fin m → ℝ) → ℝ}
    (hFm : Measurable F) (hF'm : Measurable F')
    (hd : ∀ x z, h j < z →
      HasDerivAt (fun t => F (Function.update x j t)) (F' (Function.update x j z)) z)
    (hc : ∀ x, ContinuousWithinAt (fun t => F (Function.update x j t)) (Ici (h j)) (h j))
    {q : ℕ} (hF : PerimPoly q F) (hF' : PerimPoly q F') :
    ∫ x, (if h j < x j then (x j * (x j - h j) - 1) * F x else 0)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∫ x, (if h j < x j then (x j - h j) * F' x else 0)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  cases m with
  | zero => exact j.elim0
  | succ n =>
    obtain ⟨C₁, hC₁⟩ := hF
    obtain ⟨C₂, hC₂⟩ := hF'
    have hq1 : PerimPoly 2 (fun x : Fin (n + 1) → ℝ => x j * (x j - h j) - 1) := by
      have := ((perimPoly_coord j).mul
        ((perimPoly_coord j).sub ((perimPoly_const (m := n + 1) (h j)).mono (Nat.zero_le 1)))).sub
        ((perimPoly_const (m := n + 1) 1).mono (Nat.zero_le 2))
      simpa using this
    have hq2 : PerimPoly 1 (fun x : Fin (n + 1) → ℝ => x j - h j) :=
      (perimPoly_coord j).sub ((perimPoly_const (m := n + 1) (h j)).mono (Nat.zero_le 1))
    have hI1 : Integrable (fun x : Fin (n + 1) → ℝ =>
        if h j < x j then (x j * (x j - h j) - 1) * F x else 0)
        (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
      have hp := hq1.mul ⟨C₁, hC₁⟩
      refine (hp.of_abs_le (fun x => ?_)).integrable ?_
      · split_ifs
        · exact le_rfl
        · rw [abs_zero]; positivity
      · refine Measurable.aestronglyMeasurable ?_
        exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
          ((((measurable_pi_apply j).mul ((measurable_pi_apply j).sub_const _)).sub_const 1).mul
            hFm) measurable_const
    have hI2 : Integrable (fun x : Fin (n + 1) → ℝ =>
        if h j < x j then (x j - h j) * F' x else 0)
        (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
      have hp := hq2.mul ⟨C₂, hC₂⟩
      refine (hp.of_abs_le (fun x => ?_)).integrable ?_
      · split_ifs
        · exact le_rfl
        · rw [abs_zero]; positivity
      · refine Measurable.aestronglyMeasurable ?_
        exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
          (((measurable_pi_apply j).sub_const _).mul hF'm) measurable_const
    rw [perim_integral_split j hI1, perim_integral_split j hI2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    set x₀ : Fin (n + 1) → ℝ := j.insertNth (0 : ℝ) y with hx₀
    set E : ℝ := ∏ i ∈ Finset.univ.erase j, (1 + |x₀ i|) ^ q with hE
    have hE0 : 0 < E := Finset.prod_pos fun i _ => by positivity
    set Cm : ℝ := max C₁ C₂ with hCm
    have hbound : ∀ (G : (Fin (n + 1) → ℝ) → ℝ) (C : ℝ), C ≤ Cm →
        (∀ x, |G x| ≤ C * perimW q x) → ∀ z, |G (Function.update x₀ j z)|
          ≤ (Cm * E) * (1 + |z|) ^ q := by
      intro G C hC hG z
      refine (hG _).trans ?_
      rw [perimW_update]
      have hz : 0 < (1 + |z|) ^ q * E := by positivity
      calc C * ((1 + |z|) ^ q * E) ≤ Cm * ((1 + |z|) ^ q * E) :=
            mul_le_mul_of_nonneg_right hC hz.le
        _ = _ := by ring
    have key := perim_stein_gauss (h := h j) (H := fun t => F (Function.update x₀ j t))
      (H' := fun t => F' (Function.update x₀ j t)) (hd x₀)
      (hF'm.comp (measurable_update x₀)) (hc x₀) (C := Cm * E) (k := q)
      (fun z _ => hbound F C₁ (le_max_left _ _) hC₁ z)
      (fun z _ => hbound F' C₂ (le_max_right _ _) hC₂ z)
    simpa [hx₀] using key


/-! ### Effect of changing one coordinate -/

section Update

variable {m : ℕ}

theorem perimP_update_self (h x : Fin m → ℝ) (j : Fin m) (t : ℝ) :
    perimP h j (Function.update x j t) = max (t - h j) 0 := by
  simp [perimP]

theorem perimP_update_ne (h x : Fin m → ℝ) {i j : Fin m} (hij : i ≠ j) (t : ℝ) :
    perimP h i (Function.update x j t) = perimP h i x := by
  simp [perimP, Function.update_of_ne hij]

theorem perimN2_update (h x : Fin m → ℝ) (j : Fin m) (t : ℝ) :
    perimN2 h (Function.update x j t)
      = max (t - h j) 0 ^ 2 + ∑ i ∈ Finset.univ.erase j, perimP h i x ^ 2 := by
  unfold perimN2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), perimP_update_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [perimP_update_ne h x (Finset.ne_of_mem_erase hi)]

theorem perimN2_continuous_update (h x : Fin m → ℝ) (j : Fin m) :
    Continuous fun t => perimN2 h (Function.update x j t) := by
  have : (fun t => perimN2 h (Function.update x j t))
      = fun t => max (t - h j) 0 ^ 2 + ∑ i ∈ Finset.univ.erase j, perimP h i x ^ 2 :=
    funext (perimN2_update h x j)
  rw [this]
  fun_prop

theorem perimN2_hasDerivAt_update (h x : Fin m → ℝ) (j : Fin m) {z : ℝ} (hz : h j < z) :
    HasDerivAt (fun t => perimN2 h (Function.update x j t)) (2 * (z - h j)) z := by
  set c : ℝ := ∑ i ∈ Finset.univ.erase j, perimP h i x ^ 2
  have h1 : HasDerivAt (fun t : ℝ => (t - h j) ^ 2 + c) (2 * (z - h j)) z := by
    have := (((hasDerivAt_id z).sub_const (h j)).pow 2).add_const c
    exact this.congr_deriv (by simp)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hz] with t ht
  rw [perimN2_update]
  have : max (t - h j) 0 = t - h j := max_eq_left (by simp only [mem_Ioi] at ht; linarith)
  rw [this]

/-- `V` with the `j`-th summand removed. -/
noncomputable def perimVm (h : Fin m → ℝ) (j : Fin m) (x : Fin m → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, perimG h i x

theorem perimV_split (h : Fin m → ℝ) (j : Fin m) (x : Fin m → ℝ) :
    perimV h x = perimVm h j x + perimG h j x := by
  unfold perimV perimVm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]

theorem perimVm_update (h x : Fin m → ℝ) (j : Fin m) (t : ℝ) :
    perimVm h j (Function.update x j t) = perimVm h j x := by
  unfold perimVm
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij := Finset.ne_of_mem_erase hi
  unfold perimG
  rw [Function.update_of_ne hij, perimP_update_ne h x hij]

theorem perimVm_measurable (h : Fin m → ℝ) (j : Fin m) : Measurable (perimVm h j) := by
  unfold perimVm
  exact Finset.measurable_sum _ fun i _ => perimG_measurable h i

theorem perimVm_poly (h : Fin m → ℝ) (j : Fin m) : PerimPoly 2 (perimVm h j) := by
  unfold perimVm
  exact PerimPoly.sum _ fun i _ => perimG_poly h i

end Update


/-! ### (G1): `E[Ξ(N²) V] = 2 E[N² Ξ'(N²)]` -/

section G1

variable {m : ℕ}

/-- Integrability of a product of two measurable functions of polynomial growth. -/
theorem perim_integrable_mul {q r : ℕ} {F G : (Fin m → ℝ) → ℝ} (hF : PerimPoly q F)
    (hG : PerimPoly r G) (hFm : Measurable F) (hGm : Measurable G) :
    Integrable (fun x => F x * G x) (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
  (hF.mul hG).integrable (hFm.mul hGm).aestronglyMeasurable

/-- The per-coordinate identity of (G1): `E[g_j Ξ(N²)] = 2 E[p_j² Ξ'(N²)]`. -/
theorem perim_G1_coord (h : Fin m → ℝ) (j : Fin m) {Ξ Ξ' : ℝ → ℝ}
    (hΞ : ∀ y, HasDerivAt Ξ (Ξ' y) y) (hΞ' : Continuous Ξ') {B : ℝ}
    (hB : ∀ y, 0 ≤ y → |Ξ y| ≤ B ∧ |Ξ' y| ≤ B) :
    ∫ x, perimG h j x * Ξ (perimN2 h x) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = 2 * ∫ x, perimP h j x ^ 2 * Ξ' (perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun y => (hΞ y).continuousAt
  have hFm : Measurable fun x => Ξ (perimN2 h x) := hΞc.measurable.comp (perimN2_measurable h)
  have hΞ'm : Measurable fun x => Ξ' (perimN2 h x) := hΞ'.measurable.comp (perimN2_measurable h)
  have hFp : PerimPoly 0 fun x => Ξ (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).1
  have hΞ'p : PerimPoly 0 fun x => Ξ' (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).2
  have hF'p : PerimPoly 1 fun x => 2 * perimP h j x * Ξ' (perimN2 h x) := by
    have := ((perimP_poly h j).const_mul 2).mul hΞ'p
    simpa using this
  have hF'm : Measurable fun x => 2 * perimP h j x * Ξ' (perimN2 h x) :=
    ((perimP_measurable h j).const_mul 2).mul hΞ'm
  have key := perim_coord_stein h j (F := fun x => Ξ (perimN2 h x))
    (F' := fun x => 2 * perimP h j x * Ξ' (perimN2 h x)) hFm hF'm
    (fun x z hz => by
      have h1 := perimN2_hasDerivAt_update h x j hz
      have h2 := (hΞ (perimN2 h (Function.update x j z))).comp z h1
      refine h2.congr_deriv ?_
      rw [perimP_update_self, max_eq_left (by linarith)]
      ring)
    (fun x => ((hΞc.comp (perimN2_continuous_update h x j)).continuousAt).continuousWithinAt)
    (hFp.mono (Nat.zero_le 1)) hF'p
  have e1 : ∀ x : Fin m → ℝ, (if h j < x j then (x j * (x j - h j) - 1) * Ξ (perimN2 h x) else 0)
      = perimG h j x * Ξ (perimN2 h x) := by
    intro x
    unfold perimG
    by_cases hj : h j < x j
    · rw [if_pos hj, if_pos hj, perimP_of_lt h j hj]
    · rw [if_neg hj, if_neg hj, zero_mul]
  have e2 : ∀ x : Fin m → ℝ,
      (if h j < x j then (x j - h j) * (2 * perimP h j x * Ξ' (perimN2 h x)) else 0)
      = 2 * (perimP h j x ^ 2 * Ξ' (perimN2 h x)) := by
    intro x
    by_cases hj : h j < x j
    · rw [if_pos hj, perimP_of_lt h j hj]; ring
    · rw [if_neg hj, perimP_of_le h j (not_lt.mp hj)]; ring
  simp_rw [e1, e2] at key
  rw [key, integral_const_mul]

/-- **(G1).**  For `Ξ ∈ C¹` with `Ξ`, `Ξ'` bounded on `[0, ∞)`:
`E[Ξ(N²) V] = 2 E[N² Ξ'(N²)]` under the standard Gaussian product measure. -/
theorem perim_G1 (h : Fin m → ℝ) {Ξ Ξ' : ℝ → ℝ}
    (hΞ : ∀ y, HasDerivAt Ξ (Ξ' y) y) (hΞ' : Continuous Ξ') {B : ℝ}
    (hB : ∀ y, 0 ≤ y → |Ξ y| ≤ B ∧ |Ξ' y| ≤ B) :
    ∫ x, Ξ (perimN2 h x) * perimV h x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = 2 * ∫ x, perimN2 h x * Ξ' (perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun y => (hΞ y).continuousAt
  have hFm : Measurable fun x => Ξ (perimN2 h x) := hΞc.measurable.comp (perimN2_measurable h)
  have hΞ'm : Measurable fun x => Ξ' (perimN2 h x) := hΞ'.measurable.comp (perimN2_measurable h)
  have hFp : PerimPoly 0 fun x => Ξ (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).1
  have hΞ'p : PerimPoly 0 fun x => Ξ' (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).2
  have hI1 : ∀ j ∈ Finset.univ, Integrable (fun x => perimG h j x * Ξ (perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun j _ => by
    have := perim_integrable_mul (perimG_poly h j) hFp (perimG_measurable h j) hFm
    exact this
  have hI2 : ∀ j ∈ Finset.univ, Integrable (fun x => perimP h j x ^ 2 * Ξ' (perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun j _ => by
    have hp : PerimPoly 2 fun x => perimP h j x ^ 2 := by
      simpa [sq] using (perimP_poly h j).mul (perimP_poly h j)
    exact perim_integrable_mul hp hΞ'p ((perimP_measurable h j).pow_const 2) hΞ'm
  have e1 : (fun x => Ξ (perimN2 h x) * perimV h x)
      = fun x => ∑ j, perimG h j x * Ξ (perimN2 h x) := by
    funext x
    unfold perimV
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : (fun x => perimN2 h x * Ξ' (perimN2 h x))
      = fun x => ∑ j, perimP h j x ^ 2 * Ξ' (perimN2 h x) := by
    funext x
    unfold perimN2
    rw [Finset.sum_mul]
  rw [e1, e2, integral_finsetSum _ hI1, integral_finsetSum _ hI2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => perim_G1_coord h j hΞ hΞ' hB

end G1

/-! ### (G2): the second-moment identity -/

section G2

variable {m : ℕ}

/-- The per-coordinate identity of (G2):
`E[g_j V Ξ(N²)] = E[(2 p_j² + h_j p_j) Ξ(N²)] + 2 E[p_j² Ξ'(N²) V]`. -/
theorem perim_G2_coord (h : Fin m → ℝ) (j : Fin m) {Ξ Ξ' : ℝ → ℝ}
    (hΞ : ∀ y, HasDerivAt Ξ (Ξ' y) y) (hΞ' : Continuous Ξ') {B : ℝ}
    (hB : ∀ y, 0 ≤ y → |Ξ y| ≤ B ∧ |Ξ' y| ≤ B) :
    ∫ x, perimG h j x * perimV h x * Ξ (perimN2 h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∫ x, (2 * perimP h j x ^ 2 + h j * perimP h j x) * Ξ (perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimP h j x ^ 2 * Ξ' (perimN2 h x) * perimV h x
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun y => (hΞ y).continuousAt
  have hΞm : Measurable fun x => Ξ (perimN2 h x) := hΞc.measurable.comp (perimN2_measurable h)
  have hΞ'm : Measurable fun x => Ξ' (perimN2 h x) := hΞ'.measurable.comp (perimN2_measurable h)
  have hΞp : PerimPoly 0 fun x => Ξ (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).1
  have hΞ'p : PerimPoly 0 fun x => Ξ' (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).2
  -- the bracket `V_{-j} + x_j (x_j - h_j) - 1`
  have hbr : PerimPoly 2 fun x : Fin m → ℝ =>
      perimVm h j x + x j * (x j - h j) - 1 := by
    have h1 : PerimPoly 2 fun x : Fin m → ℝ => x j * (x j - h j) := by
      have := (perimPoly_coord j).mul
        ((perimPoly_coord j).sub ((perimPoly_const (m := m) (h j)).mono (Nat.zero_le 1)))
      simpa using this
    exact ((perimVm_poly h j).add h1).sub ((perimPoly_const (m := m) 1).mono (Nat.zero_le 2))
  have hbrm : Measurable fun x : Fin m → ℝ => perimVm h j x + x j * (x j - h j) - 1 :=
    (((perimVm_measurable h j).add
      ((measurable_pi_apply j).mul ((measurable_pi_apply j).sub_const _))).sub_const 1)
  set F : (Fin m → ℝ) → ℝ := fun x =>
    (perimVm h j x + x j * (x j - h j) - 1) * Ξ (perimN2 h x) with hF
  set F' : (Fin m → ℝ) → ℝ := fun x =>
    (2 * x j - h j) * Ξ (perimN2 h x)
      + (perimVm h j x + x j * (x j - h j) - 1) * (2 * perimP h j x * Ξ' (perimN2 h x))
    with hF'
  have hFp : PerimPoly (2 + 0) F := hbr.mul hΞp
  have hFm : Measurable F := hbrm.mul hΞm
  have hF'p : PerimPoly 3 F' := by
    have h1 : PerimPoly (1 + 0) fun x : Fin m → ℝ => (2 * x j - h j) * Ξ (perimN2 h x) := by
      refine PerimPoly.mul ?_ hΞp
      exact ((perimPoly_coord j).const_mul 2).sub
        ((perimPoly_const (m := m) (h j)).mono (Nat.zero_le 1))
    have h2 : PerimPoly (2 + (1 + 0)) fun x : Fin m → ℝ =>
        (perimVm h j x + x j * (x j - h j) - 1) * (2 * perimP h j x * Ξ' (perimN2 h x)) := by
      refine hbr.mul ?_
      have := ((perimP_poly h j).const_mul 2).mul hΞ'p
      simpa using this
    exact (h1.mono (by norm_num)).add (h2.mono (by norm_num))
  have hF'm : Measurable F' :=
    ((((measurable_pi_apply j).const_mul 2).sub_const _).mul hΞm).add
      (hbrm.mul (((perimP_measurable h j).const_mul 2).mul hΞ'm))
  have key := perim_coord_stein h j (F := F) (F' := F') hFm hF'm
    (fun x z hz => by
      have hf : (fun t => F (Function.update x j t))
          = fun t => (perimVm h j x + t * (t - h j) - 1)
              * Ξ (perimN2 h (Function.update x j t)) := by
        funext t
        simp [hF, perimVm_update]
      rw [hf]
      have h1 : HasDerivAt (fun t : ℝ => perimVm h j x + t * (t - h j) - 1) (2 * z - h j) z := by
        have := ((((hasDerivAt_id z).mul ((hasDerivAt_id z).sub_const (h j))).const_add
          (perimVm h j x)).sub_const 1)
        exact this.congr_deriv (by simp; ring)
      have h2 := perimN2_hasDerivAt_update h x j hz
      have h3 := (hΞ (perimN2 h (Function.update x j z))).comp z h2
      have h4 := h1.mul h3
      refine h4.congr_deriv ?_
      simp only [hF', perimVm_update, Function.update_self, perimP_update_self,
        Function.comp_apply]
      rw [max_eq_left (by linarith)]
      ring)
    (fun x => by
      have hf : (fun t => F (Function.update x j t))
          = fun t => (perimVm h j x + t * (t - h j) - 1)
              * Ξ (perimN2 h (Function.update x j t)) := by
        funext t
        simp [hF, perimVm_update]
      rw [hf]
      exact (Continuous.mul (by fun_prop)
        (hΞc.comp (perimN2_continuous_update h x j))).continuousAt.continuousWithinAt)
    (hFp.mono (by norm_num)) hF'p
  have hG : ∀ x : Fin m → ℝ, h j < x j → perimG h j x = x j * (x j - h j) - 1 := fun x hj => by
    unfold perimG
    rw [if_pos hj, perimP_of_lt h j hj]
  have e1 : ∀ x : Fin m → ℝ,
      (if h j < x j then (x j * (x j - h j) - 1) * F x else 0)
      = perimG h j x * perimV h x * Ξ (perimN2 h x) := by
    intro x
    by_cases hj : h j < x j
    · rw [if_pos hj, perimV_split h j x, hG x hj]
      simp only [hF]
      ring
    · have : perimG h j x = 0 := by unfold perimG; rw [if_neg hj]
      rw [if_neg hj, this]
      ring
  have e2 : ∀ x : Fin m → ℝ,
      (if h j < x j then (x j - h j) * F' x else 0)
      = (2 * perimP h j x ^ 2 + h j * perimP h j x) * Ξ (perimN2 h x)
        + 2 * (perimP h j x ^ 2 * Ξ' (perimN2 h x) * perimV h x) := by
    intro x
    by_cases hj : h j < x j
    · rw [if_pos hj, perimV_split h j x, hG x hj]
      simp only [hF']
      rw [perimP_of_lt h j hj]
      ring
    · rw [if_neg hj, perimP_of_le h j (not_lt.mp hj)]
      ring
  simp_rw [e1, e2] at key
  have hp2 : PerimPoly 2 fun x : Fin m → ℝ => perimP h j x ^ 2 := by
    simpa [sq] using (perimP_poly h j).mul (perimP_poly h j)
  have hIa : Integrable (fun x => (2 * perimP h j x ^ 2 + h j * perimP h j x) * Ξ (perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hq : PerimPoly 2 fun x => 2 * perimP h j x ^ 2 + h j * perimP h j x :=
      (hp2.const_mul 2).add (((perimP_poly h j).const_mul (h j)).mono (by norm_num))
    exact perim_integrable_mul hq hΞp
      (((perimP_measurable h j).pow_const 2).const_mul 2 |>.add
        ((perimP_measurable h j).const_mul (h j))) hΞm
  have hIb : Integrable (fun x => perimP h j x ^ 2 * Ξ' (perimN2 h x) * perimV h x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hq : PerimPoly (2 + 0) fun x => perimP h j x ^ 2 * Ξ' (perimN2 h x) := hp2.mul hΞ'p
    exact perim_integrable_mul hq (perimV_poly h)
      (((perimP_measurable h j).pow_const 2).mul hΞ'm) (perimV_measurable h)
  rw [key, integral_add hIa (hIb.const_mul 2), integral_const_mul]

theorem perimP_sq_poly (h : Fin m → ℝ) (j : Fin m) :
    PerimPoly 2 fun x : Fin m → ℝ => perimP h j x ^ 2 := by
  simpa [sq] using (perimP_poly h j).mul (perimP_poly h j)

/-- **(G2).**  For `Ξ ∈ C¹` with `Ξ`, `Ξ'` bounded on `[0, ∞)`:
`E[V² Ξ(N²)] = E[Ξ(N²) (2 N² + ⟨h, p⟩)] + 2 E[N² Ξ'(N²) V]`. -/
theorem perim_G2 (h : Fin m → ℝ) {Ξ Ξ' : ℝ → ℝ}
    (hΞ : ∀ y, HasDerivAt Ξ (Ξ' y) y) (hΞ' : Continuous Ξ') {B : ℝ}
    (hB : ∀ y, 0 ≤ y → |Ξ y| ≤ B ∧ |Ξ' y| ≤ B) :
    ∫ x, perimV h x ^ 2 * Ξ (perimN2 h x) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∫ x, Ξ (perimN2 h x) * (2 * perimN2 h x + perimHP h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimN2 h x * Ξ' (perimN2 h x) * perimV h x
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun y => (hΞ y).continuousAt
  have hΞm : Measurable fun x => Ξ (perimN2 h x) := hΞc.measurable.comp (perimN2_measurable h)
  have hΞ'm : Measurable fun x => Ξ' (perimN2 h x) := hΞ'.measurable.comp (perimN2_measurable h)
  have hΞp : PerimPoly 0 fun x => Ξ (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).1
  have hΞ'p : PerimPoly 0 fun x => Ξ' (perimN2 h x) :=
    perimPoly_bdd (B := B) fun x => (hB _ (perimN2_nonneg h x)).2
  have hIa : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun x => perimG h j x * perimV h x * Ξ (perimN2 h x))
        (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun j _ => by
    have hq : PerimPoly (2 + 2) fun x => perimG h j x * perimV h x :=
      (perimG_poly h j).mul (perimV_poly h)
    exact perim_integrable_mul hq hΞp ((perimG_measurable h j).mul (perimV_measurable h)) hΞm
  have hIb : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun x => (2 * perimP h j x ^ 2 + h j * perimP h j x) * Ξ (perimN2 h x))
        (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun j _ => by
    have hq : PerimPoly 2 fun x => 2 * perimP h j x ^ 2 + h j * perimP h j x :=
      ((perimP_sq_poly h j).const_mul 2).add
        (((perimP_poly h j).const_mul (h j)).mono (by norm_num))
    exact perim_integrable_mul hq hΞp
      ((((perimP_measurable h j).pow_const 2).const_mul 2).add
        ((perimP_measurable h j).const_mul (h j))) hΞm
  have hIc : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun x => perimP h j x ^ 2 * Ξ' (perimN2 h x) * perimV h x)
        (Measure.pi fun _ : Fin m => gaussianReal 0 1) := fun j _ => by
    have hq : PerimPoly (2 + 0) fun x => perimP h j x ^ 2 * Ξ' (perimN2 h x) :=
      (perimP_sq_poly h j).mul hΞ'p
    exact perim_integrable_mul hq (perimV_poly h)
      (((perimP_measurable h j).pow_const 2).mul hΞ'm) (perimV_measurable h)
  have e1 : (fun x => perimV h x ^ 2 * Ξ (perimN2 h x))
      = fun x => ∑ j, perimG h j x * perimV h x * Ξ (perimN2 h x) := by
    funext x
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    unfold perimV
    ring
  have e2 : (fun x => Ξ (perimN2 h x) * (2 * perimN2 h x + perimHP h x))
      = fun x => ∑ j, (2 * perimP h j x ^ 2 + h j * perimP h j x) * Ξ (perimN2 h x) := by
    funext x
    rw [← Finset.sum_mul]
    unfold perimN2 perimHP
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have e3 : (fun x => perimN2 h x * Ξ' (perimN2 h x) * perimV h x)
      = fun x => ∑ j, perimP h j x ^ 2 * Ξ' (perimN2 h x) * perimV h x := by
    funext x
    rw [← Finset.sum_mul]
    unfold perimN2
    rw [Finset.sum_mul]
  rw [e1, e2, e3, integral_finsetSum _ hIa, integral_finsetSum _ hIb, integral_finsetSum _ hIc,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => perim_G2_coord h j hΞ hΞ' hB

/-- (G1) in the literal `ContDiff ℝ 1` form, with `Ξ` and `Ξ'` globally bounded. -/
theorem perim_G1_contDiff (h : Fin m → ℝ) {Ξ : ℝ → ℝ} (hΞ : ContDiff ℝ 1 Ξ) {B : ℝ}
    (hB : ∀ y, |Ξ y| ≤ B ∧ |deriv Ξ y| ≤ B) :
    ∫ x, Ξ (perimN2 h x) * perimV h x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = 2 * ∫ x, perimN2 h x * deriv Ξ (perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have h1 := contDiff_one_iff_deriv.1 hΞ
  exact perim_G1 h (fun y => (h1.1 y).hasDerivAt) h1.2 (fun y _ => hB y)

/-- (G2) in the literal `ContDiff ℝ 1` form, with `Ξ` and `Ξ'` globally bounded. -/
theorem perim_G2_contDiff (h : Fin m → ℝ) {Ξ : ℝ → ℝ} (hΞ : ContDiff ℝ 1 Ξ) {B : ℝ}
    (hB : ∀ y, |Ξ y| ≤ B ∧ |deriv Ξ y| ≤ B) :
    ∫ x, perimV h x ^ 2 * Ξ (perimN2 h x) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∫ x, Ξ (perimN2 h x) * (2 * perimN2 h x + perimHP h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimN2 h x * deriv Ξ (perimN2 h x) * perimV h x
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have h1 := contDiff_one_iff_deriv.1 hΞ
  exact perim_G2 h (fun y => (h1.1 y).hasDerivAt) h1.2 (fun y _ => hB y)

end G2

/-! ### (G3): the exponential test function -/

section G3

variable {m : ℕ}

/-- The exponential test function is `C¹` with the derivative `-λ e^{-λ y}`. -/
theorem perim_exp_hasDerivAt (lam y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-lam * y)) (-lam * Real.exp (-lam * y)) y := by
  have := ((hasDerivAt_id y).const_mul (-lam)).exp
  exact this.congr_deriv (by simp; ring)

theorem perim_exp_bound {lam : ℝ} (hlam : 0 < lam) (y : ℝ) (hy : 0 ≤ y) :
    |Real.exp (-lam * y)| ≤ 1 + lam ∧ |-lam * Real.exp (-lam * y)| ≤ 1 + lam := by
  have h1 : Real.exp (-lam * y) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h2 := Real.exp_pos (-lam * y)
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos h2]; linarith
  · rw [abs_mul, abs_neg, abs_of_pos hlam, abs_of_pos h2]
    nlinarith

/-- **(G3).**  For `λ > 0` and `w = e^{-λ N²}`:
`E[V w] = -2λ E[N² w]` and
`E[V² w] ≤ 2 E[k w] + 2 E[N² w] + 4 E[(λ N²)² w]`. -/
theorem perim_G3 (h : Fin m → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ∫ x, perimV h x * Real.exp (-lam * perimN2 h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = -2 * lam * ∫ x, perimN2 h x * Real.exp (-lam * perimN2 h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) ∧
    ∫ x, perimV h x ^ 2 * Real.exp (-lam * perimN2 h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ 2 * ∫ x, perimK h x * Real.exp (-lam * perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 2 * ∫ x, perimN2 h x * Real.exp (-lam * perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + 4 * ∫ x, (lam * perimN2 h x) ^ 2 * Real.exp (-lam * perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hΞ := perim_exp_hasDerivAt lam
  have hΞ' : Continuous fun y : ℝ => -lam * Real.exp (-lam * y) := by fun_prop
  have hB := fun y hy => perim_exp_bound hlam y hy
  have hN2m := perimN2_measurable h
  have hwm : Measurable fun x => Real.exp (-lam * perimN2 h x) := by
    have : Measurable fun x => -lam * perimN2 h x := hN2m.const_mul _
    exact this.exp
  have hwp : PerimPoly 0 fun x => Real.exp (-lam * perimN2 h x) :=
    perimPoly_bdd (B := 1 + lam) fun x => (hB _ (perimN2_nonneg h x)).1
  have hVp := perimV_poly h
  have hVm := perimV_measurable h
  have hNp := perimN2_poly h
  -- integrability of the building blocks
  have iVw : Integrable (fun x => perimV h x * Real.exp (-lam * perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := perim_integrable_mul hVp hwp hVm hwm
  have iNw : Integrable (fun x => perimN2 h x * Real.exp (-lam * perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := perim_integrable_mul hNp hwp hN2m hwm
  have iKw : Integrable (fun x => perimK h x * Real.exp (-lam * perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    perim_integrable_mul (perimK_poly h) hwp (perimK_measurable h) hwm
  have iV2w : Integrable (fun x => perimV h x ^ 2 * Real.exp (-lam * perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hq : PerimPoly (2 + 2) fun x => perimV h x ^ 2 := by
      simpa [sq] using hVp.mul hVp
    exact perim_integrable_mul hq hwp (hVm.pow_const 2) hwm
  have iQw : Integrable (fun x => (lam * perimN2 h x) ^ 2 * Real.exp (-lam * perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hq : PerimPoly (2 + 2) fun x => (lam * perimN2 h x) ^ 2 := by
      simpa [sq] using (hNp.const_mul lam).mul (hNp.const_mul lam)
    exact perim_integrable_mul hq hwp ((hN2m.const_mul lam).pow_const 2) hwm
  have iNwV : Integrable (fun x => perimN2 h x * (-lam * Real.exp (-lam * perimN2 h x))
      * perimV h x) (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hq : PerimPoly (2 + 0) fun x => perimN2 h x * (-lam * Real.exp (-lam * perimN2 h x)) :=
      hNp.mul (hwp.const_mul (-lam))
    exact perim_integrable_mul hq hVp (hN2m.mul (hwm.const_mul (-lam))) hVm
  have iHPw : Integrable (fun x => Real.exp (-lam * perimN2 h x) *
      (2 * perimN2 h x + perimHP h x)) (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hq : PerimPoly 2 fun x => 2 * perimN2 h x + perimHP h x :=
      (hNp.const_mul 2).add ((perimHP_poly h).mono (by norm_num))
    have := perim_integrable_mul hwp hq hwm ((hN2m.const_mul 2).add (perimHP_measurable h))
    simpa using this
  -- (a)
  have hG1 := perim_G1 h hΞ hΞ' hB
  have ha : ∫ x, perimV h x * Real.exp (-lam * perimN2 h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = -2 * lam * ∫ x, perimN2 h x * Real.exp (-lam * perimN2 h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have e1 : (fun x => perimV h x * Real.exp (-lam * perimN2 h x))
        = fun x => Real.exp (-lam * perimN2 h x) * perimV h x := by funext x; ring
    have e2 : (fun x => perimN2 h x * (-lam * Real.exp (-lam * perimN2 h x)))
        = fun x => -lam * (perimN2 h x * Real.exp (-lam * perimN2 h x)) := by funext x; ring
    rw [e1, hG1, e2, integral_const_mul]
    ring
  refine ⟨ha, ?_⟩
  -- (b)
  have hG2 := perim_G2 h hΞ hΞ' hB
  beta_reduce at hG2
  have hs1 : ∫ x, Real.exp (-lam * perimN2 h x) * (2 * perimN2 h x + perimHP h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = ∫ x, perimN2 h x * Real.exp (-lam * perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + ∫ x, perimV h x * Real.exp (-lam * perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
        + ∫ x, perimK h x * Real.exp (-lam * perimN2 h x)
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hNV : Integrable (fun x => perimN2 h x * Real.exp (-lam * perimN2 h x)
        + perimV h x * Real.exp (-lam * perimN2 h x))
        (Measure.pi fun _ : Fin m => gaussianReal 0 1) := iNw.add iVw
    rw [← integral_add iNw iVw, ← integral_add hNV iKw]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := perimV_eq h x
    have hHP : perimHP h x = perimV h x - perimN2 h x + perimK h x := by linarith
    beta_reduce
    rw [hHP]
    ring
  have hmono : ∫ x, 2 * (perimN2 h x * (-lam * Real.exp (-lam * perimN2 h x)) * perimV h x)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ ∫ x, (1 / 2 * (perimV h x ^ 2 * Real.exp (-lam * perimN2 h x))
          + 2 * ((lam * perimN2 h x) ^ 2 * Real.exp (-lam * perimN2 h x)))
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    refine integral_mono (iNwV.const_mul 2) ((iV2w.const_mul (1 / 2)).add (iQw.const_mul 2))
      fun x => ?_
    have hw := Real.exp_pos (-lam * perimN2 h x)
    nlinarith [mul_nonneg hw.le (sq_nonneg (perimV h x + 2 * lam * perimN2 h x))]
  rw [integral_const_mul, integral_add (iV2w.const_mul (1 / 2)) (iQw.const_mul 2),
    integral_const_mul, integral_const_mul] at hmono
  have hNnn : 0 ≤ ∫ x, perimN2 h x * Real.exp (-lam * perimN2 h x)
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    integral_nonneg fun x => mul_nonneg (perimN2_nonneg h x) (Real.exp_pos _).le
  have hlN := mul_nonneg hlam.le hNnn
  rw [hs1, ha] at hG2
  nlinarith [hG2, hmono, hlN]

end G3

/-! ### (G4): the band corollary -/

section G4

/-- The piecewise linear trapezoid, `0` outside `(a, b)`, `1` on `[a + θ, b - θ]`. -/
noncomputable def perimTrap (a b θ y : ℝ) : ℝ :=
  max 0 (min 1 (min ((y - a) / θ) ((b - y) / θ)))

theorem perimTrap_continuous (a b θ : ℝ) : Continuous (perimTrap a b θ) := by
  unfold perimTrap
  fun_prop

theorem perimTrap_nonneg (a b θ y : ℝ) : 0 ≤ perimTrap a b θ y := le_max_left _ _

theorem perimTrap_le_one (a b θ y : ℝ) : perimTrap a b θ y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem perimTrap_eq_zero_left {a b θ : ℝ} (hθ : 0 < θ) {y : ℝ} (hy : y ≤ a) :
    perimTrap a b θ y = 0 := by
  unfold perimTrap
  have h1 : (y - a) / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
  exact max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans h1))

theorem perimTrap_eq_zero_right {a b θ : ℝ} (hθ : 0 < θ) {y : ℝ} (hy : b ≤ y) :
    perimTrap a b θ y = 0 := by
  unfold perimTrap
  have h1 : (b - y) / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans h1))

theorem perimTrap_eq_one {a b θ : ℝ} (hθ : 0 < θ) {y : ℝ} (h1 : a + θ ≤ y) (h2 : y ≤ b - θ) :
    perimTrap a b θ y = 1 := by
  unfold perimTrap
  have e1 : 1 ≤ (y - a) / θ := by rw [le_div_iff₀ hθ]; linarith
  have e2 : 1 ≤ (b - y) / θ := by rw [le_div_iff₀ hθ]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

/-- A `C¹` antiderivative of the trapezoid: `Ξ(y) = ∫_y^b ψ`, with the properties needed for the
band argument. -/
theorem perim_trap_exists {a b θ : ℝ} (hab : a < b) (hθ : 0 < θ) :
    ∃ Ξ Ξ' : ℝ → ℝ, (∀ y, HasDerivAt Ξ (Ξ' y) y) ∧ Continuous Ξ' ∧ (∀ y, 0 ≤ Ξ y) ∧
      (∀ y, Ξ y ≤ b - a) ∧ (∀ y, b ≤ y → Ξ y = 0) ∧ (∀ y, Ξ' y ≤ 0) ∧ (∀ y, -1 ≤ Ξ' y) ∧
      (∀ y, a + θ ≤ y → y ≤ b - θ → Ξ' y = -1) := by
  set ψ : ℝ → ℝ := perimTrap a b θ with hψ
  have hψc : Continuous ψ := perimTrap_continuous a b θ
  have hii : ∀ u v : ℝ, IntervalIntegrable ψ volume u v := fun u v => hψc.intervalIntegrable u v
  set Ξ : ℝ → ℝ := fun y => ∫ t in y..b, ψ t with hΞdef
  have hΞeq : Ξ = fun y => (∫ t in (0 : ℝ)..b, ψ t) - ∫ t in (0 : ℝ)..y, ψ t := by
    funext y
    exact (intervalIntegral.integral_interval_sub_left (hii 0 b) (hii 0 y)).symm
  have hderiv : ∀ y, HasDerivAt Ξ (-ψ y) y := by
    intro y
    rw [hΞeq]
    exact ((hψc.integral_hasStrictDerivAt 0 y).hasDerivAt).const_sub _ |>.congr_deriv (by ring)
  have hzero : ∀ y, b ≤ y → Ξ y = 0 := by
    intro y hy
    simp only [hΞdef]
    rw [intervalIntegral.integral_symm]
    have : ∫ t in b..y, ψ t = ∫ t in b..y, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hy] at ht
      exact perimTrap_eq_zero_right hθ ht.1
    rw [this]
    simp
  have hnn : ∀ y, 0 ≤ Ξ y := by
    intro y
    by_cases hy : y ≤ b
    · exact intervalIntegral.integral_nonneg hy fun u _ => perimTrap_nonneg a b θ u
    · rw [hzero y (le_of_not_ge hy)]
  have hmid : ∀ y, a ≤ y → Ξ y ≤ b - a := by
    intro y hay
    by_cases hy : y ≤ b
    · have h1 : Ξ y ≤ ∫ t in y..b, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hy (hii y b) intervalIntegrable_const
          fun u _ => perimTrap_le_one a b θ u
      rw [intervalIntegral.integral_const] at h1
      simp only [smul_eq_mul, mul_one] at h1
      linarith
    · rw [hzero y (le_of_not_ge hy)]; linarith
  have hle : ∀ y, Ξ y ≤ b - a := by
    intro y
    by_cases hay : a ≤ y
    · exact hmid y hay
    · have hya : y ≤ a := le_of_not_ge hay
      have h1 : Ξ y = (∫ t in y..a, ψ t) + Ξ a :=
        (intervalIntegral.integral_add_adjacent_intervals (hii y a) (hii a b)).symm
      have h2 : ∫ t in y..a, ψ t = 0 := by
        have : ∫ t in y..a, ψ t = ∫ t in y..a, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hya] at ht
          exact perimTrap_eq_zero_left hθ ht.2
        rw [this]; simp
      rw [h1, h2, zero_add]
      exact hmid a le_rfl
  refine ⟨Ξ, fun y => -ψ y, hderiv, hψc.neg, hnn, hle, hzero, ?_, ?_, ?_⟩
  · intro y; simpa using perimTrap_nonneg a b θ y
  · intro y; simpa using perimTrap_le_one a b θ y
  · intro y h1 h2
    simp only [hψ]
    rw [perimTrap_eq_one hθ h1 h2]

variable {m : ℕ}

/-- **(G4), closed-band form.**  For `0 < a < b` and every `θ > 0`,
`γ{a + θ ≤ N² ≤ b - θ} ≤ ((b - a) / (2a)) E[|V|; N² < b]`. -/
theorem perim_G4_closed (h : Fin m → ℝ) {a b θ : ℝ} (ha : 0 < a) (hab : a < b) (hθ : 0 < θ) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1).real
        {x | a + θ ≤ perimN2 h x ∧ perimN2 h x ≤ b - θ}
      ≤ (b - a) / (2 * a) * ∫ x in {x | perimN2 h x < b}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  obtain ⟨Ξ, Ξ', hd, hc, h0, hle, hz, hneg, hneg1, hone⟩ := perim_trap_exists hab hθ
  have hB : ∀ y, 0 ≤ y → |Ξ y| ≤ (b - a) + 1 ∧ |Ξ' y| ≤ (b - a) + 1 := by
    intro y _
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg (h0 y)]; linarith [hle y]
    · rw [abs_le]; constructor <;> linarith [hneg y, hneg1 y]
  have hG1 := perim_G1 h hd hc hB
  have hΞc : Continuous Ξ := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hN2m := perimN2_measurable h
  have hΞm : Measurable fun x => Ξ (perimN2 h x) := hΞc.measurable.comp hN2m
  have hΞ'm : Measurable fun x => Ξ' (perimN2 h x) := hc.measurable.comp hN2m
  have hΞp : PerimPoly 0 fun x => Ξ (perimN2 h x) :=
    perimPoly_bdd (B := (b - a) + 1) fun x => (hB _ (perimN2_nonneg h x)).1
  have hΞ'p : PerimPoly 0 fun x => Ξ' (perimN2 h x) :=
    perimPoly_bdd (B := (b - a) + 1) fun x => (hB _ (perimN2_nonneg h x)).2
  have hVm := perimV_measurable h
  have hVp := perimV_poly h
  have hNp := perimN2_poly h
  set S : Set (Fin m → ℝ) := {x | a + θ ≤ perimN2 h x ∧ perimN2 h x ≤ b - θ} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const hN2m).inter (measurableSet_le hN2m measurable_const)
  have hT : MeasurableSet {x : Fin m → ℝ | perimN2 h x < b} :=
    measurableSet_lt hN2m measurable_const
  -- integrability
  have iNΞ' : Integrable (fun x => perimN2 h x * Ξ' (perimN2 h x))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := perim_integrable_mul hNp hΞ'p hN2m hΞ'm
  have iΞV : Integrable (fun x => Ξ (perimN2 h x) * perimV h x)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := perim_integrable_mul hΞp hVp hΞm hVm
  have hVabsp : PerimPoly 2 fun x => |perimV h x| := hVp.of_abs_le fun x => by rw [abs_abs]
  have iΞabsV : Integrable (fun x => Ξ (perimN2 h x) * |perimV h x|)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    perim_integrable_mul hΞp hVabsp hΞm hVm.abs
  have iabsV : Integrable (fun x => (b - a) * |perimV h x|)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have := (hVabsp.const_mul (b - a)).integrable (hVm.abs.const_mul (b - a)).aestronglyMeasurable
    exact this
  -- Step B
  have hB' : a * (Measure.pi fun _ : Fin m => gaussianReal 0 1).real S
      ≤ ∫ x, perimN2 h x * (-Ξ' (perimN2 h x))
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have h1 := integral_indicator_const (μ := Measure.pi fun _ : Fin m => gaussianReal 0 1)
      a hS
    rw [smul_eq_mul, mul_comm] at h1
    rw [← h1]
    refine integral_mono ((integrable_const a).indicator hS) (by simpa using iNΞ'.neg) fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, hone _ hx.1 hx.2]
      have := hx.1
      linarith
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (perimN2_nonneg h x) (by linarith [hneg (perimN2 h x)])
  -- Step A
  have hA : -∫ x, Ξ (perimN2 h x) * perimV h x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      ≤ (b - a) * ∫ x in {x | perimN2 h x < b}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    rw [← integral_neg, ← integral_const_mul, ← integral_indicator hT]
    refine integral_mono iΞV.neg
      (iabsV.indicator hT) fun x => ?_
    by_cases hx : perimN2 h x < b
    · rw [Set.indicator_of_mem (show x ∈ {x | perimN2 h x < b} from hx)]
      have h1 := h0 (perimN2 h x)
      have h2 := hle (perimN2 h x)
      have h3 : Ξ (perimN2 h x) * |perimV h x| ≤ (b - a) * |perimV h x| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      have h4 : -(Ξ (perimN2 h x) * perimV h x) ≤ Ξ (perimN2 h x) * |perimV h x| := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_le_abs _) h1
      beta_reduce
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | perimN2 h x < b} from hx)]
      have : Ξ (perimN2 h x) = 0 := hz _ (not_lt.mp hx)
      simp [this]
  have hI : ∫ x, perimN2 h x * (-Ξ' (perimN2 h x))
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = -∫ x, perimN2 h x * Ξ' (perimN2 h x) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp)
  rw [hG1] at hA
  rw [hI] at hB'
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hA, hB']

/-- **(G4).**  For `0 < a < b`:
`γ{a < N² < b} ≤ ((b - a) / (2a)) E[|V|; N² < b]`. -/
theorem perim_G4 (h : Fin m → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1).real
        {x | a < perimN2 h x ∧ perimN2 h x < b}
      ≤ (b - a) / (2 * a) * ∫ x in {x | perimN2 h x < b}, |perimV h x|
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  set μ : Measure (Fin m → ℝ) := Measure.pi fun _ : Fin m => gaussianReal 0 1 with hμ
  set c : ℝ := (b - a) / (2 * a) * ∫ x in {x | perimN2 h x < b}, |perimV h x| ∂μ with hc
  have hc0 : 0 ≤ c :=
    mul_nonneg (div_nonneg (by linarith) (by linarith))
      (setIntegral_nonneg (measurableSet_lt (perimN2_measurable h) measurable_const)
        fun x _ => abs_nonneg _)
  set θ : ℕ → ℝ := fun n => (b - a) / ((n : ℝ) + 1) with hθ
  have hθpos : ∀ n, 0 < θ n := fun n => div_pos (by linarith) (by positivity)
  set S : ℕ → Set (Fin m → ℝ) := fun n =>
    {x | a + θ n ≤ perimN2 h x ∧ perimN2 h x ≤ b - θ n} with hS
  have hmono : Monotone S := by
    intro n n' hnn' x hx
    have : θ n' ≤ θ n := by
      refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
      have : (n : ℝ) ≤ n' := Nat.cast_le.mpr hnn'
      linarith
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hunion : (⋃ n, S n) = {x | a < perimN2 h x ∧ perimN2 h x < b} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, hS]
    constructor
    · rintro ⟨n, h1, h2⟩
      have := hθpos n
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / min (perimN2 h x - a) (b - perimN2 h x))
      have hmin : 0 < min (perimN2 h x - a) (b - perimN2 h x) := lt_min (by linarith) (by linarith)
      refine ⟨n, ?_, ?_⟩
      · have : θ n ≤ min (perimN2 h x - a) (b - perimN2 h x) := by
          rw [hθ]
          simp only
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hmin] at hn
          nlinarith
        linarith [min_le_left (perimN2 h x - a) (b - perimN2 h x)]
      · have : θ n ≤ min (perimN2 h x - a) (b - perimN2 h x) := by
          rw [hθ]
          simp only
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hmin] at hn
          nlinarith
        linarith [min_le_right (perimN2 h x - a) (b - perimN2 h x)]
  have hbound : ∀ n, μ (S n) ≤ ENNReal.ofReal c := by
    intro n
    have h1 := perim_G4_closed h ha hab (hθpos n)
    have h2 : μ (S n) = ENNReal.ofReal (μ.real (S n)) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [h2]
    exact ENNReal.ofReal_le_ofReal h1
  rw [measureReal_def, ← hunion, hmono.measure_iUnion]
  exact ENNReal.toReal_le_of_le_ofReal hc0 (iSup_le hbound)

end G4

/-! ### Transfer to the standard Gaussian on Euclidean space -/

section Transfer

variable {m : ℕ}

/-- Integrals against `stdGaussian (EuclideanSpace ℝ (Fin m))` of functions of the coordinates are
integrals against the product measure `Measure.pi (fun _ => gaussianReal 0 1)`. -/
theorem perim_integral_stdGaussian (F : (Fin m → ℝ) → ℝ) (hF : Measurable F) :
    ∫ y, F y.ofLp ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))
      = ∫ x, F x ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  have hm : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin m) => F y.ofLp)
      (Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin m => gaussianReal 0 1)) :=
    (hF.comp (PiLp.continuous_ofLp 2 _).measurable).aestronglyMeasurable
  rw [← map_pi_eq_stdGaussian, integral_map (PiLp.continuous_toLp 2 _).aemeasurable hm]

/-- Measures of coordinate sets under `stdGaussian` and the product measure agree. -/
theorem perim_real_stdGaussian {T : Set (Fin m → ℝ)} (hT : MeasurableSet T) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real {y | y.ofLp ∈ T}
      = (Measure.pi fun _ : Fin m => gaussianReal 0 1).real T := by
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin m) | y.ofLp ∈ T} :=
    (PiLp.continuous_ofLp 2 _).measurable hT
  rw [measureReal_def, measureReal_def, ← map_pi_eq_stdGaussian,
    Measure.map_apply (PiLp.continuous_toLp 2 _).measurable hmeas]
  rfl

/-- **(G4) for `stdGaussian (EuclideanSpace ℝ (Fin m))`.** -/
theorem perim_G4_stdGaussian (h : Fin m → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real
        {y | a < perimN2 h y.ofLp ∧ perimN2 h y.ofLp < b}
      ≤ (b - a) / (2 * a) * ∫ y in {y | perimN2 h y.ofLp < b}, |perimV h y.ofLp|
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  set T : Set (Fin m → ℝ) := {x | perimN2 h x < b} with hT
  have hTm : MeasurableSet T := measurableSet_lt (perimN2_measurable h) measurable_const
  have hBm : MeasurableSet {x : Fin m → ℝ | a < perimN2 h x ∧ perimN2 h x < b} :=
    (measurableSet_lt measurable_const (perimN2_measurable h)).inter hTm
  have h1 : {y : EuclideanSpace ℝ (Fin m) | a < perimN2 h y.ofLp ∧ perimN2 h y.ofLp < b}
      = {y | y.ofLp ∈ {x : Fin m → ℝ | a < perimN2 h x ∧ perimN2 h x < b}} := rfl
  have h2 : ∫ y in {y : EuclideanSpace ℝ (Fin m) | perimN2 h y.ofLp < b}, |perimV h y.ofLp|
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))
      = ∫ x in T, |perimV h x| ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
    have hTm' : MeasurableSet {y : EuclideanSpace ℝ (Fin m) | perimN2 h y.ofLp < b} :=
      (PiLp.continuous_ofLp 2 _).measurable hTm
    rw [← integral_indicator hTm', ← integral_indicator hTm]
    have := perim_integral_stdGaussian (T.indicator fun x => |perimV h x|)
      ((perimV_measurable h).abs.indicator hTm)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    by_cases hy : perimN2 h y.ofLp < b
    · rw [Set.indicator_of_mem (show y ∈ {y : EuclideanSpace ℝ (Fin m) |
        perimN2 h y.ofLp < b} from hy), Set.indicator_of_mem (show y.ofLp ∈ T from hy)]
    · rw [Set.indicator_of_notMem (show y ∉ {y : EuclideanSpace ℝ (Fin m) |
        perimN2 h y.ofLp < b} from hy), Set.indicator_of_notMem (show y.ofLp ∉ T from hy)]
  rw [h1, perim_real_stdGaussian hBm, h2]
  exact perim_G4 h ha hab

end Transfer

end LatticeProb
