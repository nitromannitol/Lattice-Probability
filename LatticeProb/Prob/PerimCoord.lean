import Mathlib

/-!
# One Gaussian coordinate: the per-coordinate inequalities for the orthant perimeter bound

Packet Q3 of the elementary proof of the Gaussian perimeter bound for orthant layers.  For one
standard Gaussian coordinate `Z ~ γ₁ = N(0,1)`, a level `h : ℝ` and a scale `t > 0`, put
`p z = max (z - h) 0`, `w z = exp (-p z ^ 2 / t ^ 2)` and

* `perimCU h t = ∫_{z > h} (1 - w z) dγ₁`, `perimCQ h t = ∫_{z > h} w z dγ₁`,
* `perimCE2 h t = ∫_{z > h} (p z / t)^2 w z dγ₁`, `perimCE4 h t = ∫_{z > h} (p z / t)^4 w z dγ₁`.

We prove the hazard bound `φ(max x 0) ≤ (1 + max x 0) Φ̄(x)`, the comparisons `e2 ≤ u`,
`e4 ≤ c₂ u`, the density bounds `q, e2, e4 ≲ t φ(h₊)`, the activity bound
`P(Z > h) ≤ κ u` with `κ = 2 (1 + 4 (1 + h₊)² t²)`, and the tail facts for big coordinates.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-! ### Definitions -/

/-- The one-sided excess `p z = max (z - h) 0`. -/
noncomputable def perimCP (h z : ℝ) : ℝ := max (z - h) 0

/-- The weight `w z = exp (-p z ^ 2 / t ^ 2)`. -/
noncomputable def perimCW (h t z : ℝ) : ℝ := Real.exp (-perimCP h z ^ 2 / t ^ 2)

/-- The Gaussian upper tail `Φ̄ x = γ₁ (x, ∞)`, as a real number. -/
noncomputable def perimCTail (x : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi x)

/-- `u(h,t) = ∫_{z > h} (1 - w z) dγ₁`. -/
noncomputable def perimCU (h t : ℝ) : ℝ :=
  ∫ z in Ioi h, (1 - perimCW h t z) ∂(gaussianReal 0 1)

/-- `q(h,t) = ∫_{z > h} w z dγ₁`. -/
noncomputable def perimCQ (h t : ℝ) : ℝ :=
  ∫ z in Ioi h, perimCW h t z ∂(gaussianReal 0 1)

/-- `e2(h,t) = ∫_{z > h} (p z / t)^2 w z dγ₁`. -/
noncomputable def perimCE2 (h t : ℝ) : ℝ :=
  ∫ z in Ioi h, (perimCP h z / t) ^ 2 * perimCW h t z ∂(gaussianReal 0 1)

/-- `e4(h,t) = ∫_{z > h} (p z / t)^4 w z dγ₁`. -/
noncomputable def perimCE4 (h t : ℝ) : ℝ :=
  ∫ z in Ioi h, (perimCP h z / t) ^ 4 * perimCW h t z ∂(gaussianReal 0 1)

/-! ### Basic facts on the density -/

lemma perimC_phi_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

lemma perimC_phi_pos (x : ℝ) : 0 < gaussianPDFReal 0 1 x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

lemma perimC_hasDerivAt_phi (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    exact this.congr_deriv (by norm_num; ring)
  have h2 := (Real.hasDerivAt_exp (-x ^ 2 / 2)).comp x h1
  have h3 := h2.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  have hfun : gaussianPDFReal 0 1 =
      fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    funext y; exact perimC_phi_eq y
  rw [hfun]
  exact h3.congr_deriv (by beta_reduce; ring)

lemma perimC_phi_tendsto : Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h3 : Tendsto (fun y : ℝ => -y ^ 2 / 2) atTop atBot := by
    refine Filter.Tendsto.atBot_div_const (by norm_num) ?_
    exact tendsto_neg_atBot_iff.mpr (tendsto_pow_atTop (by norm_num))
  have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  simp only [Function.comp, mul_zero] at h4
  have hfun : gaussianPDFReal 0 1 =
      fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    funext y; exact perimC_phi_eq y
  rwa [hfun]

lemma perimC_phi_le_of_abs_le {a b : ℝ} (hab : |a| ≤ |b|) :
    gaussianPDFReal 0 1 b ≤ gaussianPDFReal 0 1 a := by
  rw [perimC_phi_eq, perimC_phi_eq]
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le
  have : a ^ 2 ≤ b ^ 2 := sq_le_sq.mpr hab
  linarith

/-- `Φ̄ x = ∫_{z > x} φ`. -/
lemma perimCTail_eq_integral (x : ℝ) :
    perimCTail x = ∫ z in Ioi x, gaussianPDFReal 0 1 z := by
  rw [perimCTail, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero (Ioi x),
    ENNReal.toReal_ofReal (integral_nonneg (fun z => gaussianPDFReal_nonneg 0 1 z))]

lemma perimCTail_nonneg (x : ℝ) : 0 ≤ perimCTail x := measureReal_nonneg

lemma perimCTail_le_one (x : ℝ) : perimCTail x ≤ 1 := measureReal_le_one

/-- `Φ̄ x = 1 - cdf γ₁ x`. -/
lemma perimCTail_eq_one_sub_cdf (x : ℝ) : perimCTail x = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic]
  rfl

/-! ### The hazard bound -/

/-- **Hazard bound, `x ≥ 0`**: `φ(x) ≤ (1 + x) Φ̄(x)`. -/
theorem perimC_phi_le_mul_tail_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    gaussianPDFReal 0 1 x ≤ (1 + x) * perimCTail x := by
  set φ : ℝ → ℝ := gaussianPDFReal 0 1 with hφ
  set g : ℝ → ℝ := fun z => φ z * (1 + z)⁻¹ with hg
  set G : ℝ → ℝ := fun z => φ z * (-(z * (1 + z) + 1) / (1 + z) ^ 2) with hG
  have hgd : ∀ z ∈ Ioi x, HasDerivAt g (G z) z := by
    intro z hz
    have hz0 : 0 < 1 + z := by have : x < z := hz; linarith
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by simpa using (hasDerivAt_id z).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-1 / (1 + z) ^ 2) z := h1.inv hz0.ne'
    have h3 := (perimC_hasDerivAt_phi z).mul h2
    refine h3.congr_deriv ?_
    simp only [hG]
    field_simp
    ring
  have hle : ∀ z ∈ Ioi x, -G z ≤ φ z := by
    intro z hz
    have hz1 : x < z := hz
    have hz0 : 0 < 1 + z := by linarith
    have hpos := perimC_phi_pos z
    have : -G z = φ z * ((z * (1 + z) + 1) / (1 + z) ^ 2) := by
      simp only [hG]; ring
    rw [this]
    have hq : (z * (1 + z) + 1) / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    nlinarith
  have hGmeas : Measurable G := by
    simp only [hG]
    exact (measurable_gaussianPDFReal 0 1).mul (by fun_prop)
  have hGint : IntegrableOn G (Ioi x) := by
    refine Integrable.mono' (g := φ) ((integrable_gaussianPDFReal 0 1).integrableOn)
      hGmeas.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have hz1 : x < z := hz
    have hz0 : 0 < 1 + z := by linarith
    have hpos := perimC_phi_pos z
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    have hq : |-(z * (1 + z) + 1) / (1 + z) ^ 2| ≤ 1 := by
      rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < (1 + z) ^ 2),
        abs_of_pos (by nlinarith : 0 < z * (1 + z) + 1), div_le_one (by positivity)]
      nlinarith
    nlinarith
  have hcont : ContinuousWithinAt g (Ici x) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-1 / (1 + x) ^ 2) x :=
      h1.inv (by linarith : (1 + x) ≠ 0)
    exact ((perimC_hasDerivAt_phi x).mul h2).continuousAt.continuousWithinAt
  have htend : Tendsto g atTop (𝓝 0) := by
    have hinv : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
    simpa using perimC_phi_tendsto.mul hinv
  have hkey := integral_Ioi_of_hasDerivAt_of_tendsto hcont hgd hGint htend
  have hmono : ∫ z in Ioi x, -G z ≤ ∫ z in Ioi x, φ z :=
    setIntegral_mono_on hGint.neg ((integrable_gaussianPDFReal 0 1).integrableOn)
      measurableSet_Ioi hle
  rw [integral_neg, hkey, ← perimCTail_eq_integral] at hmono
  have hgx : g x = φ x * (1 + x)⁻¹ := rfl
  have hpos : 0 < 1 + x := by linarith
  have : φ x * (1 + x)⁻¹ ≤ perimCTail x := by simp only [hgx] at hmono; linarith
  rw [← div_eq_mul_inv, div_le_iff₀ hpos] at this
  linarith

/-- `Φ̄ 0 = 1/2`. -/
lemma perimCTail_zero : perimCTail 0 = 1 / 2 := by
  rw [perimCTail_eq_integral]
  have hfun : (fun z : ℝ => gaussianPDFReal 0 1 z) =
      fun z => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * z ^ 2) := by
    funext z
    rw [perimC_phi_eq]
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_gaussian_Ioi]
  have hπ : 0 < Real.pi := Real.pi_pos
  have h2 : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  rw [h2]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  field_simp

lemma perimCTail_ge_half {x : ℝ} (hx : x ≤ 0) : 1 / 2 ≤ perimCTail x := by
  rw [← perimCTail_zero]
  exact measureReal_mono (Ioi_subset_Ioi hx)

lemma perimC_phi_zero_le_half : gaussianPDFReal 0 1 0 ≤ 1 / 2 := by
  rw [perimC_phi_eq]
  have h2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    exact Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Real.exp_zero, mul_one]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- **Hazard bound.**  `φ(max x 0) ≤ (1 + max x 0) Φ̄(x)` for every real `x`. -/
theorem perimC_phi_max_le_mul_tail (x : ℝ) :
    gaussianPDFReal 0 1 (max x 0) ≤ (1 + max x 0) * perimCTail x := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, add_zero, one_mul]
    exact perimC_phi_zero_le_half.trans (perimCTail_ge_half hx)
  · rw [max_eq_left hx]
    exact perimC_phi_le_mul_tail_of_nonneg hx

/-- **Hazard bound.**  `φ(x) ≤ (1 + max x 0) Φ̄(x)` for every real `x`. -/
theorem perimC_phi_le_mul_tail (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (1 + max x 0) * perimCTail x := by
  refine le_trans ?_ (perimC_phi_max_le_mul_tail x)
  refine perimC_phi_le_of_abs_le ?_
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, abs_zero]; exact abs_nonneg _
  · rw [max_eq_left hx]

/-- The density is dominated by its value at `max h 0` on `[h, ∞)`. -/
lemma perimC_phi_le_max {h z : ℝ} (hz : h ≤ z) :
    gaussianPDFReal 0 1 z ≤ gaussianPDFReal 0 1 (max h 0) := by
  refine perimC_phi_le_of_abs_le ?_
  rcases le_total h 0 with hh | hh
  · rw [max_eq_right hh, abs_zero]; exact abs_nonneg _
  · rw [max_eq_left hh, abs_of_nonneg hh]
    exact le_trans (le_abs_self h) (abs_le_abs_of_nonneg hh hz)

/-! ### The weight and its pointwise inequalities -/

lemma perimCP_nonneg (h z : ℝ) : 0 ≤ perimCP h z := le_max_right _ _

lemma perimCP_of_le {h z : ℝ} (hz : h ≤ z) : perimCP h z = z - h :=
  max_eq_left (by linarith)

lemma perimCP_continuous (h : ℝ) : Continuous (perimCP h) :=
  (continuous_id.sub continuous_const).max continuous_const

lemma perimCW_eq (h t z : ℝ) : perimCW h t z = Real.exp (-((perimCP h z / t) ^ 2)) := by
  unfold perimCW
  rw [div_pow]
  ring_nf

lemma perimCW_pos (h t z : ℝ) : 0 < perimCW h t z := Real.exp_pos _

lemma perimCW_le_one (h t z : ℝ) : perimCW h t z ≤ 1 := by
  rw [perimCW_eq]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (perimCP h z / t)])

lemma perimCW_continuous (h t : ℝ) : Continuous (perimCW h t) := by
  unfold perimCW
  exact Real.continuous_exp.comp (((perimCP_continuous h).pow 2).neg.div_const _)

/-- `x e^{-x} ≤ 1 - e^{-x}` (true for every real `x`, from `1 + x ≤ e^x`). -/
lemma perimC_pt_one (x : ℝ) : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h1 := Real.add_one_le_exp x
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-x) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

/-- The Taylor-polynomial positivity behind the constant `0.648`. -/
lemma perimC_poly_648 {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (648 / 1000 : ℝ) * (1 + x / 2 + x ^ 2 / 6 + x ^ 3 / 24 + x ^ 4 / 120 + x ^ 5 / 720
      + x ^ 6 / 5040 + x ^ 7 / 40320) - x := by
  have h0 := pow_nonneg hx 0
  have h1 := pow_nonneg hx 1
  have h2 := pow_nonneg hx 2
  have h3 := pow_nonneg hx 3
  have h4 := pow_nonneg hx 4
  have h5 := pow_nonneg hx 5
  have h6 := pow_nonneg hx 6
  have h7 := pow_nonneg hx 7
  nlinarith [mul_nonneg h0 (sq_nonneg (x - 996 / 625)), mul_nonneg h1 (sq_nonneg (x - 996 / 625)),
    mul_nonneg h2 (sq_nonneg (x - 996 / 625)), mul_nonneg h3 (sq_nonneg (x - 996 / 625)),
    mul_nonneg h4 (sq_nonneg (x - 996 / 625)), mul_nonneg h5 (sq_nonneg (x - 996 / 625))]

/-- `x² ≤ 0.648 (e^x - 1)` for `x ≥ 0` (the sharp constant is `≈ 0.6476`). -/
lemma perimC_sq_le_expm1 {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 ≤ (648 / 1000 : ℝ) * (Real.exp x - 1) := by
  have hT := Real.sum_le_exp_of_nonneg hx 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hp := perimC_poly_648 hx
  nlinarith [mul_nonneg hx hp]

/-- `x² e^{-x} ≤ 0.648 (1 - e^{-x})` for `x ≥ 0`. -/
lemma perimC_pt_two {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ (648 / 1000 : ℝ) * (1 - Real.exp (-x)) := by
  have h1 := perimC_sq_le_expm1 hx
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-x) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

lemma perimC_pt_e2 (h t z : ℝ) :
    (perimCP h z / t) ^ 2 * perimCW h t z ≤ 1 - perimCW h t z := by
  rw [perimCW_eq]
  exact perimC_pt_one _

lemma perimC_pt_e4 (h t z : ℝ) :
    (perimCP h z / t) ^ 4 * perimCW h t z ≤ (648 / 1000 : ℝ) * (1 - perimCW h t z) := by
  rw [perimCW_eq]
  have := perimC_pt_two (sq_nonneg (perimCP h z / t))
  rw [← pow_mul] at this
  exact this

lemma perimC_e2_nonneg (h t z : ℝ) : 0 ≤ (perimCP h z / t) ^ 2 * perimCW h t z :=
  mul_nonneg (sq_nonneg _) (perimCW_pos h t z).le

lemma perimC_e4_nonneg (h t z : ℝ) : 0 ≤ (perimCP h z / t) ^ 4 * perimCW h t z :=
  mul_nonneg (by positivity) (perimCW_pos h t z).le

lemma perimC_one_sub_nonneg (h t z : ℝ) : 0 ≤ 1 - perimCW h t z := by
  linarith [perimCW_le_one h t z]

/-! ### Integrability -/

lemma perimC_integrableOn_of_bdd {s : Set ℝ} {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f)
    (hC : ∀ z, |f z| ≤ C) : IntegrableOn f s (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (ae_of_all _ ?_)
  intro z
  simpa [Real.norm_eq_abs] using hC z

lemma perimC_continuous_e2 (h t : ℝ) :
    Continuous (fun z => (perimCP h z / t) ^ 2 * perimCW h t z) :=
  (((perimCP_continuous h).div_const t).pow 2).mul (perimCW_continuous h t)

lemma perimC_continuous_e4 (h t : ℝ) :
    Continuous (fun z => (perimCP h z / t) ^ 4 * perimCW h t z) :=
  (((perimCP_continuous h).div_const t).pow 4).mul (perimCW_continuous h t)

lemma perimC_integrableOn_one_sub (h t : ℝ) (s : Set ℝ) :
    IntegrableOn (fun z => 1 - perimCW h t z) s (gaussianReal 0 1) := by
  refine perimC_integrableOn_of_bdd (C := 1) (continuous_const.sub (perimCW_continuous h t)) ?_
  intro z
  rw [abs_of_nonneg (perimC_one_sub_nonneg h t z)]
  linarith [perimCW_pos h t z]

lemma perimC_integrableOn_w (h t : ℝ) (s : Set ℝ) :
    IntegrableOn (fun z => perimCW h t z) s (gaussianReal 0 1) := by
  refine perimC_integrableOn_of_bdd (C := 1) (perimCW_continuous h t) ?_
  intro z
  rw [abs_of_pos (perimCW_pos h t z)]
  exact perimCW_le_one h t z

lemma perimC_integrableOn_e2 (h t : ℝ) (s : Set ℝ) :
    IntegrableOn (fun z => (perimCP h z / t) ^ 2 * perimCW h t z) s (gaussianReal 0 1) := by
  refine perimC_integrableOn_of_bdd (C := 1) (perimC_continuous_e2 h t) ?_
  intro z
  rw [abs_of_nonneg (perimC_e2_nonneg h t z)]
  linarith [perimC_pt_e2 h t z, perimCW_pos h t z]

lemma perimC_integrableOn_e4 (h t : ℝ) (s : Set ℝ) :
    IntegrableOn (fun z => (perimCP h z / t) ^ 4 * perimCW h t z) s (gaussianReal 0 1) := by
  refine perimC_integrableOn_of_bdd (C := 1) (perimC_continuous_e4 h t) ?_
  intro z
  rw [abs_of_nonneg (perimC_e4_nonneg h t z)]
  linarith [perimC_pt_e4 h t z, perimCW_pos h t z]

/-! ### (P1), (P2) -/

lemma perimCU_nonneg (h t : ℝ) : 0 ≤ perimCU h t :=
  setIntegral_nonneg measurableSet_Ioi (fun z _ => perimC_one_sub_nonneg h t z)

lemma perimCQ_nonneg (h t : ℝ) : 0 ≤ perimCQ h t :=
  setIntegral_nonneg measurableSet_Ioi (fun z _ => (perimCW_pos h t z).le)

lemma perimCE2_nonneg (h t : ℝ) : 0 ≤ perimCE2 h t :=
  setIntegral_nonneg measurableSet_Ioi (fun z _ => perimC_e2_nonneg h t z)

lemma perimCE4_nonneg (h t : ℝ) : 0 ≤ perimCE4 h t :=
  setIntegral_nonneg measurableSet_Ioi (fun z _ => perimC_e4_nonneg h t z)

/-- **(P1)** `e2 ≤ u`. -/
theorem perimCE2_le_perimCU (h t : ℝ) : perimCE2 h t ≤ perimCU h t :=
  setIntegral_mono_on (perimC_integrableOn_e2 h t _) (perimC_integrableOn_one_sub h t _)
    measurableSet_Ioi (fun z _ => perimC_pt_e2 h t z)

/-- **(P2)** `e4 ≤ 0.648 u` (the sharp constant is `≈ 0.6476`). -/
theorem perimCE4_le_perimCU (h t : ℝ) : perimCE4 h t ≤ (648 / 1000 : ℝ) * perimCU h t := by
  have := setIntegral_mono_on (perimC_integrableOn_e4 h t (Ioi h))
    ((perimC_integrableOn_one_sub h t (Ioi h)).const_mul (648 / 1000 : ℝ))
    measurableSet_Ioi (fun z _ => perimC_pt_e4 h t z)
  rw [integral_const_mul] at this
  exact this

/-! ### (P3) Density bounds -/

/-- Translation of a half-line integral. -/
lemma perimC_setIntegral_Ioi_sub (h : ℝ) (f : ℝ → ℝ) :
    ∫ z in Ioi h, f (z - h) = ∫ s in Ioi (0 : ℝ), f s := by
  have := (measurePreserving_sub_right (volume : Measure ℝ) h).setIntegral_preimage_emb
    (measurableEmbedding_subRight h) f (Ioi 0)
  have hpre : (fun z : ℝ => z - h) ⁻¹' Ioi 0 = Ioi h := by
    ext z; simp
  rw [hpre] at this
  exact this

/-- Translation of half-line integrability. -/
lemma perimC_integrableOn_Ioi_sub (h : ℝ) (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (fun z => f (z - h)) (Ioi h) := by
  have := (measurePreserving_sub_right (volume : Measure ℝ) h).integrableOn_comp_preimage
    (measurableEmbedding_subRight h) (s := Ioi 0) (f := f)
  have hpre : (fun z : ℝ => z - h) ⁻¹' Ioi 0 = Ioi h := by
    ext z; simp
  rw [hpre] at this
  exact this.mpr hf

/-- Set integrals against `γ₁` as Lebesgue integrals against `φ`. -/
lemma perimC_setIntegral_gauss {s : Set ℝ} (hs : MeasurableSet s) (F : ℝ → ℝ) :
    ∫ z in s, F z ∂(gaussianReal 0 1) = ∫ z in s, gaussianPDFReal 0 1 z * F z := by
  rw [← integral_indicator hs, integral_gaussianReal_eq_integral_smul one_ne_zero,
    ← integral_indicator hs]
  congr 1
  funext z
  by_cases hz : z ∈ s <;> simp [hz]

lemma perimC_moment (n : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ n * Real.exp (-y ^ 2) = (1 / 2) * Real.Gamma (((n : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (n : ℝ)) (by norm_num)
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  simp [Real.rpow_natCast]

lemma perimC_integrableOn_moment (n : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ n * Real.exp (-y ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast]

lemma perimC_gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

lemma perimC_gamma_five_halves : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    perimC_gamma_three_halves]
  ring

/-- `∫_0^∞ e^{-y²} dy = √π / 2`. -/
lemma perimC_moment_zero :
    ∫ y in Ioi (0 : ℝ), y ^ 0 * Real.exp (-y ^ 2) = Real.sqrt Real.pi / 2 := by
  rw [perimC_moment, show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
  ring

/-- `∫_0^∞ y² e^{-y²} dy = √π / 4`. -/
lemma perimC_moment_two :
    ∫ y in Ioi (0 : ℝ), y ^ 2 * Real.exp (-y ^ 2) = Real.sqrt Real.pi / 4 := by
  rw [perimC_moment, show (((2 : ℕ) : ℝ) + 1) / 2 = 3 / 2 by norm_num, perimC_gamma_three_halves]
  ring

/-- `∫_0^∞ y⁴ e^{-y²} dy = 3 √π / 8`. -/
lemma perimC_moment_four :
    ∫ y in Ioi (0 : ℝ), y ^ 4 * Real.exp (-y ^ 2) = 3 * Real.sqrt Real.pi / 8 := by
  rw [perimC_moment, show (((4 : ℕ) : ℝ) + 1) / 2 = 5 / 2 by norm_num, perimC_gamma_five_halves]
  ring

/-- Scaling of the half-line Gaussian moments. -/
lemma perimC_scaled_moment (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0 : ℝ), (s / t) ^ n * Real.exp (-(s / t) ^ 2)
      = t * ∫ y in Ioi (0 : ℝ), y ^ n * Real.exp (-y ^ 2) := by
  have := integral_comp_mul_left_Ioi (fun y : ℝ => y ^ n * Real.exp (-y ^ 2)) 0
    (inv_pos.mpr ht)
  simp only [mul_zero, smul_eq_mul, inv_inv] at this
  rw [← this]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  simp [div_eq_inv_mul]

lemma perimC_integrableOn_scaled_moment (n : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => (s / t) ^ n * Real.exp (-(s / t) ^ 2)) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => y ^ n * Real.exp (-y ^ 2)) 0 (inv_pos.mpr ht)).mpr
  simp only [mul_zero] at h
  refine (h (perimC_integrableOn_moment n)).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp [div_eq_inv_mul]

/-- **The density comparison.**  If `φ` is bounded on `[h, ∞)` by `φ(max h 0)`, then
`∫_{z>h} f(z-h) dγ₁ ≤ φ(max h 0) ∫_0^∞ f`. -/
lemma perimC_integral_le_density (h : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfi : IntegrableOn f (Ioi 0)) :
    ∫ z in Ioi h, f (z - h) ∂(gaussianReal 0 1)
      ≤ gaussianPDFReal 0 1 (max h 0) * ∫ s in Ioi (0 : ℝ), f s := by
  rw [perimC_setIntegral_gauss measurableSet_Ioi]
  have hint : IntegrableOn (fun z => gaussianPDFReal 0 1 (max h 0) * f (z - h)) (Ioi h) :=
    (perimC_integrableOn_Ioi_sub h f hfi).const_mul _
  have hint2 : IntegrableOn (fun z => gaussianPDFReal 0 1 z * f (z - h)) (Ioi h) := by
    refine Integrable.mono' hint ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 1).mul
        (hf.measurable.comp (measurable_id.sub_const h))).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      have hz0 : 0 ≤ z - h := by have : h < z := hz; linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 1 z) (hf0 _ hz0))]
      exact mul_le_mul_of_nonneg_right (perimC_phi_le_max (le_of_lt hz)) (hf0 _ hz0)
  calc _ ≤ ∫ z in Ioi h, gaussianPDFReal 0 1 (max h 0) * f (z - h) :=
        setIntegral_mono_on hint2 hint measurableSet_Ioi
          (fun z hz => mul_le_mul_of_nonneg_right (perimC_phi_le_max hz.le)
            (hf0 _ (by have : h < z := hz; linarith)))
    _ = _ := by rw [integral_const_mul, perimC_setIntegral_Ioi_sub]

/-- The three weighted moments of the excess are dominated by `t φ(h₊)` times a half-line
Gaussian moment. -/
lemma perimC_moment_bound (n : ℕ) (h : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ z in Ioi h, (perimCP h z / t) ^ n * perimCW h t z ∂(gaussianReal 0 1)
      ≤ gaussianPDFReal 0 1 (max h 0) *
        (t * ∫ y in Ioi (0 : ℝ), y ^ n * Real.exp (-y ^ 2)) := by
  have hcongr : ∫ z in Ioi h, (perimCP h z / t) ^ n * perimCW h t z ∂(gaussianReal 0 1)
      = ∫ z in Ioi h, (fun s : ℝ => (s / t) ^ n * Real.exp (-(s / t) ^ 2)) (z - h)
          ∂(gaussianReal 0 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    have hz' : h ≤ z := le_of_lt hz
    simp only [perimCW_eq, perimCP_of_le hz']
  rw [hcongr, ← perimC_scaled_moment n ht]
  refine perimC_integral_le_density h ?_ ?_ (perimC_integrableOn_scaled_moment n ht)
  · exact (((continuous_id.div_const t).pow n).mul
      (Real.continuous_exp.comp ((continuous_id.div_const t).pow 2).neg))
  · intro s hs
    exact mul_nonneg (pow_nonneg (div_nonneg hs ht.le) n) (Real.exp_pos _).le

lemma perimC_sqrt_pi_le : Real.sqrt Real.pi ≤ 17725 / 10000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_d4]

lemma perimC_sqrt_pi_nonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _

/-- **(P3), exact form.**  `q ≤ (√π/2) t φ(h₊)`. -/
theorem perimCQ_le_sqrtPi (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCQ h t ≤ (Real.sqrt Real.pi / 2) * (t * gaussianPDFReal 0 1 (max h 0)) := by
  have := perimC_moment_bound 0 h ht
  rw [perimC_moment_zero] at this
  simp only [pow_zero, one_mul] at this
  unfold perimCQ
  linarith

/-- **(P3), exact form.**  `e2 ≤ (√π/4) t φ(h₊)`. -/
theorem perimCE2_le_sqrtPi (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCE2 h t ≤ (Real.sqrt Real.pi / 4) * (t * gaussianPDFReal 0 1 (max h 0)) := by
  have := perimC_moment_bound 2 h ht
  rw [perimC_moment_two] at this
  unfold perimCE2
  linarith

/-- **(P3), exact form.**  `e4 ≤ (3√π/8) t φ(h₊)`. -/
theorem perimCE4_le_sqrtPi (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCE4 h t ≤ (3 * Real.sqrt Real.pi / 8) * (t * gaussianPDFReal 0 1 (max h 0)) := by
  have := perimC_moment_bound 4 h ht
  rw [perimC_moment_four] at this
  unfold perimCE4
  linarith

/-- **(P3)**  `q ≤ 0.887 t φ(h₊)`. -/
theorem perimCQ_le_density (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCQ h t ≤ (887 / 1000 : ℝ) * (t * gaussianPDFReal 0 1 (max h 0)) := by
  refine (perimCQ_le_sqrtPi h ht).trans ?_
  have hp : 0 ≤ t * gaussianPDFReal 0 1 (max h 0) :=
    mul_nonneg ht.le (gaussianPDFReal_nonneg 0 1 _)
  refine mul_le_mul_of_nonneg_right ?_ hp
  linarith [perimC_sqrt_pi_le]

/-- **(P3)**  `e2 ≤ 0.4432 t φ(h₊)`.  (The constant `0.443` of the feasibility study is false:
for `h = 0`, `t → 0` the ratio tends to `√π/4 = 0.44311…`.) -/
theorem perimCE2_le_density (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCE2 h t ≤ (4432 / 10000 : ℝ) * (t * gaussianPDFReal 0 1 (max h 0)) := by
  refine (perimCE2_le_sqrtPi h ht).trans ?_
  have hp : 0 ≤ t * gaussianPDFReal 0 1 (max h 0) :=
    mul_nonneg ht.le (gaussianPDFReal_nonneg 0 1 _)
  refine mul_le_mul_of_nonneg_right ?_ hp
  linarith [perimC_sqrt_pi_le]

/-- **(P3)**  `e4 ≤ 0.665 t φ(h₊)`. -/
theorem perimCE4_le_density (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCE4 h t ≤ (665 / 1000 : ℝ) * (t * gaussianPDFReal 0 1 (max h 0)) := by
  refine (perimCE4_le_sqrtPi h ht).trans ?_
  have hp : 0 ≤ t * gaussianPDFReal 0 1 (max h 0) :=
    mul_nonneg ht.le (gaussianPDFReal_nonneg 0 1 _)
  refine mul_le_mul_of_nonneg_right ?_ hp
  linarith [perimC_sqrt_pi_le]

/-! ### (P5) Comparison of `u` with the activity probability -/

lemma perimC_measureReal_eq_integral (S : Set ℝ) :
    (gaussianReal 0 1).real S = ∫ x in S, gaussianPDFReal 0 1 x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero S,
    ENNReal.toReal_ofReal (integral_nonneg (fun z => gaussianPDFReal_nonneg 0 1 z))]

/-- Mass of an interval under a pointwise density bound. -/
lemma perimC_real_Ioc_le {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ z ∈ Ioc a b, gaussianPDFReal 0 1 z ≤ C) :
    (gaussianReal 0 1).real (Ioc a b) ≤ (b - a) * C := by
  rw [perimC_measureReal_eq_integral]
  have h1 : ∫ x in Ioc a b, gaussianPDFReal 0 1 x ≤ ∫ _ in Ioc a b, C :=
    setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
      (integrableOn_const (by simp)) measurableSet_Ioc hC
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul] at h1
  exact h1

/-- `u ≥ (1 - e^{-s²/t²}) Φ̄(h+s)` for every `s ≥ 0`. -/
theorem perimCU_ge_tail (h : ℝ) {t s : ℝ} (hs : 0 ≤ s) :
    (1 - Real.exp (-(s / t) ^ 2)) * perimCTail (h + s) ≤ perimCU h t := by
  have hsub : Ioi (h + s) ⊆ Ioi h := Ioi_subset_Ioi (by linarith)
  have h1 : ∫ z in Ioi (h + s), (1 - Real.exp (-(s / t) ^ 2)) ∂(gaussianReal 0 1)
      ≤ ∫ z in Ioi (h + s), (1 - perimCW h t z) ∂(gaussianReal 0 1) := by
    refine setIntegral_mono_on (integrableOn_const (by simp))
      (perimC_integrableOn_one_sub h t _) measurableSet_Ioi (fun z hz => ?_)
    have hz' : h + s < z := hz
    rw [perimCW_eq, perimCP_of_le (by linarith)]
    have hsz : s ≤ z - h := by linarith
    have hsq : (s / t) ^ 2 ≤ ((z - h) / t) ^ 2 := by
      rw [div_pow, div_pow]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hsz 2) (sq_nonneg t)
    have : Real.exp (-((z - h) / t) ^ 2) ≤ Real.exp (-(s / t) ^ 2) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have h2 : ∫ z in Ioi (h + s), (1 - perimCW h t z) ∂(gaussianReal 0 1) ≤ perimCU h t :=
    setIntegral_mono_set (perimC_integrableOn_one_sub h t _)
      (ae_of_all _ (fun z => perimC_one_sub_nonneg h t z)) (ae_of_all _ hsub)
  rw [setIntegral_const, smul_eq_mul] at h1
  unfold perimCTail
  linarith

lemma perimC_exp_neg_one_le : Real.exp (-1) ≤ 368 / 1000 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith [Real.exp_one_gt_d9]

/-- **(P5a)**  `u ≥ 0.632 Φ̄(h + t)`. -/
theorem perimCU_ge_tail_add (h : ℝ) {t : ℝ} (ht : 0 < t) :
    (632 / 1000 : ℝ) * perimCTail (h + t) ≤ perimCU h t := by
  have h1 := perimCU_ge_tail h (t := t) ht.le
  rw [div_self ht.ne', one_pow] at h1
  have h2 := perimC_exp_neg_one_le
  have h3 : 0 ≤ perimCTail (h + t) := perimCTail_nonneg _
  nlinarith [mul_nonneg h3 (by linarith : (0 : ℝ) ≤ 1 - Real.exp (-1) - 632 / 1000)]

/-- **(P5b)**  `q ≤ P(Z > h) = Φ̄(h)`. -/
theorem perimCQ_le_perimCTail (h t : ℝ) : perimCQ h t ≤ perimCTail h := by
  have h1 : ∫ z in Ioi h, perimCW h t z ∂(gaussianReal 0 1)
      ≤ ∫ _ in Ioi h, (1 : ℝ) ∂(gaussianReal 0 1) :=
    setIntegral_mono_on (perimC_integrableOn_w h t _) (integrableOn_const (by simp))
      measurableSet_Ioi (fun z _ => perimCW_le_one h t z)
  rw [setIntegral_const, smul_eq_mul, mul_one] at h1
  exact h1

lemma perimC_one_sub_exp_ge {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h1 := Real.add_one_le_exp x
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-x) := Real.exp_pos _
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

/-- **(P5c)**  `Φ̄(h) ≤ 2 (1 + 4 (1 + h₊)² t²) u`. -/
theorem perimCTail_le_mul_perimCU (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCTail h ≤ 2 * (1 + 4 * (1 + max h 0) ^ 2 * t ^ 2) * perimCU h t := by
  set D : ℝ := 1 + max h 0 with hD
  have hD1 : 1 ≤ D := by have := le_max_right h 0; linarith
  have hDpos : 0 < D := by linarith
  set s : ℝ := 1 / (2 * D) with hs
  have hspos : 0 < s := by positivity
  have hphi : gaussianPDFReal 0 1 (max h 0) ≤ D * perimCTail h := perimC_phi_max_le_mul_tail h
  have hslice : (gaussianReal 0 1).real (Ioc h (h + s)) ≤ s * (D * perimCTail h) := by
    have := perimC_real_Ioc_le (a := h) (b := h + s) (C := D * perimCTail h) (by linarith)
      (fun z hz => (perimC_phi_le_max hz.1.le).trans hphi)
    simpa using this
  have hs2 : s * (D * perimCTail h) = perimCTail h / 2 := by rw [hs]; field_simp
  have hsplit : perimCTail h = (gaussianReal 0 1).real (Ioc h (h + s)) + perimCTail (h + s) := by
    unfold perimCTail
    rw [← measureReal_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi,
      Set.Ioc_union_Ioi_eq_Ioi (by linarith)]
  have hmass : perimCTail h ≤ 2 * perimCTail (h + s) := by linarith
  have hu := perimCU_ge_tail h (t := t) hspos.le
  set x : ℝ := (s / t) ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg _
  set K : ℝ := 1 + 4 * D ^ 2 * t ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hxK : x / (1 + x) = 1 / K := by
    rw [hx, hs, hK]
    field_simp
    ring
  have hge : 1 / K ≤ 1 - Real.exp (-x) := hxK ▸ perimC_one_sub_exp_ge hx0
  have hT0 : 0 ≤ perimCTail (h + s) := perimCTail_nonneg _
  have h3 : 1 / K * perimCTail (h + s) ≤ perimCU h t :=
    (mul_le_mul_of_nonneg_right hge hT0).trans hu
  have h4 : perimCTail (h + s) ≤ K * perimCU h t := by
    rw [one_div, inv_mul_le_iff₀ hKpos] at h3
    exact h3
  calc perimCTail h ≤ 2 * perimCTail (h + s) := hmass
    _ ≤ 2 * (K * perimCU h t) := by linarith
    _ = 2 * K * perimCU h t := by ring

/-- **(P5c), the form of the feasibility study.**
`Φ̄(h) ≤ 3.2 (1 + 4 (1 + h₊)² t²) u`. -/
theorem perimCTail_le_mul_perimCU_32 (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCTail h ≤ (32 / 10 : ℝ) * (1 + 4 * (1 + max h 0) ^ 2 * t ^ 2) * perimCU h t := by
  refine (perimCTail_le_mul_perimCU h ht).trans ?_
  have hK : 0 < 1 + 4 * (1 + max h 0) ^ 2 * t ^ 2 := by positivity
  have hu := perimCU_nonneg h t
  nlinarith [mul_nonneg hK.le hu]

/-- **(P5)**, the chain `q ≤ Φ̄(h) ≤ κ u`. -/
theorem perimCQ_le_mul_perimCU (h : ℝ) {t : ℝ} (ht : 0 < t) :
    perimCQ h t ≤ (32 / 10 : ℝ) * (1 + 4 * (1 + max h 0) ^ 2 * t ^ 2) * perimCU h t :=
  (perimCQ_le_perimCTail h t).trans (perimCTail_le_mul_perimCU_32 h ht)

/-! ### (Pb) Big coordinates -/

lemma perimC_phi_le_of_le {H h : ℝ} (hH : 0 ≤ H) (hHh : H ≤ h) :
    gaussianPDFReal 0 1 h ≤ gaussianPDFReal 0 1 H :=
  perimC_phi_le_of_abs_le (by rw [abs_of_nonneg hH, abs_of_nonneg (hH.trans hHh)]; exact hHh)

lemma perimC_exp_gauss_integral :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 2 : ℝ) * s ^ 2) = Real.sqrt (2 * Real.pi) / 2 := by
  rw [integral_gaussian_Ioi]
  congr 2
  ring

/-- **Gaussian tail with the factor `1/2`.**  `Φ̄(h) ≤ e^{-h²/2} / 2` for `h ≥ 0`. -/
theorem perimCTail_le_exp_div_two {h : ℝ} (hh : 0 ≤ h) :
    perimCTail h ≤ Real.exp (-h ^ 2 / 2) / 2 := by
  rw [perimCTail_eq_integral]
  have hg : IntegrableOn (fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have hint : IntegrableOn
      (fun z : ℝ => gaussianPDFReal 0 1 h * Real.exp (-(1 / 2 : ℝ) * (z - h) ^ 2)) (Ioi h) :=
    (perimC_integrableOn_Ioi_sub h (fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s ^ 2)) hg).const_mul _
  have hpt : ∀ z ∈ Ioi h, gaussianPDFReal 0 1 z ≤
      gaussianPDFReal 0 1 h * Real.exp (-(1 / 2 : ℝ) * (z - h) ^ 2) := by
    intro z hz
    have hz' : h < z := hz
    rw [perimC_phi_eq, perimC_phi_eq, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    nlinarith [mul_nonneg hh (by linarith : (0 : ℝ) ≤ z - h)]
  calc ∫ z in Ioi h, gaussianPDFReal 0 1 z
      ≤ ∫ z in Ioi h, gaussianPDFReal 0 1 h * Real.exp (-(1 / 2 : ℝ) * (z - h) ^ 2) :=
        setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn hint
          measurableSet_Ioi hpt
    _ = gaussianPDFReal 0 1 h * (Real.sqrt (2 * Real.pi) / 2) := by
        rw [integral_const_mul,
          perimC_setIntegral_Ioi_sub h (fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s ^ 2)),
          perimC_exp_gauss_integral]
    _ = Real.exp (-h ^ 2 / 2) / 2 := by
        rw [perimC_phi_eq]
        have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
        field_simp

/-- **Big coordinates, tail.**  For `h ≥ H ≥ 0`: `Φ̄(h) ≤ e^{-H²/2} / 2`. -/
theorem perimCTail_le_exp_div_two_of_ge {H h : ℝ} (hH : 0 ≤ H) (hHh : H ≤ h) :
    perimCTail h ≤ Real.exp (-H ^ 2 / 2) / 2 := by
  refine (perimCTail_le_exp_div_two (hH.trans hHh)).trans ?_
  have : H ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hH hHh 2
  have := Real.exp_le_exp.mpr (by linarith : -h ^ 2 / 2 ≤ -H ^ 2 / 2)
  linarith

/-- **Big coordinates, density.**  For `h ≥ H ≥ 0`: `φ(h) ≤ φ(H) = e^{-H²/2} / √(2π)`. -/
theorem perimC_phi_le_exp_of_ge {H h : ℝ} (hH : 0 ≤ H) (hHh : H ≤ h) :
    gaussianPDFReal 0 1 h ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-H ^ 2 / 2) := by
  rw [← perimC_phi_eq]
  exact perimC_phi_le_of_le hH hHh

/-- The threshold `H = √(2 log m)`. -/
noncomputable def perimCBigLevel (m : ℕ) : ℝ := Real.sqrt (2 * Real.log m)

lemma perimCBigLevel_nonneg (m : ℕ) : 0 ≤ perimCBigLevel m := Real.sqrt_nonneg _

/-- `H ≥ 1` as soon as `m ≥ 2`. -/
theorem perimCBigLevel_ge_one {m : ℕ} (hm : 2 ≤ m) : 1 ≤ perimCBigLevel m := by
  unfold perimCBigLevel
  refine Real.le_sqrt_of_sq_le ?_
  have h2 : Real.log 2 ≤ Real.log m := by
    refine Real.log_le_log (by norm_num) ?_
    exact_mod_cast hm
  linarith [Real.log_two_gt_d9]

/-- `e^{-H²/2} = 1/m`. -/
theorem perimC_exp_bigLevel {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-perimCBigLevel m ^ 2 / 2) = 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  unfold perimCBigLevel
  rw [Real.sq_sqrt (by linarith)]
  rw [show -(2 * Real.log m) / 2 = -Real.log m by ring, Real.exp_neg, Real.exp_log hm0]
  simp

/-- **Big coordinates, total tail.**  For `m ≥ 2` coordinates `h_j` and `H = √(2 log m)`,
`∑_{h_j ≥ H} Φ̄(h_j) ≤ 1/2`. -/
theorem perimC_sum_big_tail_le {ι : Type*} [Fintype ι] {m : ℕ} (hcard : Fintype.card ι = m)
    (hm : 2 ≤ m) (h : ι → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => perimCBigLevel m ≤ h j), perimCTail (h j) ≤ 1 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hterm : ∀ j ∈ Finset.univ.filter (fun j => perimCBigLevel m ≤ h j),
      perimCTail (h j) ≤ 1 / (2 * (m : ℝ)) := by
    intro j hj
    have hj' : perimCBigLevel m ≤ h j := (Finset.mem_filter.mp hj).2
    refine (perimCTail_le_exp_div_two_of_ge (perimCBigLevel_nonneg m) hj').trans ?_
    rw [perimC_exp_bigLevel (by omega)]
    apply le_of_eq
    field_simp
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((Finset.univ.filter (fun j => perimCBigLevel m ≤ h j)).card : ℝ) ≤ m := by
    have := Finset.card_filter_le (Finset.univ : Finset ι) (fun j => perimCBigLevel m ≤ h j)
    rw [Finset.card_univ, hcard] at this
    exact_mod_cast this
  calc _ ≤ (m : ℝ) * (1 / (2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 1 / 2 := by field_simp

/-- **Big coordinates, total density.**  For `m ≥ 2` coordinates and `H = √(2 log m)`,
`∑_{h_j ≥ H} φ(h_j) ≤ 1/√(2π) ≤ 0.4`. -/
theorem perimC_sum_big_phi_le {ι : Type*} [Fintype ι] {m : ℕ} (hcard : Fintype.card ι = m)
    (hm : 2 ≤ m) (h : ι → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => perimCBigLevel m ≤ h j), gaussianPDFReal 0 1 (h j)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hterm : ∀ j ∈ Finset.univ.filter (fun j => perimCBigLevel m ≤ h j),
      gaussianPDFReal 0 1 (h j) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 / (m : ℝ)) := by
    intro j hj
    have hj' : perimCBigLevel m ≤ h j := (Finset.mem_filter.mp hj).2
    refine (perimC_phi_le_exp_of_ge (perimCBigLevel_nonneg m) hj').trans (le_of_eq ?_)
    rw [perimC_exp_bigLevel (by omega)]
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((Finset.univ.filter (fun j => perimCBigLevel m ≤ h j)).card : ℝ) ≤ m := by
    have := Finset.card_filter_le (Finset.univ : Finset ι) (fun j => perimCBigLevel m ≤ h j)
    rw [Finset.card_univ, hcard] at this
    exact_mod_cast this
  have hpos : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 / (m : ℝ)) := by positivity
  calc _ ≤ (m : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * (1 / (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hc hpos
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := by field_simp

/-- `1/√(2π) ≤ 2/5`. -/
theorem perimC_inv_sqrt_two_pi_le : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 2 / 5 := by
  have h : (5 / 2 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_d2])
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- **Big coordinates, total density (numeric).** `∑_{h_j ≥ H} φ(h_j) ≤ 0.4`. -/
theorem perimC_sum_big_phi_le_two_fifths {ι : Type*} [Fintype ι] {m : ℕ}
    (hcard : Fintype.card ι = m) (hm : 2 ≤ m) (h : ι → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => perimCBigLevel m ≤ h j), gaussianPDFReal 0 1 (h j)
      ≤ 2 / 5 :=
  (perimC_sum_big_phi_le hcard hm h).trans perimC_inv_sqrt_two_pi_le

end LatticeProb
