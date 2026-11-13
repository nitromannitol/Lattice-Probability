/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.UpperMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.UpperMomentBands




 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

private theorem two_inv_pow_eq (n : ℕ) : ((2 : ℝ)⁻¹) ^ n = ((2 : ℝ) ^ n)⁻¹ := inv_pow _ _

 
def inwardParam (n : ℕ) : ℚ := ((2 : ℚ) ^ (max n 8))⁻¹

theorem inwardParam_pos (n : ℕ) : 0 < inwardParam n := by
  unfold inwardParam; positivity

theorem inwardParam_le (n : ℕ) : ((inwardParam n : ℚ) : ℝ) ≤ 1 / 256 := by
  unfold inwardParam
  push_cast
  rw [one_div]
  apply inv_anti₀ (by norm_num)
  calc (256 : ℝ) = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ (max n 8) := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)

theorem inwardParam_le_scale (n : ℕ) : ((inwardParam n : ℚ) : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  unfold inwardParam
  push_cast
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (le_max_left _ _))

omit [MeasurableSpace Ω] in
 
theorem poly_le_bands_obig {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω)
    {ξ : ℝ} (hξ : 0 ≤ ξ) (n : ℕ) (ω : Ω) :
    Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) ≤
      ENNReal.ofReal ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * T20C.Obig n Y ω)) *
        ∑ i : Fin 4, rectLen ξ (fun x => Y x ω) (band i) := by
  have hc1 := hYc ω
  have h := Exponent.InwardMap.polyAnnularCost_le_four_rectLen (inwardParam n) (inwardParam_pos n)
    (inwardParam_le n) ξ hξ (fun x => Y x ω) hc1.continuous
    (fun z _ => (hc1.differentiable (by norm_num)).differentiableAt)
    (hc1.continuous_fderiv (by norm_num)).continuousOn
  rw [sum_band_rectLen] at h
  refine h.trans (mul_le_mul_left ?_ _)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hG0 : 0 ≤ Exponent.InwardMap.gradientSup (fun x => Y x ω) :=
    Exponent.InwardMap.gradientSup_nonneg _ (hc1.continuous_fderiv (by norm_num)).continuousOn
  calc ((inwardParam n : ℚ) : ℝ) * Exponent.InwardMap.gradientSup (fun x => Y x ω) ≤
      ((2 : ℝ) ^ n)⁻¹ * Exponent.InwardMap.gradientSup (fun x => Y x ω) :=
        mul_le_mul_of_nonneg_right (inwardParam_le_scale n) hG0
    _ ≤ T20C.Obig n Y ω := gradientSup_le_obig hYc n ω

 
theorem upper_moment (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω)) ^ j ∂P ≤
        ENNReal.ofReal ((Real.exp (C * Real.sqrt n + C) * lambdaN ξ W P n) ^ j) := by
  have := hW.isProbabilityMeasure
  obtain ⟨p₀, hp₀, h18⟩ := dddf_prop18 (P := P) hW hξ
  set p : ℝ := min p₀ (1 / 4) with hp_def
  have hp : 0 < p := lt_min hp₀ (by norm_num)
  have hp4 : p ≤ 1 / 4 := min_le_right _ _
  obtain ⟨C₈, c₈, hC₈, hc₈, t18⟩ := h18 p hp (min_le_left _ _)
  obtain ⟨K₀, hK₀, hband⟩ := band_moment hW hp hp4 hC₈ hc₈ t18 (2 * j) (by omega)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  obtain ⟨cg, Kg, hcg, hKg, hobig⟩ :=
    S6U.obig_expMoment (a := 64 * Real.sqrt 2 * j * ξ) (by positivity)
  set C₁ : ℝ := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p with hC₁_def
  have hC₁ : 0 ≤ C₁ := by positivity
  set A : ℝ := (5 / 4 : ℝ) ^ j * (5 * Real.sqrt Kg) * (4 ^ j * 2 * Real.sqrt K₀) with hA_def
  have hA : 0 ≤ A := by positivity
  set C : ℝ := cg + j * C₁ + Real.log (A + 1) with hC_def
  have hlogA : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith)
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, fun n hn => ?_⟩
  
  have ha : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have ha1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y, -, hYae, hYm, hYc, -, -, -, -, -⟩ := exists_C1_modification_phi hW ha ha1
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hφae : ∀ x, phiMN W P 0 n x =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x := by
    intro x
    have h := hφ.ae_eq x
    rwa [two_inv_pow_eq, pow_zero] at h
  have hae : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 n x ω :=
    ae_eq_of_continuous_modification (fun ω => (hYc ω).continuous) hφ.cont
      (fun x => (hYae x).trans (hφae x).symm)
  
  set O : Ω → ℝ := fun ω => T20C.Obig n Y ω with hO
  set X : Fin 4 → Ω → ℝ := fun i ω => lenObs ξ (phiMN W P 0 n) (band i) ω with hX
  set S : Ω → ℝ := fun ω => ∑ i : Fin 4, X i ω with hS
  have hX0 : ∀ i ω, 0 ≤ X i ω := fun i ω => ENNReal.toReal_nonneg
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Finset.sum_nonneg fun i _ => hX0 i ω
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_lenObs hφ.cont hφ.meas _
  have hSm : Measurable S := Finset.measurable_sum _ fun i _ => hXm i
  have hOm : AEMeasurable O P := aemeasurable_obig hW n hYae hYc
  set F : Ω → ℝ := fun ω => ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * O ω)) ^ j with hF
  set G : Ω → ℝ := fun ω => S ω ^ j with hG
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => by positivity
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => pow_nonneg (hS0 ω) _
  
  have hpath : ∀ᵐ ω ∂P, (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω)) ^ j ≤
      ENNReal.ofReal (F ω * G ω) := by
    filter_upwards [hae] with ω hω
    have hfun : (fun x => phiMN W P 0 n x ω) = fun x => Y x ω := funext fun x => (hω x).symm
    have h1 := poly_le_bands_obig hYc hξ.le n ω
    have hbands : ∑ i : Fin 4, rectLen ξ (fun x => Y x ω) (band i) = ENNReal.ofReal (S ω) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hX0 i ω)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hfun]
      exact (ofReal_lenObs hφ.cont (band i) (band_dims i).1 (band_dims i).2 ω).symm
    rw [hbands, ← ENNReal.ofReal_mul (by positivity)] at h1
    rw [hfun]
    calc (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω)) ^ j ≤
        (ENNReal.ofReal ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * O ω) * S ω)) ^ j :=
          pow_le_pow_left₀ bot_le h1 j
      _ = ENNReal.ofReal (F ω * G ω) := by
          rw [← ENNReal.ofReal_pow (mul_nonneg (by positivity) (hS0 ω)), mul_pow]
  
  have hFsq : ∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂P ≤
      ENNReal.ofReal ((5 / 4 : ℝ) ^ (2 * j) * (25 * Kg * Real.exp (cg * Real.sqrt n))) := by
    have e : ∀ ω, ENNReal.ofReal (F ω ^ 2) = ENNReal.ofReal ((5 / 4 : ℝ) ^ (2 * j)) *
        ENNReal.ofReal (Real.exp (64 * Real.sqrt 2 * j * ξ * O ω)) := by
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [hF]
      rw [← pow_mul, mul_pow, ← Real.exp_nat_mul, pow_mul]
      congr 1
      · ring
      · congr 1; push_cast; ring
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact hobig hW n hn Y hYae hYc
  
  have hGsq : ∫⁻ ω, ENNReal.ofReal (G ω ^ 2) ∂P ≤
      ENNReal.ofReal ((4 : ℝ) ^ (2 * j) * (4 * (K₀ * (LambdaN ξ W P n (ENNReal.ofReal p) *
        ellN ξ W P n (ENNReal.ofReal p)) ^ (2 * j)))) := by
    have hpow : ∀ ω, G ω ^ 2 ≤ (4 : ℝ) ^ (2 * j) * ∑ i : Fin 4, X i ω ^ (2 * j) := by
      intro ω
      have hm : 2 * j = (2 * j - 1) + 1 := by omega
      have h := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i => X i ω) (fun i _ => hX0 i ω) (2 * j - 1)
      rw [← hm, Finset.card_univ, Fintype.card_fin] at h
      calc G ω ^ 2 = S ω ^ (2 * j) := by simp only [hG]; rw [← pow_mul, mul_comm]
        _ ≤ ((4 : ℕ) : ℝ) ^ (2 * j - 1) * ∑ i : Fin 4, X i ω ^ (2 * j) := h
        _ ≤ (4 : ℝ) ^ (2 * j) * ∑ i : Fin 4, X i ω ^ (2 * j) := by
          apply mul_le_mul_of_nonneg_right _
            (Finset.sum_nonneg fun i _ => pow_nonneg (hX0 i ω) _)
          push_cast
          exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc ∫⁻ ω, ENNReal.ofReal (G ω ^ 2) ∂P ≤
        ∫⁻ ω, ENNReal.ofReal ((4 : ℝ) ^ (2 * j)) *
          ∑ i : Fin 4, ENNReal.ofReal (X i ω ^ (2 * j)) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (hX0 i ω) _),
            ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpow ω)
      _ = ENNReal.ofReal ((4 : ℝ) ^ (2 * j)) *
          ∑ i : Fin 4, ∫⁻ ω, ENNReal.ofReal (X i ω ^ (2 * j)) ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finsetSum _ fun i _ => ((hXm i).pow_const _).ennreal_ofReal]
      _ ≤ ENNReal.ofReal ((4 : ℝ) ^ (2 * j)) *
          ∑ _i : Fin 4, ENNReal.ofReal (K₀ * (LambdaN ξ W P n (ENNReal.ofReal p) *
            ellN ξ W P n (ENNReal.ofReal p)) ^ (2 * j)) := by
          gcongr with i
          exact hband n i
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity)]
          norm_num
  
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := by
    rw [← ofReal_half_eq']; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n
  have hΛ0 : 0 < LambdaN ξ W P n (ENNReal.ofReal p) := T20B.LambdaN_pos hW hpq0 hpq n
  have hΛ : LambdaN ξ W P n (ENNReal.ofReal p) ≤ Real.exp (C₁ * Real.sqrt n) :=
    Inputs.Gaussian.quantile_ratio_sqrt hW ξ hp (by linarith) n
  have hℓ : ellN ξ W P n (ENNReal.ofReal p) ≤ lambdaN ξ W P n := T20B.ellN_le_lambdaN hpq0 hpq n
  have hlam0 : 0 < lambdaN ξ W P n := hℓ0.trans_le hℓ
  have hΛℓ : LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
      Real.exp (C₁ * Real.sqrt n) * lambdaN ξ W P n :=
    mul_le_mul hΛ hℓ hℓ0.le (Real.exp_pos _).le
  
  have hCS := lintegral_ofReal_mul_le hF0 hG0
    ((Real.continuous_exp.measurable.comp_aemeasurable
      (hOm.const_mul (32 * Real.sqrt 2 * ξ))).const_mul (5 / 4 : ℝ) |>.pow_const j)
    (hSm.pow_const j).aemeasurable (by positivity)
    (mul_nonneg (by positivity) (mul_nonneg (by norm_num)
      (mul_nonneg hK₀ (pow_nonneg (mul_nonneg hΛ0.le hℓ0.le) _)))) hFsq hGsq
  
  refine (lintegral_mono_ae hpath).trans (hCS.trans (ENNReal.ofReal_le_ofReal ?_))
  set Λℓ := LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)
  have hΛℓ0 : 0 ≤ Λℓ := by positivity
  have hsqrt1 : Real.sqrt ((5 / 4 : ℝ) ^ (2 * j) * (25 * Kg * Real.exp (cg * Real.sqrt n))) =
      (5 / 4 : ℝ) ^ j * (5 * Real.sqrt Kg) * Real.exp (cg * Real.sqrt n / 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [show (5 / 4 : ℝ) ^ (2 * j) = ((5 / 4 : ℝ) ^ j) ^ 2 by rw [← pow_mul, mul_comm],
      Real.sqrt_sq (by positivity), show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show Real.exp (cg * Real.sqrt n) = Real.exp (cg * Real.sqrt n / 2) ^ 2 by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring, Real.sqrt_sq (Real.exp_pos _).le]
    ring
  have hsqrt2 : Real.sqrt ((4 : ℝ) ^ (2 * j) * (4 * (K₀ * Λℓ ^ (2 * j)))) =
      (4 ^ j * 2 * Real.sqrt K₀) * Λℓ ^ j := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hK₀]
    rw [show (4 : ℝ) ^ (2 * j) = ((4 : ℝ) ^ j) ^ 2 by rw [← pow_mul, mul_comm],
      Real.sqrt_sq (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      show Λℓ ^ (2 * j) = (Λℓ ^ j) ^ 2 by rw [← pow_mul, mul_comm],
      Real.sqrt_sq (by positivity)]
    ring
  rw [hsqrt1, hsqrt2]
  have hsqn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hΛℓj : Λℓ ^ j ≤ (Real.exp (C₁ * Real.sqrt n) * lambdaN ξ W P n) ^ j :=
    pow_le_pow_left₀ hΛℓ0 hΛℓ j
  have hexp : A * Real.exp (cg * Real.sqrt n / 2) * Real.exp (C₁ * Real.sqrt n) ^ j ≤
      Real.exp (C * Real.sqrt n + C) ^ j := by
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have hA1 : A ≤ Real.exp (Real.log (A + 1)) := by
      rw [Real.exp_log (by linarith)]; linarith
    calc A * Real.exp (cg * Real.sqrt n / 2) * Real.exp (j * (C₁ * Real.sqrt n)) ≤
        Real.exp (Real.log (A + 1)) * Real.exp (cg * Real.sqrt n / 2) *
          Real.exp (j * (C₁ * Real.sqrt n)) := by gcongr
      _ = Real.exp (Real.log (A + 1) + cg * Real.sqrt n / 2 + j * (C₁ * Real.sqrt n)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (j * (C * Real.sqrt n + C)) := by
          apply Real.exp_le_exp.2
          have h1 : C * Real.sqrt n + C ≤ j * (C * Real.sqrt n + C) :=
            le_mul_of_one_le_left (by positivity) hjr
          have h2 : Real.log (A + 1) + cg * Real.sqrt n / 2 + j * (C₁ * Real.sqrt n) ≤
              C * Real.sqrt n + C := by
            simp only [hC_def]
            nlinarith [mul_nonneg hcg hsqn, mul_nonneg (mul_nonneg hj0.le hC₁) hsqn]
          linarith
  calc (5 / 4 : ℝ) ^ j * (5 * Real.sqrt Kg) * Real.exp (cg * Real.sqrt n / 2) *
        ((4 ^ j * 2 * Real.sqrt K₀) * Λℓ ^ j) =
      A * Real.exp (cg * Real.sqrt n / 2) * Λℓ ^ j := by simp only [hA_def]; ring
    _ ≤ A * Real.exp (cg * Real.sqrt n / 2) *
        (Real.exp (C₁ * Real.sqrt n) * lambdaN ξ W P n) ^ j := by gcongr
    _ = A * Real.exp (cg * Real.sqrt n / 2) * Real.exp (C₁ * Real.sqrt n) ^ j *
        lambdaN ξ W P n ^ j := by rw [mul_pow]; ring
    _ ≤ Real.exp (C * Real.sqrt n + C) ^ j * lambdaN ξ W P n ^ j :=
        mul_le_mul_of_nonneg_right hexp (pow_nonneg hlam0.le _)
    _ = (Real.exp (C * Real.sqrt n + C) * lambdaN ξ W P n) ^ j := (mul_pow _ _ _).symm



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
