/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Slope at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.MeanRecursion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.SlopeAssembly
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.LinearLower




 













set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

theorem lambdaN_pos' (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) : 0 < lambdaN ξ W P n := by
  have := hW.isProbabilityMeasure
  have hpq0 : 0 < ENNReal.ofReal (1 / 4 : ℝ) := ENNReal.ofReal_pos.2 (by norm_num)
  have hpq : ENNReal.ofReal (1 / 4 : ℝ) ≤ 2⁻¹ := by
    rw [← ofReal_half_eq']; exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact (T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n).trans_le
    (T20B.ellN_le_lambdaN hpq0 hpq n)

 
theorem moment_package (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ n : ℕ, 1 ≤ n →
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P) ≠ ⊤ ∧
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ^ 2 ∂P) ≠ ⊤ ∧
      Real.exp (-(Cm * Real.sqrt n + Cm)) * lambdaN ξ W P n ≤
        (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P).toReal ∧
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P).toReal ≤
        Real.exp (Cm * Real.sqrt n + Cm) * lambdaN ξ W P n ∧
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ^ 2 ∂P).toReal ≤
        (Real.exp (Cm * Real.sqrt n + Cm) * lambdaN ξ W P n) ^ 2 := by
  obtain ⟨CL, hCL, hlow⟩ := lower_moment hW ξ
  obtain ⟨C1, hC1, hup1⟩ := upper_moment hW hξ 1 le_rfl
  obtain ⟨C2, hC2, hup2⟩ := upper_moment hW hξ 2 (by norm_num)
  set Cm := max CL (max C1 C2)
  have hCLm : CL ≤ Cm := le_max_left _ _
  have hC1m : C1 ≤ Cm := (le_max_left _ _).trans (le_max_right _ _)
  have hC2m : C2 ≤ Cm := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Cm, hCL.trans hCLm, fun n hn => ?_⟩
  have hlam := lambdaN_pos' hW ξ n
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h1 := hup1 n hn
  have h2 := hup2 n hn
  simp only [pow_one] at h1
  have hfin1 : (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hfin2 : (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ^ 2 ∂P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have hexpU : ∀ C : ℝ, C ≤ Cm → Real.exp (C * Real.sqrt n + C) ≤
      Real.exp (Cm * Real.sqrt n + Cm) := fun C hC =>
    Real.exp_le_exp.2 (by nlinarith)
  refine ⟨hfin1, hfin2, ?_, ?_, ?_⟩
  · refine le_trans ?_ ((ENNReal.ofReal_le_iff_le_toReal hfin1).1 (hlow n))
    apply mul_le_mul_of_nonneg_right _ hlam.le
    exact Real.exp_le_exp.2 (by nlinarith)
  · refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h1).trans ?_
    exact mul_le_mul_of_nonneg_right (hexpU C1 hC1m) hlam.le
  · refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h2).trans ?_
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (hexpU C2 hC2m) hlam.le) 2

 
theorem sqrt_le_rpow_two_thirds {m k : ℕ} (hm : 1 ≤ m) :
    Real.sqrt (m : ℝ) ≤ ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Real.sqrt_eq_rpow]
  calc (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
    _ ≤ ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
          (by norm_num)

 
theorem real_recursion (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hmom : ∀ n : ℕ, 1 ≤ n →
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P) ≠ ⊤ ∧
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ^ 2 ∂P) ≠ ⊤ ∧
      Real.exp (-(Cm * Real.sqrt n + Cm)) * lambdaN ξ W P n ≤
        (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P).toReal ∧
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P).toReal ≤
        Real.exp (Cm * Real.sqrt n + Cm) * lambdaN ξ W P n ∧
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ^ 2 ∂P).toReal ≤
        (Real.exp (Cm * Real.sqrt n + Cm) * lambdaN ξ W P n) ^ 2) :
    ∃ Crec : ℝ, 1 ≤ Crec ∧ ∀ m k : ℕ, 8 ≤ m → 1 ≤ k →
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 (m + k) x ω) ∂P).toReal ≤
        Crec * Real.exp (Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) *
          (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 m x ω) ∂P).toReal *
          (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 k x ω) ∂P).toReal := by
  have := hW.isProbabilityMeasure
  obtain ⟨ca, Ka, hca, hKa, hobA⟩ := S6U.obig_expMoment (a := 108 * ξ) (by positivity)
  obtain ⟨cb, Kb, hcb, hKb, hobB⟩ := S6U.obig_expMoment (a := 54 * ξ) (by positivity)
  set B₀ : ℝ := 5 * Real.sqrt Ka * Real.exp (2 * Cm) + 25 * Kb with hB₀
  set c₀ : ℝ := ca / 2 + 2 * Cm + cb with hc₀
  set Crec : ℝ := 1 + 20 * B₀ + c₀ with hCrec
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hc₀0 : 0 ≤ c₀ := by positivity
  refine ⟨Crec, by linarith, fun m k hm hk => ?_⟩
  set EU : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hfm, hf2m, hlowm, hupm, hsecm⟩ := hmom m hm1
  obtain ⟨hfk, -, -, -, -⟩ := hmom k hk
  have hlamm := lambdaN_pos' hW ξ m
  set μm := (EU m).toReal
  have hμm : 0 < μm := lt_of_lt_of_le (by positivity) hlowm
  
  have ha : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
  have ha1 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y, -, hYae, hYm, hYc, -, -, -, -, -⟩ := exists_C1_modification_phi hW ha ha1
  have hmr := mean_recursion hW hξ.le hm hk (δ := ENNReal.ofReal μm) (ENNReal.ofReal_pos.2 hμm)
    hYae hYm hYc
  
  have hφm := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hφae : ∀ x, phiMN W P 0 m x =ᵐ[P] phi W ((2 : ℝ) ^ m)⁻¹ 1 x := by
    intro x
    have h := hφm.ae_eq x
    rwa [inv_pow, pow_zero] at h
  have hUae : ∀ᵐ ω ∂P, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) =
      Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 m x ω) := by
    filter_upwards [ae_eq_of_continuous_modification (fun ω => (hYc ω).continuous) hφm.cont
      (fun x => (hYae x).trans (hφae x).symm)] with ω hω
    rw [show (fun x => Y x ω) = fun x => phiMN W P 0 m x ω from funext hω]
  
  set f : Ω → ℝ := fun ω => Real.exp (54 * ξ * T20C.Obig m Y ω)
  set g : Ω → ℝ := fun ω => (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω)).toReal
  have hUfin : ∀ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) ≠ ⊤ := fun ω =>
    (polyAnnularCost_lt_top_of_contDiff hξ.le (hYc ω)).ne
  have hgU : ∀ ω, ENNReal.ofReal (g ω) = Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) := fun ω =>
    ENNReal.ofReal_toReal (hUfin ω)
  have hYc' : ∀ ω, Continuous fun x => Y x ω := fun ω => (hYc ω).continuous
  have hUm : Measurable fun ω => Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) :=
    Exponent.PolygonalCost.measurable_polyAnnularCost hYc' hYm ξ
  have hOm := aemeasurable_obig hW m hYae hYc
  have hfm' : AEMeasurable f P :=
    Real.continuous_exp.measurable.comp_aemeasurable (hOm.const_mul (54 * ξ))
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => (Real.exp_pos _).le
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => ENNReal.toReal_nonneg
  set A : ℝ := 25 * Ka * Real.exp (ca * Real.sqrt m)
  set B : ℝ := (Real.exp (Cm * Real.sqrt m + Cm) * lambdaN ξ W P m) ^ 2
  have hfA : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal A := by
    have e : ∀ ω, f ω ^ 2 = Real.exp (108 * ξ * T20C.Obig m Y ω) := by
      intro ω; simp only [f]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    simp only [e]
    exact hobA hW m hm1 Y hYae hYc
  have hgB : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P ≤ ENNReal.ofReal B := by
    have e : ∀ ω, ENNReal.ofReal (g ω ^ 2) = Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) ^ 2 := by
      intro ω; rw [ENNReal.ofReal_pow (hg0 ω), hgU]
    simp only [e]
    rw [lintegral_congr_ae (hUae.mono fun ω hω => by rw [hω])]
    rw [← ENNReal.ofReal_toReal hf2m]
    exact ENNReal.ofReal_le_ofReal hsecm
  have hCS := lintegral_ofReal_mul_le hf0 hg0 hfm' ((hUm.ennreal_toReal).aemeasurable)
    (by positivity) (by positivity) hfA hgB
  have hfB : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal (25 * Kb * Real.exp (cb * Real.sqrt m)) :=
    hobB hW m hm1 Y hYae hYc
  have hJ : ∫⁻ ω, ENNReal.ofReal (Real.exp (54 * ξ * T20C.Obig m Y ω)) *
      (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) + ENNReal.ofReal μm) ∂P ≤
      ENNReal.ofReal (Real.sqrt A * Real.sqrt B + μm * (25 * Kb * Real.exp (cb * Real.sqrt m))) := by
    have e : ∀ ω, ENNReal.ofReal (Real.exp (54 * ξ * T20C.Obig m Y ω)) *
        (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) + ENNReal.ofReal μm) =
        ENNReal.ofReal (f ω * g ω) + ENNReal.ofReal μm * ENNReal.ofReal (f ω) := by
      intro ω
      rw [mul_add, ← hgU, ← ENNReal.ofReal_mul (hf0 ω), mul_comm (ENNReal.ofReal (f ω))]
    simp only [e]
    rw [lintegral_add_right' _ (hfm'.ennreal_ofReal.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hμm.le]
    gcongr
  
  have hEUk := hfk
  set μk := (EU k).toReal
  have hfin_mk : EU (m + k) ≠ ⊤ := (hmom (m + k) (by omega)).1
  have hbound : EU (m + k) ≤ ENNReal.ofReal (μk * (20 *
      (Real.sqrt A * Real.sqrt B + μm * (25 * Kb * Real.exp (cb * Real.sqrt m))))) := by
    refine hmr.trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfk,
      ENNReal.ofReal_mul (by norm_num)]
    gcongr
    · norm_num
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
  
  have hlamle : lambdaN ξ W P m ≤ Real.exp (Cm * Real.sqrt m + Cm) * μm := by
    have h := hlowm
    have he : Real.exp (Cm * Real.sqrt m + Cm) * Real.exp (-(Cm * Real.sqrt m + Cm)) = 1 := by
      rw [← Real.exp_add]; simp
    calc lambdaN ξ W P m = Real.exp (Cm * Real.sqrt m + Cm) *
        (Real.exp (-(Cm * Real.sqrt m + Cm)) * lambdaN ξ W P m) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (Cm * Real.sqrt m + Cm) * μm :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hsA : Real.sqrt A = 5 * Real.sqrt Ka * Real.exp (ca * Real.sqrt m / 2) := by
    simp only [A]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
      show Real.exp (ca * Real.sqrt m) = Real.exp (ca * Real.sqrt m / 2) ^ 2 by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring, Real.sqrt_sq (Real.exp_pos _).le]
  have hsB : Real.sqrt B = Real.exp (Cm * Real.sqrt m + Cm) * lambdaN ξ W P m := by
    simp only [B]
    exact Real.sqrt_sq (by positivity)
  have hsqm : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hkey : Real.sqrt A * Real.sqrt B + μm * (25 * Kb * Real.exp (cb * Real.sqrt m)) ≤
      B₀ * Real.exp (c₀ * Real.sqrt m) * μm := by
    rw [hsA, hsB]
    have h1 : 5 * Real.sqrt Ka * Real.exp (ca * Real.sqrt m / 2) *
        (Real.exp (Cm * Real.sqrt m + Cm) * lambdaN ξ W P m) ≤
        5 * Real.sqrt Ka * Real.exp (2 * Cm) * Real.exp (c₀ * Real.sqrt m) * μm := by
      calc 5 * Real.sqrt Ka * Real.exp (ca * Real.sqrt m / 2) *
          (Real.exp (Cm * Real.sqrt m + Cm) * lambdaN ξ W P m) ≤
          5 * Real.sqrt Ka * Real.exp (ca * Real.sqrt m / 2) *
            (Real.exp (Cm * Real.sqrt m + Cm) * (Real.exp (Cm * Real.sqrt m + Cm) * μm)) := by
            gcongr
        _ = 5 * Real.sqrt Ka * Real.exp (2 * Cm) *
            Real.exp ((ca / 2 + 2 * Cm) * Real.sqrt m) * μm := by
            have hE : Real.exp (ca * Real.sqrt m / 2) * (Real.exp (Cm * Real.sqrt m + Cm) *
                Real.exp (Cm * Real.sqrt m + Cm)) =
                Real.exp (2 * Cm) * Real.exp ((ca / 2 + 2 * Cm) * Real.sqrt m) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
            calc 5 * Real.sqrt Ka * Real.exp (ca * Real.sqrt m / 2) *
                (Real.exp (Cm * Real.sqrt m + Cm) * (Real.exp (Cm * Real.sqrt m + Cm) * μm)) =
                5 * Real.sqrt Ka * μm * (Real.exp (ca * Real.sqrt m / 2) *
                  (Real.exp (Cm * Real.sqrt m + Cm) * Real.exp (Cm * Real.sqrt m + Cm))) := by ring
              _ = _ := by rw [hE]; ring
        _ ≤ 5 * Real.sqrt Ka * Real.exp (2 * Cm) * Real.exp (c₀ * Real.sqrt m) * μm := by
            gcongr
            simp only [hc₀]; nlinarith
    have h2 : μm * (25 * Kb * Real.exp (cb * Real.sqrt m)) ≤
        25 * Kb * Real.exp (c₀ * Real.sqrt m) * μm := by
      rw [mul_comm]
      gcongr
      simp only [hc₀]; nlinarith
    calc _ ≤ 5 * Real.sqrt Ka * Real.exp (2 * Cm) * Real.exp (c₀ * Real.sqrt m) * μm +
          25 * Kb * Real.exp (c₀ * Real.sqrt m) * μm := add_le_add h1 h2
      _ = B₀ * Real.exp (c₀ * Real.sqrt m) * μm := by simp only [hB₀]; ring
  have hμk0 : 0 ≤ μk := ENNReal.toReal_nonneg
  have hsq := sqrt_le_rpow_two_thirds (k := k) hm1
  have hexp : 20 * B₀ * Real.exp (c₀ * Real.sqrt m) ≤
      Crec * Real.exp (Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) := by
    have hCrec1 : 20 * B₀ ≤ Crec := by simp only [hCrec]; linarith
    have hCc : c₀ * Real.sqrt m ≤ Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by
      have : c₀ ≤ Crec := by simp only [hCrec]; linarith
      calc c₀ * Real.sqrt m ≤ Crec * Real.sqrt m := mul_le_mul_of_nonneg_right this hsqm
        _ ≤ Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
    exact mul_le_mul hCrec1 (Real.exp_le_exp.2 hCc) (Real.exp_pos _).le (by linarith)
  calc (EU (m + k)).toReal ≤ μk * (20 *
      (Real.sqrt A * Real.sqrt B + μm * (25 * Kb * Real.exp (cb * Real.sqrt m)))) := hreal
    _ ≤ μk * (20 * (B₀ * Real.exp (c₀ * Real.sqrt m) * μm)) := by gcongr
    _ = 20 * B₀ * Real.exp (c₀ * Real.sqrt m) * μm * μk := by ring
    _ ≤ Crec * Real.exp (Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μm * μk := by gcongr


end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
