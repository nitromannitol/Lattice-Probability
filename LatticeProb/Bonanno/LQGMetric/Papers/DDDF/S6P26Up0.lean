/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Up0 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs

/-!
# DDDF Prop 26, Step 1: `E e^{a 2^{-k} ‖∇φ_{0,k}‖} ≤ K e^{c√k}` (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
Prop 26, Step 1 (l. 1307–1309) uses `E(e^{4ξ 2^{-k} ‖∇φ_{0,k}‖_{[0,1]²}}) ≤ e^{C√k}`, citing
(2.17) (`eq:OscBoundExp`, l. 337). (2.17) as stated carries a factor `n^ε` (`ε > 0`) and gives
only `e^{c n^{1/2+ε}}`, too weak for Lemma 25; the `e^{C√k}` bound is DDDF's own proof of (2.17)
(l. 345–352) run with `a_n = a` (i.e. `ε = 0`): from the tail (2.16) (`prop3_tail`) with
`x_n = aσ² + √(2σ² n log 4)` and `lintegral_exp_le_of_tail`. This file is that proof (same steps
as `prop3_expMoment`, FieldOscExp.lean, with `m = 1`), followed by the transfer to the 25
translated boxes of `T20C.Obig` (motion invariance, as in `T20C.prop3_expMoment_shift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6U

open WhiteNoise SupTail T20C

/-- **(2.17) with `ε = 0`** (DDDF l. 345–352 with `a_n = a`): `E e^{a O_n} ≤ K e^{c√n}`, `n ≥ 1`. -/
theorem osc_expMoment0 {a : ℝ} (ha : 0 < a) : ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (n : ℕ), 1 ≤ n → ∀ (Y : ℂ → Ω → ℝ),
    (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
    (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (((2 : ℝ) ^ n)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖))) ∂P ≤
      ENNReal.ofReal (K * Real.exp (c * √(n : ℝ))) := by
  obtain ⟨C₃, σ2, hC₃, hσ2, h3⟩ := prop3_tail
  set L := Real.log 4 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set d₁ := Real.sqrt (2 * σ2 * L) with hd₁
  have hd₁0 : 0 < d₁ := Real.sqrt_pos.2 (by positivity)
  refine ⟨a * d₁, Real.exp (a ^ 2 * σ2) + a * C₃ * σ2 * Real.exp (a ^ 2 * σ2 / 2) / d₁,
    by positivity, by positivity, ?_⟩
  intro Ω _ P W hW n hn Y hY hYc
  have := hW.isProbabilityMeasure
  set N : ℝ := (n : ℝ) with hN_def
  have hN1 : 1 ≤ N := by rw [hN_def]; exact_mod_cast hn
  set X : Ω → ℝ := fun ω => ((2 : ℝ) ^ n)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖ with hX
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω =>
    mul_nonneg (by positivity) (Real.iSup_nonneg fun _ => norm_nonneg _)
  have hXm : AEMeasurable X P := aemeasurable_osc hW n hY hYc
  set d := Real.sqrt (2 * σ2 * L * N) with hd_def
  have hd0 : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hd2 : d ^ 2 = 2 * σ2 * L * N := Real.sq_sqrt (by positivity)
  have hdd : d = d₁ * Real.sqrt N := by
    rw [hd_def, hd₁, Real.sqrt_mul (by positivity)]
  have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
  set x₀ := a * σ2 + d with hx₀
  set κ := d / σ2 with hκ
  have hκ0 : 0 < κ := by positivity
  set B := a * C₃ * Real.exp (a ^ 2 * σ2 / 2) * Real.exp (κ * x₀) with hB
  have h4 : (4 : ℝ) ^ n = Real.exp (N * L) := by
    rw [hN_def, hL_def, ← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have htail : ∀ t, x₀ < t → a * Real.exp (a * t) * P.real {ω | t ≤ X ω} ≤
      B * Real.exp (-κ * t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.le
    have hP := h3 hW n Y hY hYc t ht0
    have hNL : N * L = d ^ 2 / (2 * σ2) := by rw [hd2]; field_simp
    have key : a * t + N * L + -t ^ 2 / (2 * σ2) ≤ a ^ 2 * σ2 / 2 + κ * x₀ + -κ * t := by
      have iden : (a ^ 2 * σ2 / 2 + κ * x₀ + -κ * t) - (a * t + N * L + -t ^ 2 / (2 * σ2)) =
          (t - a * σ2 - d) ^ 2 / (2 * σ2) := by
        rw [hNL, hκ, hx₀]; field_simp; ring
      have : 0 ≤ (t - a * σ2 - d) ^ 2 / (2 * σ2) := by positivity
      linarith
    calc a * Real.exp (a * t) * P.real {ω | t ≤ X ω}
        ≤ a * Real.exp (a * t) * (C₃ * 4 ^ n * Real.exp (-t ^ 2 / (2 * σ2))) := by gcongr
      _ = a * C₃ * Real.exp (a * t + N * L + -t ^ 2 / (2 * σ2)) := by
          rw [h4, Real.exp_add, Real.exp_add]; ring
      _ ≤ a * C₃ * Real.exp (a ^ 2 * σ2 / 2 + κ * x₀ + -κ * t) := by gcongr
      _ = B * Real.exp (-κ * t) := by rw [hB, Real.exp_add, Real.exp_add]; ring
  have hE := lintegral_exp_le_of_tail hX0 hXm ha (by positivity) hκ0 (by positivity) htail
  refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
  have hBe : B * Real.exp (-κ * x₀) / κ = a * C₃ * σ2 * Real.exp (a ^ 2 * σ2 / 2) / d := by
    rw [hB, hκ, mul_assoc (a * C₃ * Real.exp (a ^ 2 * σ2 / 2)), ← Real.exp_add]
    rw [show d / σ2 * x₀ + -(d / σ2) * x₀ = 0 by ring, Real.exp_zero]
    field_simp
  rw [hBe]
  have hfirst : Real.exp (a * x₀) = Real.exp (a ^ 2 * σ2) * Real.exp (a * d₁ * Real.sqrt N) := by
    rw [← Real.exp_add, hx₀, hdd]; ring_nf
  have hd1 : d₁ ≤ d := by
    have := le_mul_of_one_le_right hd₁0.le hsN
    linarith [hdd]
  have hge1 : 1 ≤ Real.exp (a * d₁ * Real.sqrt N) := Real.one_le_exp (by positivity)
  have hsecond : a * C₃ * σ2 * Real.exp (a ^ 2 * σ2 / 2) / d ≤
      a * C₃ * σ2 * Real.exp (a ^ 2 * σ2 / 2) / d₁ * Real.exp (a * d₁ * Real.sqrt N) := by
    calc a * C₃ * σ2 * Real.exp (a ^ 2 * σ2 / 2) / d
        ≤ a * C₃ * σ2 * Real.exp (a ^ 2 * σ2 / 2) / d₁ := by gcongr
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hge1
  rw [hfirst]
  nlinarith

/-- **The gradient term of Step 1** (DDDF l. 1307–1309): `E e^{a Obig_k} ≤ 25 K e^{c√k}` for
`k ≥ 1`, `Obig` the oscillation of `φ_{0,k}` on the 25 unit boxes of `[-2,3]²`. -/
theorem obig_expMoment {a : ℝ} (ha : 0 < a) : ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Y : ℂ → Ω → ℝ),
    (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
    (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Obig k Y ω)) ∂P ≤
      ENNReal.ofReal (25 * K * Real.exp (c * √(k : ℝ))) := by
  obtain ⟨c, K, hc, hK, h0⟩ := osc_expMoment0 ha
  refine ⟨c, K, hc, hK, fun {Ω} _ {P} {W} hW k hk Y hY hYc => ?_⟩
  set O : ℂ → Ω → ℝ := fun c₁ ω => ((2 : ℝ) ^ k)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖ with hO
  -- each translated box (motion invariance, as in `prop3_expMoment_shift`)
  have hone : ∀ c₁ : ℂ, AEMeasurable (O c₁) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * O c₁ ω)) ∂P ≤
        ENNReal.ofReal (K * Real.exp (c * √(k : ℝ))) := by
    intro c₁
    set W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c₁ f)
    have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
    have hY' : ∀ x, (fun ω => Y (x + c₁) ω) =ᵐ[P] phi W' ((2 : ℝ) ^ k)⁻¹ 1 x := by
      intro x
      have e := phi_motion W (a := ((2 : ℝ) ^ k)⁻¹) (by positivity) 1 1 x c₁
      simp only [Circle.coe_one, one_mul] at e
      rw [← e]; exact hY (x + c₁)
    have hYc' : ∀ ω, ContDiff ℝ 1 fun x => Y (x + c₁) ω := fun ω =>
      (hYc ω).comp (contDiff_id.add contDiff_const)
    exact ⟨aemeasurable_osc hW' k hY' hYc', h0 hW' k hk (fun x => Y (x + c₁)) hY' hYc'⟩
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (a * Obig k Y ω)) ≤
      ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (a * O c₁ ω)) := by
    intro ω
    obtain ⟨c₁, hc₁, he⟩ := Finset.exists_mem_eq_sup' offs_nonempty fun c₁ => O c₁ ω
    have : Obig k Y ω = O c₁ ω := he
    rw [this]
    exact Finset.single_le_sum (f := fun c₁ => ENNReal.ofReal (Real.exp (a * O c₁ ω)))
      (fun _ _ => by positivity) hc₁
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Obig k Y ω)) ∂P
      ≤ ∫⁻ ω, ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (a * O c₁ ω)) ∂P := lintegral_mono hpt
    _ = ∑ c₁ ∈ offs, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * O c₁ ω)) ∂P := by
        refine lintegral_finsetSum' _ fun c₁ _ => ?_
        exact (Real.measurable_exp.comp_aemeasurable
          ((hone c₁).1.const_mul a)).ennreal_ofReal
    _ ≤ ∑ _c₁ ∈ offs, ENNReal.ofReal (K * Real.exp (c * √(k : ℝ))) :=
        Finset.sum_le_sum fun c₁ _ => (hone c₁).2
    _ ≤ ENNReal.ofReal (25 * K * Real.exp (c * √(k : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h25 : (offs.card : ℝ) ≤ 25 := by exact_mod_cast card_offs_le
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right h25 (by positivity)

end S6U
end DDDF
end LQGMetric
