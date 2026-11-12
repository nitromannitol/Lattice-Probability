/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20CMom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOscExp
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Rigid
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BXMom

/-!
# DDDF Theorem 20, Step 4: moments of the field quantities on translated boxes (task P2-DDDFT20c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1158–1163 ((5.68) = `eq:EffectE0`) and the moments
of `e^{8ξX}` (l. 1152). Step 4 needs the oscillation of `φ_{0,K}` and the comparison variable
`X` on a neighbourhood of `[0,1]²` (blocks of `𝒫_K` meeting `[0,1]²` and their circuits stick
out of the square; DDDF use `‖∇φ_{0,K}‖_{[0,1]²}`). Both are moved to the reference box by the
motion invariance of white noise (`isWhiteNoise_isometry`, `phi_motion`; DDDF l. 293:
the fields are stationary).

* `T20C.prop3_expMoment_lintegral`: DDDF Prop 3, (2.17) as a lower Lebesgue integral (same proof
  as `prop3_expMoment` in `FieldOscExp.lean`, which only records the Bochner integral).
* `T20C.prop3_expMoment_shift`: the same for the box `c + [0,1]²`.
* `T20C.ae_forall_eq_of_cont`: two continuous modifications are indistinguishable.
* `T20C.expMoment_XAB_shift`: `E e^{l X}` for `X = X_{a,b}` on the box `c + [0,a]×[0,b]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

namespace T20C

theorem prop3_expMoment_lintegral {ε : ℝ} (hε : 0 < ε) {a : ℝ} (ha : 0 < a) : ∃ c K : ℝ,
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (n : ℕ) (Y : ℂ → Ω → ℝ), (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
    (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (n : ℝ) ^ ε * (((2 : ℝ) ^ n)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖))) ∂P ≤
      ENNReal.ofReal (Real.exp (c * (n : ℝ) ^ (1 / 2 + ε) + K * (n : ℝ) ^ (2 * ε))) := by
  obtain ⟨C₃, σ2, hC₃, hσ2, h3⟩ := prop3_tail
  set L := Real.log 4 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set d₁ := Real.sqrt (2 * σ2 * L) with hd₁
  have hd₁0 : 0 < d₁ := Real.sqrt_pos.2 (by positivity)
  set C' := C₃ * σ2 / d₁ with hC'
  have hC'0 : 0 ≤ C' := by positivity
  refine ⟨a * d₁ + a, a ^ 2 * σ2 + Real.log (1 + C'), ?_⟩
  intro Ω _ P W hW n Y hY hYc
  have := hW.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ((0 : ℕ) : ℝ) ^ ε = 0 := by rw [Nat.cast_zero]; exact Real.zero_rpow hε.ne'
    have h1 : ((0 : ℕ) : ℝ) ^ (1 / 2 + ε) = 0 := by
      rw [Nat.cast_zero]; exact Real.zero_rpow (by positivity)
    have h2 : ((0 : ℕ) : ℝ) ^ (2 * ε) = 0 := by
      rw [Nat.cast_zero]; exact Real.zero_rpow (by positivity)
    simp only [h0, h1, h2, mul_zero, zero_mul, Real.exp_zero, add_zero, ENNReal.ofReal_one,
      lintegral_const, measure_univ, mul_one, le_refl]
  set N : ℝ := (n : ℝ) with hN_def
  have hN1 : 1 ≤ N := by rw [hN_def]; exact_mod_cast hn
  set m := N ^ ε with hm_def
  have hm1 : 1 ≤ m := Real.one_le_rpow hN1 hε.le
  set X : Ω → ℝ := fun ω => ((2 : ℝ) ^ n)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y x ω) z‖ with hX
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω =>
    mul_nonneg (by positivity) (Real.iSup_nonneg fun _ => norm_nonneg _)
  have hXm : AEMeasurable X P := aemeasurable_osc hW n hY hYc
  set l := a * m with hl_def
  have hl : 0 < l := by positivity
  set d := Real.sqrt (2 * σ2 * L * N) with hd_def
  have hd0 : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hd2 : d ^ 2 = 2 * σ2 * L * N := Real.sq_sqrt (by positivity)
  have hdd : d = d₁ * Real.sqrt N := by
    rw [hd_def, hd₁, Real.sqrt_mul (by positivity)]
  have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
  set x₀ := l * σ2 + d with hx₀
  set κ := d / σ2 with hκ
  have hκ0 : 0 < κ := by positivity
  set B := l * C₃ * Real.exp (l ^ 2 * σ2 / 2) * Real.exp (κ * x₀) with hB
  have h4 : (4 : ℝ) ^ n = Real.exp (N * L) := by
    rw [hN_def, hL_def, ← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have htail : ∀ t, x₀ < t → l * Real.exp (l * t) * P.real {ω | t ≤ X ω} ≤
      B * Real.exp (-κ * t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.le
    have hP := h3 hW n Y hY hYc t ht0
    have hNL : N * L = d ^ 2 / (2 * σ2) := by rw [hd2]; field_simp
    have key : l * t + N * L + -t ^ 2 / (2 * σ2) ≤ l ^ 2 * σ2 / 2 + κ * x₀ + -κ * t := by
      have iden : (l ^ 2 * σ2 / 2 + κ * x₀ + -κ * t) - (l * t + N * L + -t ^ 2 / (2 * σ2)) =
          (t - l * σ2 - d) ^ 2 / (2 * σ2) := by
        rw [hNL, hκ, hx₀]; field_simp; ring
      have : 0 ≤ (t - l * σ2 - d) ^ 2 / (2 * σ2) := by positivity
      linarith
    calc l * Real.exp (l * t) * P.real {ω | t ≤ X ω}
        ≤ l * Real.exp (l * t) * (C₃ * 4 ^ n * Real.exp (-t ^ 2 / (2 * σ2))) := by gcongr
      _ = l * C₃ * Real.exp (l * t + N * L + -t ^ 2 / (2 * σ2)) := by
          rw [h4, Real.exp_add, Real.exp_add]; ring
      _ ≤ l * C₃ * Real.exp (l ^ 2 * σ2 / 2 + κ * x₀ + -κ * t) := by gcongr
      _ = B * Real.exp (-κ * t) := by rw [hB, Real.exp_add, Real.exp_add]; ring
  have hE := lintegral_exp_le_of_tail hX0 hXm hl (by positivity) hκ0 (by positivity) htail
  refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the elementary final estimate
  have hrp1 : N ^ (1 / 2 + ε) = Real.sqrt N * m := by
    rw [Real.rpow_add (by linarith), Real.sqrt_eq_rpow]
  have hrp2 : N ^ (2 * ε) = m ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by linarith), hm_def, Real.rpow_two]
  rw [hrp1, hrp2]
  set Z := (a * d₁ + a) * (Real.sqrt N * m) + a ^ 2 * σ2 * m ^ 2 with hZ
  have hBe : B * Real.exp (-κ * x₀) / κ = l * C₃ * σ2 * Real.exp (l ^ 2 * σ2 / 2) / d := by
    rw [hB, hκ, mul_assoc (l * C₃ * Real.exp (l ^ 2 * σ2 / 2)), ← Real.exp_add]
    rw [show d / σ2 * x₀ + -(d / σ2) * x₀ = 0 by ring, Real.exp_zero]
    field_simp
  rw [hBe]
  have hsm : 0 ≤ Real.sqrt N * m := by positivity
  have hasm : 0 ≤ a * (Real.sqrt N * m) := mul_nonneg ha.le hsm
  have hfirst : Real.exp (l * x₀) ≤ Real.exp Z := by
    rw [Real.exp_le_exp]
    have key : Z - l * x₀ = a * (Real.sqrt N * m) := by
      rw [hZ, hx₀, hdd, hl_def]; ring
    linarith
  have hsecond : l * C₃ * σ2 * Real.exp (l ^ 2 * σ2 / 2) / d ≤ C' * Real.exp Z := by
    have hlexp : l ≤ Real.exp (a * (Real.sqrt N * m)) := by
      refine le_trans ?_ (Real.add_one_le_exp _)
      have h1 := mul_le_mul_of_nonneg_left hsN (by positivity : (0 : ℝ) ≤ a * m)
      have e1 : a * (Real.sqrt N * m) = a * m * Real.sqrt N := by ring
      rw [e1, hl_def]; linarith
    have hd1 : d₁ ≤ d := by
      have := le_mul_of_one_le_right hd₁0.le hsN
      linarith [hdd]
    have hZ' : a * (Real.sqrt N * m) + l ^ 2 * σ2 / 2 ≤ Z := by
      have key : Z - (a * (Real.sqrt N * m) + l ^ 2 * σ2 / 2) =
          a * d₁ * (Real.sqrt N * m) + a ^ 2 * σ2 * m ^ 2 / 2 := by
        rw [hZ, hl_def]; ring
      have : 0 ≤ a * d₁ * (Real.sqrt N * m) + a ^ 2 * σ2 * m ^ 2 / 2 := by positivity
      linarith
    calc l * C₃ * σ2 * Real.exp (l ^ 2 * σ2 / 2) / d
        ≤ Real.exp (a * (Real.sqrt N * m)) * C₃ * σ2 * Real.exp (l ^ 2 * σ2 / 2) / d₁ := by
          gcongr
      _ = C' * Real.exp (a * (Real.sqrt N * m) + l ^ 2 * σ2 / 2) := by
          rw [hC', Real.exp_add]; ring
      _ ≤ C' * Real.exp Z := by gcongr
  have hlog : 0 ≤ Real.log (1 + C') := Real.log_nonneg (by linarith)
  calc Real.exp (l * x₀) + l * C₃ * σ2 * Real.exp (l ^ 2 * σ2 / 2) / d
      ≤ (1 + C') * Real.exp Z := by linarith
    _ = Real.exp (Real.log (1 + C') + Z) := by
        rw [Real.exp_add (Real.log (1 + C')) Z, Real.exp_log (by linarith)]
    _ ≤ Real.exp ((a * d₁ + a) * (Real.sqrt N * m) + (a ^ 2 * σ2 + Real.log (1 + C')) * m ^ 2) := by
        rw [Real.exp_le_exp, hZ]
        have : Real.log (1 + C') ≤ Real.log (1 + C') * m ^ 2 :=
          le_mul_of_one_le_right hlog (one_le_pow₀ hm1)
        have key : (a * d₁ + a) * (Real.sqrt N * m) + (a ^ 2 * σ2 + Real.log (1 + C')) * m ^ 2 -
            (Real.log (1 + C') + ((a * d₁ + a) * (Real.sqrt N * m) + a ^ 2 * σ2 * m ^ 2)) =
            Real.log (1 + C') * m ^ 2 - Real.log (1 + C') := by ring
        linarith
/-- DDDF Prop 3, (2.17), on the translated box `c₁ + [0,1]²` (motion invariance). -/
theorem prop3_expMoment_shift {ε : ℝ} (hε : 0 < ε) {a : ℝ} (ha : 0 < a) : ∃ c K : ℝ,
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (n : ℕ) (Y : ℂ → Ω → ℝ), (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
    (∀ ω, ContDiff ℝ 1 fun x => Y x ω) → ∀ c₁ : ℂ,
    AEMeasurable (fun ω => ((2 : ℝ) ^ n)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖) P ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (n : ℝ) ^ ε * (((2 : ℝ) ^ n)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖))) ∂P ≤
      ENNReal.ofReal (Real.exp (c * (n : ℝ) ^ (1 / 2 + ε) + K * (n : ℝ) ^ (2 * ε))) := by
  obtain ⟨c, K, h⟩ := prop3_expMoment_lintegral hε ha
  refine ⟨c, K, fun {Ω} _ {P} {W} hW n Y hY hYc c₁ => ?_⟩
  set W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c₁ f)
  have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
  have hY' : ∀ x, (fun ω => Y (x + c₁) ω) =ᵐ[P] phi W' ((2 : ℝ) ^ n)⁻¹ 1 x := by
    intro x
    have e := phi_motion W (a := ((2 : ℝ) ^ n)⁻¹) (by positivity) 1 1 x c₁
    simp only [Circle.coe_one, one_mul] at e
    rw [← e]; exact hY (x + c₁)
  have hYc' : ∀ ω, ContDiff ℝ 1 fun x => Y (x + c₁) ω := fun ω =>
    (hYc ω).comp (contDiff_id.add contDiff_const)
  exact ⟨aemeasurable_osc hW' n hY' hYc', h hW' n (fun x => Y (x + c₁)) hY' hYc'⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- two modifications with continuous paths are indistinguishable -/
lemma ae_forall_eq_of_cont {Y₁ Y₂ : ℂ → Ω → ℝ} (h1 : ∀ ω, Continuous fun x => Y₁ x ω)
    (h2 : ∀ ω, Continuous fun x => Y₂ x ω)
    (h : ∀ x, (fun ω => Y₁ x ω) =ᵐ[P] fun ω => Y₂ x ω) : ∀ᵐ ω ∂P, ∀ x, Y₁ x ω = Y₂ x ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ d : D, Y₁ d ω = Y₂ d ω := ae_all_iff.2 fun d => h d
  filter_upwards [hD] with ω hω x
  have e := Continuous.ext_on hDd (h1 ω) (h2 ω) fun y hy => hω ⟨y, hy⟩
  exact congrFun e x

/-- exponential moments of `X_{a,b}` on the translated box `c₁ + [0,a]×[0,b]` -/
theorem expMoment_XAB_shift {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams)
    (c₁ : ℂ) (a b : ℝ) {l : ℝ} (hl : 0 < l) :
    AEMeasurable (fun ω => (XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
      (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b).toReal) P ∧
    ∃ M : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
      (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b).toReal)) ∂P ≤ ENNReal.ofReal M := by
  set W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c₁ f)
  have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
  have hφ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y, phiMN W P 0 n (y + c₁) ω = phiMN W' P 0 n y ω := by
    refine ae_all_iff.2 fun n => ?_
    have h1 := isPhiVersion_phiMN hW (Nat.zero_le n)
    have h2 := isPhiVersion_phiMN hW' (Nat.zero_le n)
    refine ae_forall_eq_of_cont (fun ω => (h1.cont ω).comp (continuous_id.add continuous_const))
      h2.cont fun x => ?_
    have e := phi_motion W (a := (2 : ℝ)⁻¹ ^ n) (by positivity) ((2 : ℝ)⁻¹ ^ 0) 1 x c₁
    simp only [Circle.coe_one, one_mul] at e
    exact (h1.ae_eq (x + c₁)).trans (by rw [e]; exact (h2.ae_eq x).symm)
  have hψ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y, psiMN Q W P 0 n (y + c₁) ω = psiMN Q W' P 0 n y ω := by
    refine ae_all_iff.2 fun n => ?_
    have h1 := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    have h2 := isPsiVersion_psiMN (Q := Q) hW' (Nat.zero_le n)
    refine ae_forall_eq_of_cont (fun ω => (h1.cont ω).comp (continuous_id.add continuous_const))
      h2.cont fun x => ?_
    have e : psi Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (x + c₁) =
        psi Q W' ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) x := by
      have e1 := psiKernelL2_motion Q (a := (2 : ℝ)⁻¹ ^ n) (by positivity) ((2 : ℝ)⁻¹ ^ 0) 1 x c₁
      simp only [Circle.coe_one, one_mul] at e1
      funext ω; simp only [psi, e1, W']
    exact (h1.ae_eq (x + c₁)).trans (by rw [e]; exact (h2.ae_eq x).symm)
  have hX : (fun ω => (XAB (fun n y => phiMN W P 0 n (y + c₁) ω)
      (fun n y => psiMN Q W P 0 n (y + c₁) ω) a b).toReal) =ᵐ[P]
      fun ω => (XAB (fun n y => phiMN W' P 0 n y ω) (fun n y => psiMN Q W' P 0 n y ω) a b).toReal := by
    filter_upwards [hφ, hψ] with ω h1 h2
    simp only [h1, h2]
  refine ⟨(T20B.measurable_XAB hW' Q a b).ennreal_toReal.aemeasurable.congr hX.symm, ?_⟩
  obtain ⟨M, hM⟩ := dddf_expMoment_XAB hW' Q a b hl
  refine ⟨M, le_of_eq_of_le (lintegral_congr_ae ?_) hM⟩
  filter_upwards [hX] with ω h
  rw [h]

end T20C

end DDDF
end LQGMetric
