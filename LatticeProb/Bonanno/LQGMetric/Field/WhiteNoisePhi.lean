/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePhi at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DDDF's white-noise field `φ_{a,b}` (task P2-WN; blueprint DDDF.D2.phi)

DDDF (arXiv:1904.08021, `tightness.tex` l. 143, 253, 289): for `0 < a < b`,
`φ_{a,b}(x) := √π ∫_{a²}^{b²} ∫_{ℝ²} p_{t/2}(x − y) W(dy, dt)`, `φ_δ := φ_{δ,1}`.

* `cov_phi`: `E φ_{a,b}(x) φ_{a,b}(x') = ∫_{a²}^{b²} (2t)⁻¹ e^{−|x−x'|²/(2t)} dt` (DDDF l. 287;
  `π p_{t/2} * p_{t/2} = π p_t`).
* `variance_phi_delta`: `Var φ_δ(x) = log δ⁻¹` (DDDF l. 289).
* `phi_add_ae`, `indepFun_phi`: `φ_{a,c} = φ_{a,b} + φ_{b,c}` with `φ_{a,b}`, `φ_{b,c}`
  independent (DDDF l. 220, 283: independence of the white noise at different times).
* `hasLaw_phi_sub`, `variance_phi_sub_le`: Gaussian increments with
  `Var(φ_{a,b}(x) − φ_{a,b}(x')) = ∫_{a²}^{b²} t⁻¹(1 − e^{−|x−x'|²/(2t)}) dt ≤ b²|x−x'|²/(2a⁴)`
  (the bound `1 − e^{−z} ≤ z`; own elementary step, used for the continuous version).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DDDF's field `φ_{a,b}(x) = √π ∫_{a²}^{b²} ∫ p_{t/2}(x − y) W(dy, dt)` (`tightness.tex`
l. 289; junk `0` for `a ≤ 0`, deviation WN-3). -/
def phi (W : WNSpace → Ω → ℝ) (a b : ℝ) (x : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (phiKernelL2 a b x) ω

lemma measurable_phi (hW : IsWhiteNoise P W) (a b : ℝ) (x : ℂ) : Measurable (phi W a b x) :=
  (hW.measurable _).const_mul _

lemma pi_mul_heatKernel (t : ℝ) (x x' : ℂ) :
    Real.pi * heatKernel t x x' = (2 * t)⁻¹ * Real.exp (-‖x - x'‖ ^ 2 / (2 * t)) := by
  unfold heatKernel
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [← mul_assoc]
  congr 1
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

/-- **Covariance of `φ_{a,b}`** (DDDF l. 287). -/
theorem cov_phi (hW : IsWhiteNoise P W) {a : ℝ} (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    cov[phi W a b x, phi W a b x'; P] =
      ∫ t in Icc (a ^ 2) (b ^ 2), (2 * t)⁻¹ * Real.exp (-‖x - x'‖ ^ 2 / (2 * t)) := by
  unfold phi
  rw [covariance_const_mul_left, covariance_const_mul_right, hW.cov_eq,
    inner_phiKernelL2 a b ha, ← mul_assoc, Real.mul_self_sqrt Real.pi_pos.le,
    ← integral_const_mul]
  simp_rw [pi_mul_heatKernel]

/-- **`Var φ_δ(x) = log δ⁻¹`** (DDDF l. 289). -/
theorem variance_phi_delta (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x : ℂ) : Var[phi W δ 1 x; P] = Real.log δ⁻¹ := by
  have := hW.isProbabilityMeasure
  have hm : MemLp (phi W δ 1 x) 2 P := by
    unfold phi
    exact ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  rw [← covariance_self hm.aemeasurable, cov_phi hW hδ]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Real.exp_zero, mul_one]
  have hδ2 : δ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hδ.le hδ1 2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ2]
  simp_rw [mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by positivity) (by norm_num),
    one_pow, one_div, Real.log_inv, Real.log_pow, Real.log_inv]
  push_cast
  ring

/-- The kernels add up: `k_{a,c} = k_{a,b} + k_{b,c}` in `L²` (they differ only on `{t = b²}`). -/
lemma phiKernelL2_add {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (x : ℂ) :
    phiKernelL2 a c x = phiKernelL2 a b x + phiKernelL2 b c x := by
  have hb : 0 < b := ha.trans_le hab
  have hnull : ∀ᵐ p : ℝ × ℂ ∂volume, p.1 ≠ b ^ 2 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have : {p : ℝ × ℂ | p.1 = b ^ 2} = {b ^ 2} ×ˢ univ := by ext p; simp
    rw [this, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
    simp
  refine Lp.ext ?_
  filter_upwards [coeFn_phiKernelL2 a c ha x, coeFn_phiKernelL2 a b ha x,
    coeFn_phiKernelL2 b c hb x, Lp.coeFn_add (phiKernelL2 a b x) (phiKernelL2 b c x), hnull]
    with p h1 h2 h3 h4 h5
  rw [h4, Pi.add_apply, h1, h2, h3]
  have ha2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hb2 : b ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hb.le hbc 2
  unfold phiKernel
  simp only [indicator, mem_prod, mem_Icc, mem_univ, and_true]
  by_cases h1 : p.1 < b ^ 2
  · have : ¬ (b ^ 2 ≤ p.1) := not_le.mpr h1
    by_cases h0 : a ^ 2 ≤ p.1
    · simp [h0, h1.le, this, (h1.le.trans hb2)]
    · simp [h0, this]
  · have h1' : b ^ 2 < p.1 := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h5)
    have : ¬ (p.1 ≤ b ^ 2) := not_le.mpr h1'
    simp [this, ha2.trans h1'.le, h1'.le]

/-- `φ_{a,c} = φ_{a,b} + φ_{b,c}` almost surely (DDDF l. 283). -/
theorem phi_add_ae (hW : IsWhiteNoise P W) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (x : ℂ) :
    phi W a c x =ᵐ[P] fun ω => phi W a b x ω + phi W b c x ω := by
  filter_upwards [hW.add_ae (phiKernelL2 a b x) (phiKernelL2 b c x)] with ω h
  simp only [phi]
  rw [phiKernelL2_add ha hab hbc, h, mul_add]

/-- `k_{a,b,x}` vanishes a.e. off the time strip `[a², b²) × ℂ`. -/
lemma supportedIn_phiKernelL2 {a b : ℝ} (ha : 0 < a) (x : ℂ) :
    SupportedIn (Ico (a ^ 2) (b ^ 2) ×ˢ univ) (phiKernelL2 a b x) := by
  have hnull : ∀ᵐ p : ℝ × ℂ ∂volume, p.1 ≠ b ^ 2 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have : {p : ℝ × ℂ | p.1 = b ^ 2} = {b ^ 2} ×ˢ univ := by ext p; simp
    rw [this, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
    simp
  have h : ∀ᵐ p : ℝ × ℂ ∂volume, p ∈ (Ico (a ^ 2) (b ^ 2) ×ˢ univ)ᶜ →
      (phiKernelL2 a b x : ℝ × ℂ → ℝ) p = 0 := by
    filter_upwards [coeFn_phiKernelL2 a b ha x, hnull] with p h1 h2 hp
    rw [h1]
    unfold phiKernel
    refine indicator_of_notMem (fun hq => hp ?_) _
    simp only [mem_prod, mem_Icc, mem_univ, and_true] at hq
    simp only [mem_prod, mem_Ico, mem_univ, and_true]
    exact ⟨hq.1, lt_of_le_of_ne hq.2 h2⟩
  exact (ae_restrict_iff' ((measurableSet_Ico.prod MeasurableSet.univ).compl)).mpr h

lemma supportedIn_phiKernelL2' {b c : ℝ} (hb : 0 < b) (x : ℂ) :
    SupportedIn (Icc (b ^ 2) (c ^ 2) ×ˢ univ) (phiKernelL2 b c x) := by
  have h : ∀ᵐ p : ℝ × ℂ ∂volume, p ∈ (Icc (b ^ 2) (c ^ 2) ×ˢ univ)ᶜ →
      (phiKernelL2 b c x : ℝ × ℂ → ℝ) p = 0 := by
    filter_upwards [coeFn_phiKernelL2 b c hb x] with p h1 hp
    rw [h1]
    exact indicator_of_notMem hp _
  exact (ae_restrict_iff' ((measurableSet_Icc.prod MeasurableSet.univ).compl)).mpr h

/-- **Independence of scales**: the fields `φ_{a,b}` and `φ_{b,c}` are independent
(DDDF l. 220, 283). -/
theorem indepFun_phi (hW : IsWhiteNoise P W) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IndepFun (fun ω x => phi W a b x ω) (fun ω x => phi W b c x ω) P := by
  have hb : 0 < b := ha.trans_le hab
  have hdisj : Disjoint (Ico (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)) (Icc (b ^ 2) (c ^ 2) ×ˢ univ) := by
    rw [Set.disjoint_prod]
    left
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.1 (not_le.mpr h1.2)
  have hI := hW.indepFun_of_disjoint hdisj
  let Φ₁ : ({f // SupportedIn (Ico (a ^ 2) (b ^ 2) ×ˢ univ) f} → ℝ) → ℂ → ℝ :=
    fun F x => Real.sqrt Real.pi * F ⟨phiKernelL2 a b x, supportedIn_phiKernelL2 ha x⟩
  let Φ₂ : ({g // SupportedIn (Icc (b ^ 2) (c ^ 2) ×ˢ univ) g} → ℝ) → ℂ → ℝ :=
    fun F x => Real.sqrt Real.pi * F ⟨phiKernelL2 b c x, supportedIn_phiKernelL2' hb x⟩
  have hΦ₁ : Measurable Φ₁ :=
    measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  have hΦ₂ : Measurable Φ₂ :=
    measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  exact hI.comp hΦ₁ hΦ₂

end WhiteNoise
end LQGMetric
