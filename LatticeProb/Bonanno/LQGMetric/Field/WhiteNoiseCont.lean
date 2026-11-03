/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseCont at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN

/-!
# Increments and a continuous version of `φ_{a,b}` (task P2-WN; blueprint DDDF.D2.phi (iv))

* `hasLaw_phi_sub`, `variance_phi_sub`: `φ_{a,b}(x) − φ_{a,b}(x')` is a centred Gaussian with
  variance `∫_{a²}^{b²} t⁻¹(1 − e^{−|x−x'|²/(2t)}) dt` (from `cov_phi`, DDDF l. 287).
* `variance_phi_sub_le`: this is `≤ (b² − a²)|x − x'|²/(2a⁴)` (`1 − e^{−z} ≤ z`; own elementary
  step).
* `exists_continuous_modification_phi`: for `0 < a ≤ b`, `x ↦ φ_{a,b}(x)` has a modification
  that is continuous for every `ω` (DDDF l. 292 "a.s. smooth version", here only `C⁰`; `C¹` is
  WP-21). Proof: Gaussian 4th moments (QZ `KolmG.lintegral_pow_two_mul_of_map_eq`) and the
  Kolmogorov–Čentsov theorem on `Fin 2 → ℝ` (QZ `KolmN.exists_continuous_modification_N`;
  Revuz–Yor Ch. I Thm (2.1)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma integrableOn_pi_heatKernel {a : ℝ} (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    IntegrableOn (fun t => heatKernel t x x') (Icc (a ^ 2) (b ^ 2)) :=
  (continuousOn_heatKernel_time a ha b x x').integrableOn_compact isCompact_Icc

/-- `‖√π k_x − √π k_{x'}‖² = ∫_{a²}^{b²} t⁻¹(1 − e^{−|x−x'|²/(2t)}) dt`. -/
lemma sq_norm_phiKernelL2_sub {a : ℝ} (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    ‖Real.sqrt Real.pi • phiKernelL2 a b x + (-Real.sqrt Real.pi) • phiKernelL2 a b x'‖ ^ 2 =
      ∫ t in Icc (a ^ 2) (b ^ 2), t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t))) := by
  rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt Real.pi_pos.le, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_phiKernelL2 a b ha, inner_phiKernelL2 a b ha,
    inner_phiKernelL2 a b ha]
  have h1 := integrableOn_pi_heatKernel ha b x x
  have h2 := integrableOn_pi_heatKernel ha b x x'
  have h3 := integrableOn_pi_heatKernel ha b x' x'
  have e : ∀ t : ℝ, t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t))) =
      Real.pi * heatKernel t x x - 2 * (Real.pi * heatKernel t x x') +
        Real.pi * heatKernel t x' x' := by
    intro t
    rw [pi_mul_heatKernel, pi_mul_heatKernel, pi_mul_heatKernel]
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      neg_zero, zero_div, Real.exp_zero, mul_one, mul_inv]
    ring
  simp_rw [e]
  rw [integral_add ?_ ?_, integral_sub ?_ ?_, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  · ring
  · exact h1.const_mul _
  · exact (h2.const_mul _).const_mul _
  · exact (h1.const_mul _).sub ((h2.const_mul _).const_mul _)
  · exact h3.const_mul _

/-- The increments of `φ_{a,b}` are centred Gaussians. -/
theorem hasLaw_phi_sub (hW : IsWhiteNoise P W) {a : ℝ} (ha : 0 < a) (b : ℝ) (x x' : ℂ) :
    HasLaw (fun ω => phi W a b x ω - phi W a b x' ω)
      (gaussianReal 0 (∫ t in Icc (a ^ 2) (b ^ 2),
        t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t)))).toNNReal) P := by
  have h := hW.hasLaw ![phiKernelL2 a b x, phiKernelL2 a b x']
    ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [sq_norm_phiKernelL2_sub ha] at h
  refine (h.congr ?_)
  exact Eventually.of_forall fun ω => by simp only [phi]; ring

/-- `Var(φ_{a,b}(x) − φ_{a,b}(x')) ≤ (b² − a²)|x − x'|²/(2a⁴)` (via `1 − e^{−z} ≤ z`). -/
theorem incrVar_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x x' : ℂ) :
    ∫ t in Icc (a ^ 2) (b ^ 2), t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t))) ≤
      (‖x - x'‖ ^ 2 / (2 * a ^ 4)) * (b ^ 2 - a ^ 2) := by
  have ha2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (a ^ 2) (b ^ 2))
    (f := fun t => t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t))))
    (C := ‖x - x'‖ ^ 2 / (2 * a ^ 4)) (by simp [Real.volume_Icc]) (fun t ht => by
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
      have hz : 0 ≤ ‖x - x'‖ ^ 2 / (2 * t) := by positivity
      have he1 : Real.exp (-‖x - x'‖ ^ 2 / (2 * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_div]; linarith
      have he2 := Real.add_one_le_exp (-‖x - x'‖ ^ 2 / (2 * t))
      have hnn : 0 ≤ t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t))) :=
        mul_nonneg (inv_nonneg.mpr ht0.le) (by linarith)
      rw [Real.norm_of_nonneg hnn]
      calc t⁻¹ * (1 - Real.exp (-‖x - x'‖ ^ 2 / (2 * t)))
          ≤ t⁻¹ * (‖x - x'‖ ^ 2 / (2 * t)) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht0.le)
            have := neg_div (2 * t) (‖x - x'‖ ^ 2); linarith
        _ = ‖x - x'‖ ^ 2 / (2 * t ^ 2) := by field_simp
        _ ≤ ‖x - x'‖ ^ 2 / (2 * a ^ 4) := by
            have : a ^ 4 ≤ t ^ 2 := by
              have := pow_le_pow_left₀ (by positivity) ht.1 2
              calc a ^ 4 = (a ^ 2) ^ 2 := by ring
                _ ≤ t ^ 2 := this
            gcongr)
  rw [Real.volume_real_Icc_of_le ha2] at hb
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)

/-! ### Kolmogorov–Čentsov on `ℂ ≅ Fin 2 → ℝ` -/

/-- `q ↦ q 0 + q 1 i`. -/
def finTwoToC (q : Fin 2 → ℝ) : ℂ := ⟨q 0, q 1⟩

lemma norm_finTwoToC_sub_le (q q' : Fin 2 → ℝ) : ‖finTwoToC q - finTwoToC q'‖ ≤ 2 * ‖q - q'‖ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h0 : |(finTwoToC q - finTwoToC q').re| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 0
    simpa [finTwoToC, Real.norm_eq_abs] using this
  have h1 : |(finTwoToC q - finTwoToC q').im| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 1
    simpa [finTwoToC, Real.norm_eq_abs] using this
  linarith

/-- **Continuous version of `φ_{a,b}`** (DDDF l. 292, `C⁰` part): for `0 < a ≤ b` there is a
modification of `x ↦ φ_{a,b}(x)` that is continuous for every `ω`. -/
theorem exists_continuous_modification_phi (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W a b x := by
  set C : ℝ := (b ^ 2 - a ^ 2) / (2 * a ^ 4) with hC
  have hC0 : 0 ≤ C := by
    have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
    rw [hC]; apply div_nonneg <;> nlinarith [sq_nonneg a]
  set Z : (Fin 2 → ℝ) → Ω → ℝ := fun q => phi W a b (finTwoToC q) with hZ
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG Z P 4 4 K R := by
    intro R
    refine ⟨C ^ 2 * QuantumZipper.gaussianAbsMoment 4 * 16, by
      have := QuantumZipper.gaussianAbsMoment_nonneg 4; positivity, fun q _ q' _ => ?_⟩
    have hlaw := hasLaw_phi_sub hW ha b (finTwoToC q) (finTwoToC q')
    have e := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((measurable_phi hW a b _).sub (measurable_phi hW a b _)) 2 hlaw.map_eq
    simp only [Pi.sub_apply] at e
    simp only [hZ]
    rw [show (4 : ℕ) = 2 * 2 from rfl, e]
    refine ENNReal.ofReal_le_ofReal ?_
    set v := ∫ t in Icc (a ^ 2) (b ^ 2),
      t⁻¹ * (1 - Real.exp (-‖finTwoToC q - finTwoToC q'‖ ^ 2 / (2 * t)))
    have hv : v ≤ C * ‖finTwoToC q - finTwoToC q'‖ ^ 2 := by
      have := incrVar_le ha hab (finTwoToC q) (finTwoToC q')
      calc v ≤ _ := this
        _ = C * ‖finTwoToC q - finTwoToC q'‖ ^ 2 := by rw [hC]; ring
    have hM := QuantumZipper.gaussianAbsMoment_nonneg 4
    have hn := norm_finTwoToC_sub_le q q'
    have hv' : ((v.toNNReal : NNReal) : ℝ) ≤ C * (2 * ‖q - q'‖) ^ 2 := by
      rw [Real.coe_toNNReal']
      refine max_le (hv.trans ?_) (by positivity)
      gcongr
    have hv0 : 0 ≤ ((v.toNNReal : NNReal) : ℝ) := NNReal.coe_nonneg _
    calc ((v.toNNReal : NNReal) : ℝ) ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2)
        ≤ (C * (2 * ‖q - q'‖) ^ 2) ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2) := by
          gcongr
      _ = C ^ 2 * QuantumZipper.gaussianAbsMoment (2 * 2) * 16 * ‖q - q'‖ ^ (4 : ℝ) := by
          rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  obtain ⟨Y₀, hYc₀, hYm₀, hYt⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (d := 2) (P := P) (Z := Z) (fun q => (measurable_phi hW a b _).aemeasurable)
    (p := 4) (by norm_num) (a := 4) (by norm_num) hmom
  -- a measurable full-measure set on which the dyadic values converge to `Y₀`
  set B : Set Ω := {ω | ¬ ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
    (nhds (Y₀ q ω))} with hB
  set G : Set Ω := (toMeasurable P B)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [hG, mem_compl_iff, not_not, Set.ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.mp hYt
  have hGt : ∀ ω ∈ G, ∀ q, Tendsto (fun n => Z (QuantumZipper.KolmD.rndD n q) ω) atTop
      (nhds (Y₀ q ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  set Y : (Fin 2 → ℝ) → Ω → ℝ := fun q ω => G.indicator (fun ω => Y₀ q ω) ω with hY
  have hYc : ∀ ω, Continuous fun q => Y q ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hYc₀ ω
    · simp only [hY, indicator_of_notMem hω]; exact continuous_const
  have hYmeas : ∀ q, Measurable (Y q) := by
    intro q
    refine measurable_of_tendsto_metrizable
      (f := fun n => G.indicator (Z (QuantumZipper.KolmD.rndD n q)))
      (fun n => (measurable_phi hW a b _).indicator hGm) (tendsto_pi_nhds.mpr fun ω => ?_)
    by_cases hω : ω ∈ G
    · simp only [hY, indicator_of_mem hω]; exact hGt ω hω q
    · simp only [hY, indicator_of_notMem hω]; exact tendsto_const_nhds
  have hYm : ∀ q, (fun ω => Y q ω) =ᵐ[P] Z q := by
    intro q
    filter_upwards [hGae, hYm₀ q] with ω h1 h2
    simp only [hY, indicator_of_mem h1]
    exact h2
  let fromC : ℂ → Fin 2 → ℝ := fun z => ![z.re, z.im]
  have hfc : Continuous fromC := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re
    · exact Complex.continuous_im
  have hft : ∀ z, finTwoToC (fromC z) = z := fun z => by
    apply Complex.ext <;> simp [finTwoToC, fromC]
  refine ⟨fun x ω => Y (fromC x) ω, fun ω => (hYc ω).comp hfc, fun x => hYmeas _, fun x => ?_⟩
  have := hYm (fromC x)
  simp only [hZ, hft] at this
  exact this

end WhiteNoise
end LQGMetric
