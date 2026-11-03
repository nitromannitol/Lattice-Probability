/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistSFub2 at commit 31e7483; only the module paths of local imports are changed.
   v4.35 port: use MemLp.aestronglyMeasurable in place of a conjunction projection.
   v4.35 port: replace deprecated push_neg with push Not.
   v4.35 port: silence unused-section-variable linter. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub

/-!
# Stochastic Fubini: `∫ F ∂_re ∂_im φ = W(kerFun φ)` almost surely (task P2-EXIST)

For a white noise `W` and a version `Y` of `F(x) = W(rectL2 x)` continuous in `x`:
`ae_integral_d12_mul_eq`: `∫ ∂_re∂_im φ(x) Y(x) dx = W(testL2 φ)` a.s., for every `φ ∈ 𝓓(ℂ)`.
Proof: the `L²(P)` distance is `E A² − 2 E AB + E B² = 0`, each term computed by Fubini on
`Ω × ℂ` and `integral_d12_mul_inner_rectL2`. Own elementary proof (standard stochastic Fubini).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace LQGMetric
namespace GFFExist

open WhiteNoise

lemma memLp_kerFun_test (φ : TestC) : MemLp (kerFun φ) 2 (volume : Measure (ℝ × ℂ)) := by
  obtain ⟨M, R, _, h⟩ := testC_bddSupp φ
  exact h.memLp_kerFun.1

/-- the `L²` class of `kerFun φ` for a test function -/
def testL2 (φ : TestC) : WNSpace := (memLp_kerFun_test φ).toLp _

lemma inner_testL2_eq (φ : TestC) (G : WNSpace) :
    ⟪testL2 φ, G⟫ = ∫ q, kerFun φ q * G q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_kerFun_test φ).coeFn_toLp] with q h1
  rw [testL2, h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

lemma integral_d12_mul_inner_rectL2' (φ : TestC) (G : WNSpace) :
    ∫ x, d12 φ x * ⟪rectL2 x, G⟫ = ⟪testL2 φ, G⟫ := by
  rw [integral_d12_mul_inner_rectL2, inner_testL2_eq]

lemma sq_norm_rectL2 (x : ℂ) : ‖rectL2 x‖ ^ 2 = ∫ q, kerFun (rectInd x) q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_rectL2_eq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_rectL2 x] with q h
  rw [h, sq]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma wn_integral_mul (hW : IsWhiteNoise P W) (f g : WNSpace) :
    ∫ ω, W f ω * W g ω ∂P = ⟪f, g⟫ := by
  have := hW.isProbabilityMeasure
  have hf := (hW.hasLaw_single f).hasGaussianLaw.memLp_two
  have hg := (hW.hasLaw_single g).hasGaussianLaw.memLp_two
  have h := covariance_eq_sub hf hg
  rw [hW.cov_eq, QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single f),
    zero_mul, sub_zero] at h
  rw [h]; rfl

lemma wn_memLp (hW : IsWhiteNoise P W) (f : WNSpace) : MemLp (W f) 2 P := by
  have := hW.isProbabilityMeasure
  exact (hW.hasLaw_single f).hasGaussianLaw.memLp_two

lemma integrable_d12_mul_slice (φ : TestC) (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable fun x => d12 φ x * f x :=
  ((d12 φ).continuous.mul hf).integrable_of_hasCompactSupport
    (d12 φ).hasCompactSupport.mul_right

section SFub

variable (hW : IsWhiteNoise P W) {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x)) (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (rectL2 x))
include hW hYc hYm hYW

lemma memLp_Y (x : ℂ) : MemLp (Y x) 2 P := (wn_memLp hW _).ae_eq (hYW x).symm

lemma integral_Y_mul (x : ℂ) {Z : Ω → ℝ} : ∫ ω, Y x ω * Z ω ∂P = ∫ ω, W (rectL2 x) ω * Z ω ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h]

lemma measurable_Y₂ : Measurable fun p : Ω × ℂ => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

omit hYc hYm in
lemma integral_sq_Y (x : ℂ) : ∫ ω, Y x ω ^ 2 ∂P = ‖rectL2 x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h, sq]

/-- the swap `E[(∫ ψ Y) Z] = ∫ ψ E[Y Z]` for `Z ∈ L²(P)` -/
lemma integral_A_mul (φ : TestC) {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, d12 φ x * Y x ω) * Z ω ∂P = ∫ x, d12 φ x * ∫ ω, Y x ω * Z ω ∂P := by
  have := hW.isProbabilityMeasure
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  set Ck := (2 * Real.pi + 32 * L ^ 4) * (4 * L * L)
  set H : Ω × ℂ → ℝ := fun p => d12 φ p.2 * Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod volume) :=
    ((((d12 φ).continuous.measurable.comp measurable_snd).mul
      (measurable_Y₂ hW hYc hYm hYW)).aestronglyMeasurable).mul hZ.aestronglyMeasurable.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x
    have h1 := (memLp_Y hW hYc hYm hYW x).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((memLp_Y hW hYc hYm hYW x).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = _ := by rw [integral_div, integral_add h1 hZ2]
  have hY2 : ∀ x, ‖x‖ ≤ L → ∫ ω, Y x ω ^ 2 ∂P ≤ Ck := by
    intro x hx
    rw [integral_sq_Y hW hYW x, sq_norm_rectL2]
    exact integral_sq_kerFun_rect_le hx
  have hHi : Integrable H (P.prod volume) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hH, mul_assoc]
      exact ((memLp_Y hW hYc hYm hYW x).integrable_mul hZ).const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (d12 φ)).norm.mul_const
        ((Ck + ∫ ω, Z ω ^ 2 ∂P) / 2)) hHm.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖H (ω, x)‖ ∂P = ‖d12 φ x‖ * ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P := by
        simp only [hH, norm_mul]; rw [← integral_const_mul]; congr 1; funext ω; ring
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      by_cases hx : L < ‖x‖
      · rw [hL x hx]; simp
      · push Not at hx
        refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (norm_nonneg _)
        gcongr
        exact hY2 x hx
  have e1 : ∀ ω, (∫ x, d12 φ x * Y x ω) * Z ω = ∫ x, H (ω, x) := fun ω => by
    rw [← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun ω x => H (ω, x)) hHi]
  congr 1; funext x
  simp only [hH]
  rw [← integral_const_mul]
  congr 1; funext ω; ring

lemma memLp_A (φ : TestC) : MemLp (fun ω => ∫ x, d12 φ x * Y x ω) 2 P := by
  have := hW.isProbabilityMeasure
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  set Ck := (2 * Real.pi + 32 * L ^ 4) * (4 * L * L)
  have hjm := measurable_Y₂ hW hYc hYm hYW
  have hAm : Measurable fun ω => ∫ x, d12 φ x * Y x ω :=
    ((((d12 φ).continuous.measurable.comp measurable_snd).mul hjm).stronglyMeasurable.integral_prod_right'
      (ν := volume)).measurable
  set Q : Ω × ℂ → ℝ := fun p => |d12 φ p.2| * Y p.2 p.1 ^ 2 with hQ
  have hQm : Measurable Q := (continuous_abs.measurable.comp
    ((d12 φ).continuous.measurable.comp measurable_snd)).mul (hjm.pow_const 2)
  have hQi : Integrable Q (P.prod volume) := by
    rw [integrable_prod_iff' hQm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hQ]
      exact (memLp_Y hW hYc hYm hYW x).integrable_sq.const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (d12 φ)).norm.mul_const Ck)
        hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖Q (ω, x)‖ ∂P = ‖d12 φ x‖ * ∫ ω, Y x ω ^ 2 ∂P := by
        simp only [hQ, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, sq_abs]
        rw [integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      by_cases hx : L < ‖x‖
      · rw [hL x hx]; simp
      · push Not at hx
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [integral_sq_Y hW hYW x, sq_norm_rectL2]
        exact integral_sq_kerFun_rect_le hx
  have hQ1 := hQi.integral_prod_left
  rw [memLp_two_iff_integrable_sq hAm.aestronglyMeasurable]
  refine (hQ1.const_mul (∫ x, |d12 φ x|)).mono' (hAm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hc : Continuous fun x => Y x ω := hYc ω
  have h := sq_integral_mul_le (μ := volume) (a := fun x => d12 φ x) (b := fun x => Y x ω)
    (GFFInv.integrable_test (d12 φ)) (integrable_d12_mul_slice φ _ hc)
    (by
      have : Integrable (fun x => d12 φ x * Y x ω ^ 2) :=
        integrable_d12_mul_slice φ (fun x => Y x ω ^ 2) ((continuous_pow 2).comp hc)
      refine this.abs.congr (Eventually.of_forall fun x => ?_)
      simp only [abs_mul, abs_pow, sq_abs])
  exact h

/-- **Stochastic Fubini.** `∫ ∂_re ∂_im φ(x) Y(x) dx = W(kerFun φ)` almost surely. -/
theorem ae_integral_d12_mul_eq (φ : TestC) :
    (fun ω => ∫ x, d12 φ x * Y x ω) =ᵐ[P] W (testL2 φ) := by
  have := hW.isProbabilityMeasure
  set A : Ω → ℝ := fun ω => ∫ x, d12 φ x * Y x ω with hA
  set B : Ω → ℝ := W (testL2 φ) with hB
  set T := ⟪testL2 φ, testL2 φ⟫ with hT
  have hAL := memLp_A hW hYc hYm hYW φ
  have hBL := wn_memLp hW (testL2 φ)
  have hAW : ∀ g : WNSpace, ∫ ω, A ω * W g ω ∂P = ⟪testL2 φ, g⟫ := by
    intro g
    rw [hA, integral_A_mul hW hYc hYm hYW φ (wn_memLp hW g)]
    have e : ∀ x, ∫ ω, Y x ω * W g ω ∂P = ⟪rectL2 x, g⟫ := fun x => by
      rw [integral_Y_mul hW hYc hYm hYW x, wn_integral_mul hW]
    simp_rw [e]
    exact integral_d12_mul_inner_rectL2' φ g
  have hAA : ∫ ω, A ω * A ω ∂P = T := by
    have h1 : ∫ ω, A ω * A ω ∂P = ∫ x, d12 φ x * ∫ ω, Y x ω * A ω ∂P :=
      integral_A_mul hW hYc hYm hYW φ hAL
    rw [h1]
    have e : ∀ x, ∫ ω, Y x ω * A ω ∂P = ⟪rectL2 x, testL2 φ⟫ := fun x => by
      rw [integral_Y_mul hW hYc hYm hYW]
      calc ∫ ω, W (rectL2 x) ω * A ω ∂P = ∫ ω, A ω * W (rectL2 x) ω ∂P := by
            congr 1; funext ω; ring
        _ = _ := by rw [hAW, real_inner_comm]
    simp_rw [e]
    exact integral_d12_mul_inner_rectL2' φ _
  have hAB : ∫ ω, A ω * B ω ∂P = T := hAW _
  have hBB : ∫ ω, B ω * B ω ∂P = T := wn_integral_mul hW _ _
  have hiAA : Integrable (fun ω => A ω * A ω) P := hAL.integrable_mul hAL
  have hiAB : Integrable (fun ω => A ω * B ω) P := hAL.integrable_mul hBL
  have hiBB : Integrable (fun ω => B ω * B ω) P := hBL.integrable_mul hBL
  have hsq : ∫ ω, (A ω - B ω) ^ 2 ∂P = 0 := by
    have e : ∀ ω, (A ω - B ω) ^ 2 = A ω * A ω - 2 * (A ω * B ω) + B ω * B ω := fun ω => by ring
    simp_rw [e]
    have i1 : Integrable (fun ω => A ω * A ω - 2 * (A ω * B ω)) P := hiAA.sub (hiAB.const_mul 2)
    rw [integral_add i1 hiBB, integral_sub hiAA (hiAB.const_mul 2), integral_const_mul, hAA, hAB,
      hBB]
    ring
  have hint : Integrable (fun ω => (A ω - B ω) ^ 2) P := (hAL.sub hBL).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - B ω)) hint).mp hsq
  filter_upwards [h0] with ω hω
  have : (A ω - B ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

end SFub

end GFFExist
end LQGMetric
