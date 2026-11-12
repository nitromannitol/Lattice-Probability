/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127I1 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable). -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2

/-!
# (L4) of D127, part 1: stochastic Fubini against a test function (packet P-127I, P2-HEATI)

Copy of `DGo.ZB.integral_d12_mul_inner_gen` / `DGo.ZB.ae_integral_d12_mul_eq_gen`
(Papers/DGo/ZBSFubG, task P2-DGZB; themselves from `GFFExist.integral_d12_mul_inner_rectL2`,
`GFFExist.ae_integral_d12_mul_eq`) with the weight `∂_re∂_im φ` replaced by an arbitrary test
function `ψ` (the proofs only use that the weight is a test function). Used for the pairing
`∫ ψ h_{t,∞} = √π W(K^{(t,∞)}(ψ 1_U))` of the continuous coarse field of CONF C:722–731.

* `integral_tmul_inner_gen`: `∫ ψ(x) ⟪k x, G⟫ dx = ∫ k_ψ G`;
* `ae_integral_tmul_eq_gen`: `∫ ψ(x) Y(x) dx = W(T)` a.s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open WhiteNoise GFFExist

lemma integrable_tmul_slice (ψ : TestC) (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable fun x => ψ x * f x :=
  (ψ.continuous.mul hf).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right

/-- **Fubini against a family of kernels** (copy of `DGo.ZB.integral_d12_mul_inner_gen`). -/
theorem integral_tmul_inner_gen (ψ : TestC) (k : ℂ → ℝ × ℂ → ℝ)
    (hkm : Measurable fun p : ℂ × (ℝ × ℂ) => k p.1 p.2) (hk2 : ∀ x, MemLp (k x) 2 volume)
    {Ck : ℝ} (hkb : ∀ x, ∫ q, k x q ^ 2 ≤ Ck) (kφ : ℝ × ℂ → ℝ)
    (hid : ∀ q, ∫ x, ψ x * k x q = kφ q) (G : WNSpace) :
    ∫ x, ψ x * ∫ q, k x q * G q = ∫ q, kφ q * G q := by
  have hG2 : Integrable fun q => G q ^ 2 := (Lp.memLp G).integrable_sq
  set F : ℂ × (ℝ × ℂ) → ℝ := fun p => ψ p.1 * k p.1 p.2 * G p.2 with hF
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    ((((ψ).continuous.measurable.comp measurable_fst).mul
      hkm).aestronglyMeasurable).mul (Lp.aestronglyMeasurable G).comp_snd
  have hslice : ∀ x, Integrable fun q => k x q * G q := fun x =>
    ((hk2 x).integrable_mul (Lp.memLp G))
  have hbd : ∀ x, ∫ q, ‖k x q‖ * ‖G q‖ ≤ ((∫ q, k x q ^ 2) + ∫ q, G q ^ 2) / 2 := by
    intro x
    have h1 := (hk2 x).integrable_sq
    calc ∫ q, ‖k x q‖ * ‖G q‖
        ≤ ∫ q, (k x q ^ 2 + G q ^ 2) / 2 := by
          refine integral_mono ((hslice x).norm.congr (Eventually.of_forall fun q => norm_mul _ _))
            ((h1.add hG2).div_const _) fun q => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|k x q| - |G q|), sq_abs (k x q), sq_abs (G q)]
      _ = _ := by rw [integral_div, integral_add h1 hG2]
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hF, mul_assoc]; exact (hslice x).const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (ψ)).norm.mul_const
        ((Ck + ∫ q, G q ^ 2) / 2)) ?_ (Eventually.of_forall fun x => ?_)
      · exact hFm.norm.integral_prod_right'
      · simp only [hF, mul_assoc, norm_mul, integral_const_mul, norm_norm]
        rw [Real.norm_of_nonneg (integral_nonneg fun q => by positivity)]
        refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (abs_nonneg _)
        gcongr
        exact hkb x
  have e1 : ∀ x, ψ x * ∫ q, k x q * G q = ∫ q, F (x, q) := fun x => by
    rw [← integral_const_mul]
    congr 1; funext q; simp only [hF]; ring
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x q => F (x, q)) hFi]
  congr 1; funext q
  simp only [hF]
  rw [integral_mul_const, hid]

section SFub

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  (hW : IsWhiteNoise P W) {R : ℂ → WNSpace} {Cr : ℝ} (hRb : ∀ x, ‖R x‖ ^ 2 ≤ Cr)
  {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x)) (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (R x))
include hW hYc hYm hYW

omit hYc hYm in
lemma memLp_YgT (x : ℂ) : MemLp (Y x) 2 P := (wn_memLp hW _).ae_eq (hYW x).symm

omit hYc hYm in
lemma integral_YgT_mul (x : ℂ) {Z : Ω → ℝ} :
    ∫ ω, Y x ω * Z ω ∂P = ∫ ω, W (R x) ω * Z ω ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h]

omit hW hYW in
lemma measurable_YgT₂ : Measurable fun p : Ω × ℂ => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

omit hYc hYm in
lemma integral_sq_YgT (x : ℂ) : ∫ ω, Y x ω ^ 2 ∂P = ‖R x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h, sq]

include hRb

/-- the swap `E[(∫ ψ Y) Z] = ∫ ψ E[Y Z]` for `Z ∈ L²(P)` -/
lemma integral_AgT_mul (ψ : TestC) {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, ψ x * Y x ω) * Z ω ∂P = ∫ x, ψ x * ∫ ω, Y x ω * Z ω ∂P := by
  have := hW.isProbabilityMeasure
  set H : Ω × ℂ → ℝ := fun p => ψ p.2 * Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod volume) :=
    ((((ψ).continuous.measurable.comp measurable_snd).mul
      (measurable_YgT₂ hYc hYm)).aestronglyMeasurable).mul hZ.aestronglyMeasurable.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x
    have h1 := (memLp_YgT hW hYW x).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((memLp_YgT hW hYW x).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = _ := by rw [integral_div, integral_add h1 hZ2]
  have hHi : Integrable H (P.prod volume) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hH, mul_assoc]
      exact ((memLp_YgT hW hYW x).integrable_mul hZ).const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (ψ)).norm.mul_const
        ((Cr + ∫ ω, Z ω ^ 2 ∂P) / 2)) hHm.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖H (ω, x)‖ ∂P = ‖ψ x‖ * ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P := by
        simp only [hH, norm_mul]; rw [← integral_const_mul]; congr 1; funext ω; ring
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (norm_nonneg _)
      gcongr
      rw [integral_sq_YgT hW hYW x]
      exact hRb x
  have e1 : ∀ ω, (∫ x, ψ x * Y x ω) * Z ω = ∫ x, H (ω, x) := fun ω => by
    rw [← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun ω x => H (ω, x)) hHi]
  congr 1; funext x
  simp only [hH]
  rw [← integral_const_mul]
  congr 1; funext ω; ring

lemma memLp_AgT (ψ : TestC) : MemLp (fun ω => ∫ x, ψ x * Y x ω) 2 P := by
  have := hW.isProbabilityMeasure
  have hjm := measurable_YgT₂ hYc hYm
  have hAm : Measurable fun ω => ∫ x, ψ x * Y x ω :=
    ((((ψ).continuous.measurable.comp measurable_snd).mul hjm).stronglyMeasurable.integral_prod_right'
      (ν := volume)).measurable
  set Q : Ω × ℂ → ℝ := fun p => |ψ p.2| * Y p.2 p.1 ^ 2 with hQ
  have hQm : Measurable Q := (continuous_abs.measurable.comp
    ((ψ).continuous.measurable.comp measurable_snd)).mul (hjm.pow_const 2)
  have hQi : Integrable Q (P.prod volume) := by
    rw [integrable_prod_iff' hQm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hQ]
      exact (memLp_YgT hW hYW x).integrable_sq.const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (ψ)).norm.mul_const Cr)
        hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖Q (ω, x)‖ ∂P = ‖ψ x‖ * ∫ ω, Y x ω ^ 2 ∂P := by
        simp only [hQ, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, sq_abs]
        rw [integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [integral_sq_YgT hW hYW x]
      exact hRb x
  have hQ1 := hQi.integral_prod_left
  rw [memLp_two_iff_integrable_sq hAm.aestronglyMeasurable]
  refine (hQ1.const_mul (∫ x, |ψ x|)).mono' (hAm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hc : Continuous fun x => Y x ω := hYc ω
  have h := sq_integral_mul_le (μ := volume) (a := fun x => ψ x) (b := fun x => Y x ω)
    (GFFInv.integrable_test (ψ)) (integrable_tmul_slice ψ _ hc)
    (by
      have : Integrable (fun x => ψ x * Y x ω ^ 2) :=
        integrable_tmul_slice ψ (fun x => Y x ω ^ 2) ((continuous_pow 2).comp hc)
      refine this.abs.congr (Eventually.of_forall fun x => ?_)
      simp only [abs_mul, abs_pow, sq_abs])
  exact h

/-- **Stochastic Fubini, generic kernels** (adapted from `GFFExist.ae_integral_d12_mul_eq`):
`∫ ψ(x) Y(x) dx = W(T)` almost surely. -/
theorem ae_integral_tmul_eq_gen (ψ : TestC) {T : WNSpace}
    (hRT : ∀ G : WNSpace, ∫ x, ψ x * ⟪R x, G⟫ = ⟪T, G⟫) :
    (fun ω => ∫ x, ψ x * Y x ω) =ᵐ[P] W T := by
  have := hW.isProbabilityMeasure
  set A : Ω → ℝ := fun ω => ∫ x, ψ x * Y x ω with hA
  set B : Ω → ℝ := W T with hB
  have hAL := memLp_AgT hW hRb hYc hYm hYW ψ
  have hBL := wn_memLp hW T
  have hAW : ∀ g : WNSpace, ∫ ω, A ω * W g ω ∂P = ⟪T, g⟫ := by
    intro g
    rw [hA, integral_AgT_mul hW hRb hYc hYm hYW ψ (wn_memLp hW g)]
    have e : ∀ x, ∫ ω, Y x ω * W g ω ∂P = ⟪R x, g⟫ := fun x => by
      rw [integral_YgT_mul hW hYW x, wn_integral_mul hW]
    simp_rw [e]
    exact hRT g
  have hAA : ∫ ω, A ω * A ω ∂P = ⟪T, T⟫ := by
    have h1 : ∫ ω, A ω * A ω ∂P = ∫ x, ψ x * ∫ ω, Y x ω * A ω ∂P :=
      integral_AgT_mul hW hRb hYc hYm hYW ψ hAL
    rw [h1]
    have e : ∀ x, ∫ ω, Y x ω * A ω ∂P = ⟪R x, T⟫ := fun x => by
      rw [integral_YgT_mul hW hYW]
      calc ∫ ω, W (R x) ω * A ω ∂P = ∫ ω, A ω * W (R x) ω ∂P := by
            congr 1; funext ω; ring
        _ = _ := by rw [hAW, real_inner_comm]
    simp_rw [e]
    exact hRT _
  have hAB : ∫ ω, A ω * B ω ∂P = ⟪T, T⟫ := hAW _
  have hBB : ∫ ω, B ω * B ω ∂P = ⟪T, T⟫ := wn_integral_mul hW _ _
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
end LQGMetric.CONF.ZBM
