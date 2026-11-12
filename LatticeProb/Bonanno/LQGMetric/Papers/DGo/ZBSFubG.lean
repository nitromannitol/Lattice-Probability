/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.ZBSFubG at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable). -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2

/-!
# Stochastic Fubini for antiderivative fields, generic kernels (task P2-DGZB)

The two halves of the whole-plane stochastic Fubini step (`GFFExist.integral_d12_mul_inner_rectL2`,
`GFFExist.ae_integral_d12_mul_eq`, P2-EXIST) with the rectangle kernels `kerFun 1_{[0,x]}`
replaced by an arbitrary family:

* `integral_d12_mul_inner_gen`: for kernels `k x ∈ L²(ℝ × ℂ)`, jointly measurable, with
  `‖k x‖² ≤ C` and `∫ ∂_re∂_im φ(x) k x q dx = k_φ q` pointwise:
  `∫ ∂_re∂_im φ(x) ⟪k x, G⟫ dx = ∫ k_φ G` for every `G ∈ L²`;
* `ae_integral_d12_mul_eq_gen`: for a white noise `W`, `R : ℂ → L²` with `‖R x‖² ≤ C`,
  `∫ ∂_re∂_im φ(x) ⟪R x, G⟫ dx = ⟪T, G⟫` for all `G`, and a version `Y` of `W ∘ R` continuous in
  `x`: `∫ ∂_re∂_im φ(x) Y(x) dx = W(T)` a.s.

The proofs are those of `Field/ExistSFub` and `Field/ExistSFub2` verbatim, with the specific
kernel bound `integral_sq_kerFun_rect_le` replaced by the hypothesis `‖R x‖² ≤ C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace ZB

open WhiteNoise GFFExist

/-- **Fubini against a family of kernels** (adapted from `integral_d12_mul_inner_rectL2`). -/
theorem integral_d12_mul_inner_gen (φ : TestC) (k : ℂ → ℝ × ℂ → ℝ)
    (hkm : Measurable fun p : ℂ × (ℝ × ℂ) => k p.1 p.2) (hk2 : ∀ x, MemLp (k x) 2 volume)
    {Ck : ℝ} (hkb : ∀ x, ∫ q, k x q ^ 2 ≤ Ck) (kφ : ℝ × ℂ → ℝ)
    (hid : ∀ q, ∫ x, d12 φ x * k x q = kφ q) (G : WNSpace) :
    ∫ x, d12 φ x * ∫ q, k x q * G q = ∫ q, kφ q * G q := by
  have hG2 : Integrable fun q => G q ^ 2 := (Lp.memLp G).integrable_sq
  set F : ℂ × (ℝ × ℂ) → ℝ := fun p => d12 φ p.1 * k p.1 p.2 * G p.2 with hF
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    ((((d12 φ).continuous.measurable.comp measurable_fst).mul
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
    · refine Integrable.mono' ((GFFInv.integrable_test (d12 φ)).norm.mul_const
        ((Ck + ∫ q, G q ^ 2) / 2)) ?_ (Eventually.of_forall fun x => ?_)
      · exact hFm.norm.integral_prod_right'
      · simp only [hF, mul_assoc, norm_mul, integral_const_mul, norm_norm]
        rw [Real.norm_of_nonneg (integral_nonneg fun q => by positivity)]
        refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (abs_nonneg _)
        gcongr
        exact hkb x
  have e1 : ∀ x, d12 φ x * ∫ q, k x q * G q = ∫ q, F (x, q) := fun x => by
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
lemma memLp_Yg (x : ℂ) : MemLp (Y x) 2 P := (wn_memLp hW _).ae_eq (hYW x).symm

omit hYc hYm in
lemma integral_Yg_mul (x : ℂ) {Z : Ω → ℝ} :
    ∫ ω, Y x ω * Z ω ∂P = ∫ ω, W (R x) ω * Z ω ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h]

omit hW hYW in
lemma measurable_Yg₂ : Measurable fun p : Ω × ℂ => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

omit hYc hYm in
lemma integral_sq_Yg (x : ℂ) : ∫ ω, Y x ω ^ 2 ∂P = ‖R x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
  refine integral_congr_ae ?_
  filter_upwards [hYW x] with ω h
  rw [h, sq]

include hRb

/-- the swap `E[(∫ ψ Y) Z] = ∫ ψ E[Y Z]` for `Z ∈ L²(P)` -/
lemma integral_Ag_mul (φ : TestC) {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, d12 φ x * Y x ω) * Z ω ∂P = ∫ x, d12 φ x * ∫ ω, Y x ω * Z ω ∂P := by
  have := hW.isProbabilityMeasure
  set H : Ω × ℂ → ℝ := fun p => d12 φ p.2 * Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod volume) :=
    ((((d12 φ).continuous.measurable.comp measurable_snd).mul
      (measurable_Yg₂ hYc hYm)).aestronglyMeasurable).mul hZ.aestronglyMeasurable.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x
    have h1 := (memLp_Yg hW hYW x).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((memLp_Yg hW hYW x).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = _ := by rw [integral_div, integral_add h1 hZ2]
  have hHi : Integrable H (P.prod volume) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hH, mul_assoc]
      exact ((memLp_Yg hW hYW x).integrable_mul hZ).const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (d12 φ)).norm.mul_const
        ((Cr + ∫ ω, Z ω ^ 2 ∂P) / 2)) hHm.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖H (ω, x)‖ ∂P = ‖d12 φ x‖ * ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P := by
        simp only [hH, norm_mul]; rw [← integral_const_mul]; congr 1; funext ω; ring
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (norm_nonneg _)
      gcongr
      rw [integral_sq_Yg hW hYW x]
      exact hRb x
  have e1 : ∀ ω, (∫ x, d12 φ x * Y x ω) * Z ω = ∫ x, H (ω, x) := fun ω => by
    rw [← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun ω x => H (ω, x)) hHi]
  congr 1; funext x
  simp only [hH]
  rw [← integral_const_mul]
  congr 1; funext ω; ring

lemma memLp_Ag (φ : TestC) : MemLp (fun ω => ∫ x, d12 φ x * Y x ω) 2 P := by
  have := hW.isProbabilityMeasure
  have hjm := measurable_Yg₂ hYc hYm
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
      exact (memLp_Yg hW hYW x).integrable_sq.const_mul _
    · refine Integrable.mono' ((GFFInv.integrable_test (d12 φ)).norm.mul_const Cr)
        hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
        (Eventually.of_forall fun x => ?_)
      have e0 : ∫ ω, ‖Q (ω, x)‖ ∂P = ‖d12 φ x‖ * ∫ ω, Y x ω ^ 2 ∂P := by
        simp only [hQ, norm_mul, norm_pow, Real.norm_eq_abs, abs_abs, sq_abs]
        rw [integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [integral_sq_Yg hW hYW x]
      exact hRb x
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

/-- **Stochastic Fubini, generic kernels** (adapted from `GFFExist.ae_integral_d12_mul_eq`):
`∫ ∂_re ∂_im φ(x) Y(x) dx = W(T)` almost surely. -/
theorem ae_integral_d12_mul_eq_gen (φ : TestC) {T : WNSpace}
    (hRT : ∀ G : WNSpace, ∫ x, d12 φ x * ⟪R x, G⟫ = ⟪T, G⟫) :
    (fun ω => ∫ x, d12 φ x * Y x ω) =ᵐ[P] W T := by
  have := hW.isProbabilityMeasure
  set A : Ω → ℝ := fun ω => ∫ x, d12 φ x * Y x ω with hA
  set B : Ω → ℝ := W T with hB
  have hAL := memLp_Ag hW hRb hYc hYm hYW φ
  have hBL := wn_memLp hW T
  have hAW : ∀ g : WNSpace, ∫ ω, A ω * W g ω ∂P = ⟪T, g⟫ := by
    intro g
    rw [hA, integral_Ag_mul hW hRb hYc hYm hYW φ (wn_memLp hW g)]
    have e : ∀ x, ∫ ω, Y x ω * W g ω ∂P = ⟪R x, g⟫ := fun x => by
      rw [integral_Yg_mul hW hYW x, wn_integral_mul hW]
    simp_rw [e]
    exact hRT g
  have hAA : ∫ ω, A ω * A ω ∂P = ⟪T, T⟫ := by
    have h1 : ∫ ω, A ω * A ω ∂P = ∫ x, d12 φ x * ∫ ω, Y x ω * A ω ∂P :=
      integral_Ag_mul hW hRb hYc hYm hYW φ hAL
    rw [h1]
    have e : ∀ x, ∫ ω, Y x ω * A ω ∂P = ⟪R x, T⟫ := fun x => by
      rw [integral_Yg_mul hW hYW]
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

end ZB
end DGo
end LQGMetric
