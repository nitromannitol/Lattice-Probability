/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVer2SFub at commit 31e7483; only the module paths of local imports are changed.
   v4.35 port: use MemLp.aestronglyMeasurable in place of a conjunction projection.
   v4.35 port: replace deprecated push_neg with push Not. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistKerId
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2

/-!
# Stochastic Fubini for continuous `L²` fields (task P2-MKV)

`integral_A_mul_gen`, `memLp_A_gen`: for `Y : ℂ → Ω → ℝ` continuous in `x`, measurable in `ω`,
with `Y x ∈ L²(P)` and `E[Y(x)²]` bounded on compacts, and `φ ∈ 𝓓(ℂ)`:
`A = ∫ ∂_re∂_im φ(x) Y(x) dx ∈ L²(P)` and `E[A Z] = ∫ ∂_re∂_im φ(x) E[Y(x) Z] dx`.
These are `GFFExist.integral_A_mul`, `GFFExist.memLp_A` (`ExistSFub2`, task P2-EXIST) with the
white-noise hypotheses replaced by the two moment hypotheses they actually use (proofs copied
verbatim up to that replacement). Own elementary proof (standard stochastic Fubini).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovVer2

open GFFExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section SFub

variable {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x)) (hYL2 : ∀ x, MemLp (Y x) 2 P)
  (hYb : ∀ L : ℝ, ∃ Ck, ∀ x : ℂ, ‖x‖ ≤ L → ∫ ω, Y x ω ^ 2 ∂P ≤ Ck)
include hYc hYm hYL2 hYb

omit [IsProbabilityMeasure P] hYL2 hYb in
lemma measurable_Y₂_gen : Measurable fun p : Ω × ℂ => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

/-- the swap `E[(∫ ψ Y) Z] = ∫ ψ E[Y Z]` for `Z ∈ L²(P)` -/
lemma integral_A_mul_gen (φ : TestC) {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, d12 φ x * Y x ω) * Z ω ∂P = ∫ x, d12 φ x * ∫ ω, Y x ω * Z ω ∂P := by
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  obtain ⟨Ck, hCk⟩ := hYb L
  set H : Ω × ℂ → ℝ := fun p => d12 φ p.2 * Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod volume) :=
    ((((d12 φ).continuous.measurable.comp measurable_snd).mul
      (measurable_Y₂_gen hYc hYm)).aestronglyMeasurable).mul hZ.aestronglyMeasurable.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x
    have h1 := (hYL2 x).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((hYL2 x).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = _ := by rw [integral_div, integral_add h1 hZ2]
  have hY2 : ∀ x, ‖x‖ ≤ L → ∫ ω, Y x ω ^ 2 ∂P ≤ Ck := by
    exact hCk
  have hHi : Integrable H (P.prod volume) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hH, mul_assoc]
      exact ((hYL2 x).integrable_mul hZ).const_mul _
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

lemma memLp_A_gen (φ : TestC) : MemLp (fun ω => ∫ x, d12 φ x * Y x ω) 2 P := by
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 φ)
  obtain ⟨Ck, hCk⟩ := hYb L
  have hjm := measurable_Y₂_gen hYc hYm
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
      exact (hYL2 x).integrable_sq.const_mul _
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
        exact hCk x hx
  have hQ1 := hQi.integral_prod_left
  rw [memLp_two_iff_integrable_sq hAm.aestronglyMeasurable]
  refine (hQ1.const_mul (∫ x, |d12 φ x|)).mono' (hAm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hc : Continuous fun x => Y x ω := hYc ω
  have h := GFFExist.sq_integral_mul_le (μ := volume) (a := fun x => d12 φ x) (b := fun x => Y x ω)
    (GFFInv.integrable_test (d12 φ)) (GFFExist.integrable_d12_mul_slice φ _ hc)
    (by
      have : Integrable (fun x => d12 φ x * Y x ω ^ 2) :=
        GFFExist.integrable_d12_mul_slice φ (fun x => Y x ω ^ 2) ((continuous_pow 2).comp hc)
      refine this.abs.congr (Eventually.of_forall fun x => ?_)
      simp only [abs_mul, abs_pow, sq_abs])
  exact h

end SFub

end MarkovVer2
end LQGMetric
