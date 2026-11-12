/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA3SFub at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable).
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2

/-!
For a white noise `W`, a family `k : ℂ → L²` bounded and Bochner integrable for a finite measure
`μ` carried by a compact set `S`, and a version `Y` of `z ↦ W(k z)` on `S` continuous in `z`:

`ae_integral_eq_wn`: `∫ Y(z) μ(dz) = W(∫ k z μ(dz))` a.s.

Used to identify the circle averages of DG's continuous modifications (DG Lemma 3.1,
`metric-comparison-final.tex` DG:966–974) with the white-noise integrals of the circle kernels.
Proof as `GFFExist.ae_integral_d12_mul_eq` (`E(A − B)² = 0` by Fubini on `Ω × ℂ`); own
elementary proof (standard stochastic Fubini).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DG

open WhiteNoise GFFExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

section SFub

variable (hW : IsWhiteNoise P W) {S : Set ℂ} (hS : IsCompact S) {μ : Measure ℂ}
  [IsFiniteMeasure μ] (hμS : μ Sᶜ = 0) {k : ℂ → WNSpace} {M : ℝ} (hkM : ∀ z ∈ S, ‖k z‖ ≤ M)
  {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
  (hYW : ∀ x ∈ S, Y x =ᵐ[P] W (k x))

include hW hYW in
lemma sfub_memLp_Y {x : ℂ} (hx : x ∈ S) : MemLp (Y x) 2 P := (wn_memLp hW _).ae_eq (hYW x hx).symm

include hYW in
lemma sfub_integral_Y_mul {x : ℂ} (hx : x ∈ S) (Z : Ω → ℝ) :
    ∫ ω, Y x ω * Z ω ∂P = ∫ ω, W (k x) ω * Z ω ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [hYW x hx] with ω h
  rw [h]

include hYc hYm in
lemma sfub_measurable_Y₂ : Measurable fun p : Ω × ℂ => Y p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm).comp
    measurable_swap

include hW hYW hkM in
lemma sfub_integral_sq_Y {x : ℂ} (hx : x ∈ S) : ∫ ω, Y x ω ^ 2 ∂P ≤ M ^ 2 := by
  have e : ∫ ω, Y x ω ^ 2 ∂P = ‖k x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
    refine integral_congr_ae ?_
    filter_upwards [hYW x hx] with ω h
    rw [h, sq]
  rw [e]
  exact pow_le_pow_left₀ (norm_nonneg _) (hkM x hx) 2

include hS hμS hYc in
lemma sfub_integrable_slice (ω : Ω) : Integrable (fun x => Y x ω) μ := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hYc ω).continuousOn
  exact Integrable.of_bound (hYc ω).aestronglyMeasurable C
    ((show ∀ᵐ x ∂μ, x ∈ S from mem_ae_iff.2 hμS).mono fun x hx => hC x hx)

include hW hμS hkM hYc hYm hYW in
/-- the swap `E[(∫ Y dμ) Z] = ∫ E[Y Z] dμ` for `Z ∈ L²(P)` -/
lemma sfub_integral_A_mul {Z : Ω → ℝ} (hZ : MemLp Z 2 P) :
    ∫ ω, (∫ x, Y x ω ∂μ) * Z ω ∂P = ∫ x, (∫ ω, Y x ω * Z ω ∂P) ∂μ := by
  have := hW.isProbabilityMeasure
  have hSae : ∀ᵐ x ∂μ, x ∈ S := mem_ae_iff.2 hμS
  set H : Ω × ℂ → ℝ := fun p => Y p.2 p.1 * Z p.1 with hH
  have hHm : AEStronglyMeasurable H (P.prod μ) :=
    (sfub_measurable_Y₂ hYc hYm).aestronglyMeasurable.mul hZ.aestronglyMeasurable.comp_fst
  have hZ2 := hZ.integrable_sq
  have hbd : ∀ x ∈ S, ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ (M ^ 2 + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
    intro x hx
    have h1 := (sfub_memLp_Y hW hYW hx).integrable_sq
    calc ∫ ω, ‖Y x ω‖ * ‖Z ω‖ ∂P ≤ ∫ ω, (Y x ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
          refine integral_mono (((sfub_memLp_Y hW hYW hx).integrable_mul hZ).norm.congr
            (Eventually.of_forall fun ω => norm_mul _ _)) ((h1.add hZ2).div_const _) fun ω => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|Y x ω| - |Z ω|), sq_abs (Y x ω), sq_abs (Z ω)]
      _ = ((∫ ω, Y x ω ^ 2 ∂P) + ∫ ω, Z ω ^ 2 ∂P) / 2 := by
          rw [integral_div, integral_add h1 hZ2]
      _ ≤ _ := by gcongr; exact sfub_integral_sq_Y hW hkM hYW hx
  have hHi : Integrable H (P.prod μ) := by
    rw [integrable_prod_iff' hHm]
    refine ⟨hSae.mono fun x hx => ?_, ?_⟩
    · exact (sfub_memLp_Y hW hYW hx).integrable_mul hZ
    · refine Integrable.of_bound hHm.norm.prod_swap.integral_prod_right'
        ((M ^ 2 + ∫ ω, Z ω ^ 2 ∂P) / 2) (hSae.mono fun x hx => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [hH, norm_mul]
      exact hbd x hx
  have e1 : ∀ ω, (∫ x, Y x ω ∂μ) * Z ω = ∫ x, H (ω, x) ∂μ := fun ω => by
    rw [← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun ω x => H (ω, x)) hHi]

include hW hS hμS hkM hYc hYm hYW in
lemma sfub_memLp_A : MemLp (fun ω => ∫ x, Y x ω ∂μ) 2 P := by
  have := hW.isProbabilityMeasure
  have hSae : ∀ᵐ x ∂μ, x ∈ S := mem_ae_iff.2 hμS
  have hjm := sfub_measurable_Y₂ hYc hYm
  have hAm : Measurable fun ω => ∫ x, Y x ω ∂μ :=
    (hjm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  set Q : Ω × ℂ → ℝ := fun p => Y p.2 p.1 ^ 2 with hQ
  have hQm : Measurable Q := hjm.pow_const 2
  have hQi : Integrable Q (P.prod μ) := by
    rw [integrable_prod_iff' hQm.aestronglyMeasurable]
    refine ⟨hSae.mono fun x hx => (sfub_memLp_Y hW hYW hx).integrable_sq, ?_⟩
    refine Integrable.of_bound hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
      (M ^ 2) (hSae.mono fun x hx => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [hQ, norm_pow, Real.norm_eq_abs, sq_abs]
    exact sfub_integral_sq_Y hW hkM hYW hx
  have hQ1 := hQi.integral_prod_left
  rw [memLp_two_iff_integrable_sq hAm.aestronglyMeasurable]
  refine (hQ1.const_mul (∫ _x, |(1 : ℝ)| ∂μ)).mono' (hAm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hi := sfub_integrable_slice hS hμS hYc ω
  have hi2 : Integrable (fun x => Y x ω ^ 2) μ := by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn ((hYc ω).pow 2).continuousOn
    exact Integrable.of_bound ((hYc ω).pow 2).aestronglyMeasurable C
      ((show ∀ᵐ x ∂μ, x ∈ S from mem_ae_iff.2 hμS).mono fun x hx => hC x hx)
  have h := sq_integral_mul_le (μ := μ) (a := fun _ => (1 : ℝ)) (b := fun x => Y x ω)
    (integrable_const _) (by simpa using hi) (by simpa using hi2)
  simpa [Q] using h

include hW hS hμS hkM hYc hYm hYW in
/-- **Stochastic Fubini.** `∫ Y dμ = W(∫ k dμ)` almost surely. -/
theorem ae_integral_eq_wn (hk : Integrable k μ) :
    (fun ω => ∫ x, Y x ω ∂μ) =ᵐ[P] W (∫ x, k x ∂μ) := by
  have := hW.isProbabilityMeasure
  have hSae : ∀ᵐ x ∂μ, x ∈ S := mem_ae_iff.2 hμS
  set A : Ω → ℝ := fun ω => ∫ x, Y x ω ∂μ with hA
  set B : Ω → ℝ := W (∫ x, k x ∂μ) with hB
  set T := ⟪∫ x, k x ∂μ, ∫ x, k x ∂μ⟫ with hT
  have hAL := sfub_memLp_A hW hS hμS hkM hYc hYm hYW
  have hBL := wn_memLp hW (∫ x, k x ∂μ)
  have hAW : ∀ g : WNSpace, ∫ ω, A ω * W g ω ∂P = ⟪∫ x, k x ∂μ, g⟫ := by
    intro g
    rw [hA, sfub_integral_A_mul hW hμS hkM hYc hYm hYW (wn_memLp hW g), real_inner_comm,
      ← integral_inner (𝕜 := ℝ) hk g]
    refine integral_congr_ae (hSae.mono fun x hx => ?_)
    simp only
    rw [sfub_integral_Y_mul hYW hx, wn_integral_mul hW, real_inner_comm]
  have hAA : ∫ ω, A ω * A ω ∂P = T := by
    rw [sfub_integral_A_mul hW hμS hkM hYc hYm hYW hAL, hT,
      ← integral_inner (𝕜 := ℝ) hk (∫ x, k x ∂μ)]
    refine integral_congr_ae (hSae.mono fun x hx => ?_)
    simp only
    rw [sfub_integral_Y_mul hYW hx]
    calc ∫ ω, W (k x) ω * A ω ∂P = ∫ ω, A ω * W (k x) ω ∂P := by
          congr 1; funext ω; ring
      _ = _ := by rw [hAW]
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

end DG
end LQGMetric
