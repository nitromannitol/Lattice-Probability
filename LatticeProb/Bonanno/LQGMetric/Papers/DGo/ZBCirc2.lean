/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.ZBCirc2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBCirc

/-!
# `zbKer(σ_{x,δ} * ψ_n) = ∫ ψ_n(z) K_{δ,x+z} dz` weakly, and the rate (task P2-DGZB)

* `inner_zbKerL2_circBump`: `⟪zbKer f_n, G⟫ = ∫ ψ_n(z) ⟪K_{δ,x+z}, G⟫ dz` (Fubini over `(z, q)`);
* `norm_zbKerL2_circBump_sub_le`: if `‖K_{δ,x+z} − K_{δ,x}‖ ≤ M` for `|z| < 2^{-n}`, then
  `‖zbKer f_n − K_{δ,x}‖ ≤ M`.

Own elementary proof (the mollified circle is the `ψ_n`-mixture of the translated circles).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real Function
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace ZB

open WhiteNoise HeatSq DDDF.P29WN GFFExist HeatDir CircleAvg

variable {a L δ : ℝ}

lemma measurable_dirCircFun_shift (hL : 0 < L) (x : ℂ) :
    Measurable fun p : ℂ × (ℝ × ℂ) => dirCircFun a L δ (x + p.1) p.2 := by
  have hF : StronglyMeasurable (uncurry fun (p : ℂ × (ℝ × ℂ)) (θ : ℝ) =>
      if 0 < p.2.1 / 2 then sqDirKernel a L (p.2.1 / 2) (circleMap (x + p.1) δ θ) p.2.2
        else 0) := by
    refine (DDDF.P29WN.measurable_sqDirKernel_joint (a := a) hL
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).div_const 2) ?_
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).stronglyMeasurable
    have : Continuous fun z : (ℂ × (ℝ × ℂ)) × ℝ => circleMap (x + z.1.1) δ z.2 := by
      simp only [circleMap]; fun_prop
    exact this.measurable
  have hG := (hF.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * π)))).measurable
  have e : (fun p : ℂ × (ℝ × ℂ) => dirCircFun a L δ (x + p.1) p.2) =
      fun p => (Ioi 0 ×ˢ sqOpen a L).indicator (fun q : ℝ × ℂ => (1 : ℝ)) p.2 * ((2 * π)⁻¹ *
        ∫ θ in Ioc 0 (2 * π), if 0 < p.2.1 / 2 then
          sqDirKernel a L (p.2.1 / 2) (circleMap (x + p.1) δ θ) p.2.2 else 0) := by
    funext p
    unfold dirCircFun
    by_cases hq : p.2 ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
    · have h2 : 0 < p.2.1 / 2 := half_pos hq.1
      simp only [indicator_of_mem hq, if_pos h2, one_mul,
        intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    · simp only [indicator_of_notMem hq, zero_mul]
  rw [e]
  exact ((measurable_const.indicator ((measurableSet_Ioi).prod (measurableSet_sqOpen a L))).comp
    measurable_snd).mul (hG.const_mul _)

lemma inner_dirCircKernel_eq (hL : 0 < L) (hδ : 0 < δ) {v : ℂ}
    (hB : closedBall v δ ⊆ sqOpen a L) (G : WNSpace) :
    ⟪dirCircKernel a L δ v, G⟫ = ∫ q, dirCircFun a L δ v q * G q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_dirCircKernel hL hδ hB] with q h1
  rw [h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

lemma sq_norm_dirCircKernel_eq (hL : 0 < L) (hδ : 0 < δ) {v : ℂ}
    (hB : closedBall v δ ⊆ sqOpen a L) :
    ‖dirCircKernel a L δ v‖ ^ 2 = ∫ q, dirCircFun a L δ v q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_dirCircKernel_eq hL hδ hB]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_dirCircKernel hL hδ hB] with q h1
  rw [h1, sq]

/-- `f_n 1_D` as an element of `BddOn D` -/
abbrev circBd (a L : ℝ) (n : ℕ) (x : ℂ) (δ : ℝ) : BddOn (sqOpen a L) :=
  extZeroTest (sqOpens a L) (circBump n x δ)

variable {n : ℕ} {x : ℂ}

lemma circBump_eq_zero_of (hδ : 0 < δ) (hB : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ n → closedBall (x + z) δ ⊆ sqOpen a L)
    {y : ℂ} (hy : y ∉ sqOpen a L) : circBump n x δ y = 0 := by
  rw [circBump_eq]
  have : ∀ θ, bumpTest n 0 (y - circleMap x δ θ) = 0 := by
    intro θ
    refine bumpTest_zero_eq_zero n (not_lt.1 fun h => hy (hB _ h ?_))
    rw [mem_closedBall, dist_eq_norm,
      show y - (x + (y - circleMap x δ θ)) = circleMap x δ θ - x by ring]
    simp [circleMap, abs_of_pos hδ]
  simp only [this, integral_zero, mul_zero]


lemma zbKerFun_circBd (hL : 0 < L) (hδ : 0 < δ)
    (hB : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ n → closedBall (x + z) δ ⊆ sqOpen a L) (q : ℝ × ℂ) :
    zbKerFun a L (circBd a L n x δ).1 q = ∫ z, bumpTest n 0 z * dirCircFun a L δ (x + z) q := by
  have hf : (circBd a L n x δ).1 = circBump n x δ := by
    funext y
    show (sqOpen a L).indicator (circBump n x δ) y = _
    by_cases hy : y ∈ sqOpen a L
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, circBump_eq_zero_of hδ hB hy]
  unfold zbKerFun dirCircFun
  rw [hf]
  by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L
  · simp only [indicator_of_mem hq,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    exact integral_circBump_mul_sqDirKernel hL (half_pos hq.1) n x δ q.2
  · simp only [indicator_of_notMem hq, mul_zero, integral_zero]

/-- **Weak mixture identity**: `⟪zbKer f_n, G⟫ = ∫ ψ_n(z) ⟪K_{δ,x+z}, G⟫ dz`. -/
theorem inner_zbKerL2_circBump (hL : 0 < L) (hδ : 0 < δ)
    (hB : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ n → closedBall (x + z) δ ⊆ sqOpen a L) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ n →
      ‖dirCircKernel a L δ (x + z) - dirCircKernel a L δ x‖ ≤ M) (G : WNSpace) :
    Integrable (fun z => bumpTest n 0 z * ⟪dirCircKernel a L δ (x + z), G⟫) ∧
    ⟪zbKerL2 a L hL (circBd a L n x δ), G⟫ =
      ∫ z, bumpTest n 0 z * ⟪dirCircKernel a L δ (x + z), G⟫ := by
  set ψ : ℂ → ℝ := fun z => bumpTest n 0 z
  set r : ℝ := (2 : ℝ)⁻¹ ^ n
  have hψ0 : ∀ z, r ≤ ‖z‖ → ψ z = 0 := fun z hz => bumpTest_zero_eq_zero n hz
  set Ck := (‖dirCircKernel a L δ x‖ + M) ^ 2
  have hG2 : Integrable fun q => G q ^ 2 := (Lp.memLp G).integrable_sq
  have hK2 : ∀ z, ‖z‖ < r → ∫ q, dirCircFun a L δ (x + z) q ^ 2 ≤ Ck := by
    intro z hz
    rw [← sq_norm_dirCircKernel_eq hL hδ (hB z hz)]
    have h1 := norm_le_insert' (dirCircKernel a L δ (x + z)) (dirCircKernel a L δ x)
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [hM z hz]) 2
  set H : ℂ × (ℝ × ℂ) → ℝ := fun p => ψ p.1 * dirCircFun a L δ (x + p.1) p.2 * G p.2 with hH
  have hHm : AEStronglyMeasurable H (volume.prod volume) :=
    (((bumpTest n 0).continuous.measurable.comp measurable_fst).mul
      (measurable_dirCircFun_shift hL x)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable G).comp_snd
  have hslice : ∀ z, Integrable fun q => H (z, q) := by
    intro z
    by_cases hz : ‖z‖ < r
    · simp only [hH, mul_assoc]
      exact ((memLp_dirCircFun hL hδ (hB z hz)).integrable_mul (Lp.memLp G)).const_mul _
    · simp only [hH, hψ0 z (not_lt.1 hz), zero_mul]
      exact integrable_zero _ _ _
  have hHi : Integrable H (volume.prod volume) := by
    rw [integrable_prod_iff hHm]
    refine ⟨Eventually.of_forall hslice, ?_⟩
    refine Integrable.mono' ((GFFInv.integrable_test (bumpTest n 0)).norm.mul_const
      ((Ck + ∫ q, G q ^ 2) / 2)) hHm.norm.integral_prod_right' (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
    by_cases hz : ‖z‖ < r
    · have hm2 := memLp_dirCircFun (a := a) hL hδ (hB z hz)
      have e0 : ∫ q, ‖H (z, q)‖ = ‖ψ z‖ * ∫ q, ‖dirCircFun a L δ (x + z) q‖ * ‖G q‖ := by
        simp only [hH, norm_mul]; rw [← integral_const_mul]; congr 1; funext q; ring
      rw [e0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := hm2.integrable_sq
      calc ∫ q, ‖dirCircFun a L δ (x + z) q‖ * ‖G q‖
          ≤ ∫ q, (dirCircFun a L δ (x + z) q ^ 2 + G q ^ 2) / 2 := by
            refine integral_mono ((hm2.integrable_mul (Lp.memLp G)).norm.congr
              (Eventually.of_forall fun q => norm_mul _ _)) ((h1.add hG2).div_const _)
              fun q => ?_
            simp only [Real.norm_eq_abs]
            nlinarith [sq_nonneg (|dirCircFun a L δ (x + z) q| - |G q|),
              sq_abs (dirCircFun a L δ (x + z) q), sq_abs (G q)]
        _ = ((∫ q, dirCircFun a L δ (x + z) q ^ 2) + ∫ q, G q ^ 2) / 2 := by
            rw [integral_div, integral_add h1 hG2]
        _ ≤ _ := by gcongr; exact hK2 z hz
    · have : ∀ q, H (z, q) = 0 := fun q => by simp only [hH, hψ0 z (not_lt.1 hz), zero_mul]
      simp only [this, norm_zero, integral_zero]
      positivity
  have hpt : ∀ z, ∫ q, H (z, q) = ψ z * ⟪dirCircKernel a L δ (x + z), G⟫ := by
    intro z
    by_cases hz : ‖z‖ < r
    · rw [inner_dirCircKernel_eq hL hδ (hB z hz), ← integral_const_mul]
      congr 1; funext q; simp only [hH]; ring
    · have : ∀ q, H (z, q) = 0 := fun q => by simp only [hH, hψ0 z (not_lt.1 hz), zero_mul]
      simp only [this, integral_zero, hψ0 z (not_lt.1 hz), zero_mul]
  refine ⟨hHi.integral_prod_left.congr (Eventually.of_forall hpt), ?_⟩
  rw [inner_zbKerL2_eq]
  have e1 : ∀ q, zbKerFun a L (circBd a L n x δ).1 q * G q = ∫ z, H (z, q) := fun q => by
    rw [zbKerFun_circBd hL hδ hB, ← integral_mul_const]
  simp_rw [e1]
  rw [← integral_integral_swap (f := fun z q => H (z, q)) hHi]
  exact integral_congr_ae (Eventually.of_forall hpt)

/-- **Rate**: `‖zbKer f_n − K_{δ,x}‖ ≤ sup_{|z| < 2^{-n}} ‖K_{δ,x+z} − K_{δ,x}‖`. -/
theorem norm_zbKerL2_circBump_sub_le (hL : 0 < L) (hδ : 0 < δ)
    (hB : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ n → closedBall (x + z) δ ⊆ sqOpen a L) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ < (2 : ℝ)⁻¹ ^ n →
      ‖dirCircKernel a L δ (x + z) - dirCircKernel a L δ x‖ ≤ M) :
    ‖zbKerL2 a L hL (circBd a L n x δ) - dirCircKernel a L δ x‖ ≤ M := by
  set ψ : ℂ → ℝ := fun z => bumpTest n 0 z
  set G := zbKerL2 a L hL (circBd a L n x δ) - dirCircKernel a L δ x
  have hM0 : 0 ≤ M := by simpa using hM 0 (by simp)
  obtain ⟨hi, he⟩ := inner_zbKerL2_circBump hL hδ hB hM G
  have hψi : Integrable ψ := GFFInv.integrable_test (bumpTest n 0)
  have hψ1 : ∫ z, ψ z = 1 := integral_bumpTest' n 0
  have h2 : ‖G‖ ^ 2 ≤ M * ‖G‖ := by
    rw [← real_inner_self_eq_norm_sq]
    calc ⟪G, G⟫ = ⟪zbKerL2 a L hL (circBd a L n x δ), G⟫ - ⟪dirCircKernel a L δ x, G⟫ := by
          simp only [G, inner_sub_left]
      _ = ∫ z, (ψ z * ⟪dirCircKernel a L δ (x + z), G⟫ - ψ z * ⟪dirCircKernel a L δ x, G⟫) := by
          rw [he, integral_sub hi (hψi.mul_const _), integral_mul_const, hψ1, one_mul]
      _ ≤ ∫ z, ψ z * (M * ‖G‖) := by
          refine integral_mono (hi.sub (hψi.mul_const _)) (hψi.mul_const _) fun z => ?_
          rw [← mul_sub, ← inner_sub_left]
          by_cases hz : ‖z‖ < (2 : ℝ)⁻¹ ^ n
          · refine mul_le_mul_of_nonneg_left ((real_inner_le_norm _ _).trans ?_)
              (bumpTest_nonneg n z)
            exact mul_le_mul_of_nonneg_right (hM z hz) (norm_nonneg _)
          · simp only [ψ, bumpTest_zero_eq_zero n (not_lt.1 hz), zero_mul, le_refl]
      _ = M * ‖G‖ := by rw [integral_mul_const, hψ1, one_mul]
  rcases (norm_nonneg G).eq_or_lt with h0 | h0
  · rw [← h0]; exact hM0
  · nlinarith

end ZB
end DGo
end LQGMetric
