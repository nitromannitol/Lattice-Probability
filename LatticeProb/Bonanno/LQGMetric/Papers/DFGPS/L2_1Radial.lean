/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1Radial at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl3
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: pairing a distribution with a radial test function (deterministic part)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:715–717: "Using the circle average
process we may therefore write in polar coordinates …". For every distribution `T` and every test
function `φ` radial about `z`:

* `tendsto_integral_mul_pair_bumpTest`: `∫ φ(y) ⟨T, ψ_{n,y}⟩ dy → ⟨T, φ⟩` (regularization
  `⟨T, φ * ψ_n⟩ = ∫ φ(y) ⟨T, ψ_n(· − y)⟩ dy = ∫ ψ_n(t) ⟨T, φ(· − t)⟩ dt → ⟨T, φ⟩`; Hörmander,
  *ALPDO I*, Thm 4.1.1 / (4.1.2); same argument as `MarkovWeyl3.integral_mul_weylFun`, reusing
  `MarkovWeyl3.exists_conv_pairing_on`, `MarkovWeyl2.continuous_transFam` and mathlib's
  `ContDiffBump.convolution_tendsto_right_of_continuous`);
* `integral_mul_eq_polar`: `∫ φ m = ∫_0^∞ 2π r φ(z + r) ⨍_{∂B(z,r)} m dr` for continuous `m`
  (polar coordinates, mathlib `Complex.integral_comp_polarCoord_symm`);
* `tendsto_polar_circBump`: hence `∫_0^∞ 2π r φ(z + r) ⟨T, σ_{z,r} * ψ_n⟩ dr → ⟨T, φ⟩`
  (`CircleAvg.circleAverage_pairing`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric TopologicalSpace
open scoped Real Distributions Convolution

namespace LQGMetric.DFGPS

/-- **Regularization**: `∫ φ(y) ⟨T, ψ_{n,y}⟩ dy → ⟨T, φ⟩` for every distribution `T`. -/
theorem tendsto_integral_mul_pair_bumpTest (T : DistC) (φ : TestC) :
    Tendsto (fun n : ℕ => ∫ y, φ y * T (bumpTest n y)) atTop (𝓝 (T φ)) := by
  obtain ⟨R, hR0⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  have hR : ∀ y, R < ‖y‖ → φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR0 h; rw [mem_closedBall, dist_zero_right] at this; linarith
  set K' : Compacts ℂ := MarkovWeyl.ballK0 (R + 1)
  have hK'V : (K' : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ) := fun _ _ => mem_univ _
  let L : 𝓓^{⊤}_{K'}(ℂ, ℝ) →L[ℝ] ℝ := T.comp (TestFunction.ofSupportedInCLM ℝ hK'V)
  have hqK : ∀ t : ℂ, closedBall (MarkovWeyl2.projB 0 1 t) R ⊆ (K' : Set ℂ) := fun t =>
    closedBall_subset_closedBall' (by
      have := MarkovWeyl2.norm_projB_sub_le one_pos 0 t
      rw [sub_zero] at this; rw [dist_zero_right]; linarith)
  let G : ℂ → 𝓓^{⊤}_{K'}(ℂ, ℝ) := MarkovWeyl2.transFam φ.contDiff hR hqK
  have hGc : Continuous G :=
    MarkovWeyl2.continuous_transFam φ.contDiff hR hqK (MarkovWeyl2.continuous_projB 0 1)
  let c : ℂ → ℝ := fun t => L (G t)
  have hc : Continuous c := L.continuous.comp hGc
  have hc0 : c 0 = T φ := by
    show T (TestFunction.ofSupportedIn hK'V (G 0)) = T φ
    congr 1
    refine TestFunction.ext fun x => ?_
    show φ (x - MarkovWeyl2.projB 0 1 0) = φ x
    rw [MarkovWeyl2.projB_eq one_pos (by simp), sub_zero]
  have key : ∀ n : ℕ, ∫ y, φ y * T (bumpTest n y) = ∫ t, bumpTest n 0 t * c t := by
    intro n
    set ρ : ℂ → ℝ := ⇑(bumpTest n 0) with hρdef
    have hρc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := (bumpTest n 0).contDiff
    have hρS : ∀ x, 1 < ‖x‖ → ρ x = 0 := fun x hx => bumpTest_zero_eq_zero n hx.le
    obtain ⟨FA, hFA, IA, hIA, hLA⟩ := MarkovWeyl3.exists_conv_pairing_on (K' := K') hρc hρS hR
      φ.continuous (fun y x hyx => by
        have h1 : ‖y‖ ≤ R := not_lt.1 fun h => left_ne_zero_of_mul hyx (hR y h)
        have h2 : ‖x - y‖ ≤ 1 := not_lt.1 fun h => right_ne_zero_of_mul hyx (hρS _ h)
        show x ∈ closedBall (0 : ℂ) (R + 1)
        rw [mem_closedBall, dist_zero_right]
        linarith [norm_sub_norm_le x y])
    obtain ⟨FB, hFB, IB, hIB, hLB⟩ := MarkovWeyl3.exists_conv_pairing_on (K' := K') φ.contDiff
      hR hρS hρc.continuous (fun t x htx => by
        have h1 : ‖t‖ ≤ 1 := not_lt.1 fun h => left_ne_zero_of_mul htx (hρS t h)
        have h2 : ‖x - t‖ ≤ R := not_lt.1 fun h => right_ne_zero_of_mul htx (hR _ h)
        show x ∈ closedBall (0 : ℂ) (R + 1)
        rw [mem_closedBall, dist_zero_right]
        linarith [norm_sub_norm_le x t])
    have hIAB : IA = IB := ContDiffMapSupportedIn.ext fun x => by
      rw [hIA, hIB]
      have := integral_sub_left_eq_self (fun t => ρ t * φ (x - t)) (volume : Measure ℂ) x
      simp only [sub_sub_cancel] at this
      rw [← this]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    have hA : ∀ y, L (FA y) = φ y * T (bumpTest n y) := by
      intro y
      rw [← smul_eq_mul, ← map_smul]
      show T (TestFunction.ofSupportedIn hK'V (FA y)) = _
      congr 1
      refine TestFunction.ext fun x => ?_
      show FA y x = φ y * bumpTest n y x
      rw [hFA, CircleAvg.bumpTest_eq_sub n y x]
    have hB : ∀ t, L (FB t) = ρ t * c t := by
      intro t
      by_cases ht : ‖t‖ ≤ 1
      · have hp : MarkovWeyl2.projB 0 1 t = t :=
          MarkovWeyl2.projB_eq one_pos (by rw [sub_zero]; exact ht)
        have : FB t = ρ t • G t := ContDiffMapSupportedIn.ext fun x => by
          rw [hFB]
          show _ = ρ t * φ (x - MarkovWeyl2.projB 0 1 t)
          rw [hp]
        rw [this, map_smul, smul_eq_mul]
      · have h0 := hρS t (not_le.1 ht)
        have : FB t = 0 := ContDiffMapSupportedIn.ext fun x => by rw [hFB, h0, zero_mul]; rfl
        rw [this, map_zero, h0, zero_mul]
    calc ∫ y, φ y * T (bumpTest n y) = ∫ y, L (FA y) :=
          integral_congr_ae (Eventually.of_forall fun y => (hA y).symm)
      _ = L IB := by rw [← hLA, hIAB]
      _ = ∫ t, ρ t * c t := by rw [hLB]; exact integral_congr_ae (Eventually.of_forall hB)
  have hr : Tendsto (fun n : ℕ => (CircleAvg.bumpAt n 0).rOut) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hconv := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℂ))
    hr (hc.comp continuous_neg) 0
  have h0 : (c ∘ fun a => -a) 0 = c 0 := by simp
  rw [h0] at hconv
  rw [← hc0]
  refine Tendsto.congr (fun n => ?_) hconv
  rw [key n, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Function.comp_apply, zero_sub,
    neg_neg]
  rfl

/-- **Polar coordinates against a radial test function.** -/
theorem integral_mul_eq_polar {m : ℂ → ℝ} (hm : Continuous m) (φ : TestC) (z : ℂ)
    (hrad : ∀ w : ℂ, φ w = φ (z + ((‖w - z‖ : ℝ) : ℂ))) :
    ∫ y, φ y * m y =
      ∫ r in Ioi (0 : ℝ), 2 * π * r * φ (z + (r : ℂ)) * Real.circleAverage m z r := by
  obtain ⟨R, hR0⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall z
  have hR : ∀ x : ℂ, R < ‖x‖ → φ (z + x) = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR0 h; rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at this; linarith
  set f : ℂ → ℝ := fun x => φ (z + x) * m (z + x) with hf
  have hfc : Continuous f :=
    (φ.continuous.comp (continuous_const.add continuous_id)).mul
      (hm.comp (continuous_const.add continuous_id))
  have h1 : ∫ y, φ y * m y = ∫ x, f x :=
    (integral_add_left_eq_self (fun y => φ y * m y) z).symm
  rw [h1, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hcont : Continuous fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p) := by
    refine continuous_fst.smul (hfc.comp ?_)
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I)).congr
        fun p => (Complex.polarCoord_symm_apply p).symm
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hK : IsCompact (Icc (0 : ℝ) R ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
    refine (hcont.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    have hr' : R < r := by
      by_contra hle
      push Not at hle
      exact hn ⟨⟨le_of_lt hr, hle⟩, Ioo_subset_Icc_self hθ⟩
    have : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos (mem_Ioi.1 hr)]
    simp only [hf, hR _ (this ▸ hr'), zero_mul, smul_zero]
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 < r := hr
  have hpt : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    intro θ
    rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hφr : ∀ θ : ℝ, φ (z + circleMap 0 r θ) = φ (z + (r : ℂ)) := by
    intro θ
    rw [hrad, add_sub_cancel_left, circleMap_zero, norm_mul, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
  simp only [hf, hpt, hφr, smul_eq_mul]
  have hca : ∫ θ in Ioo (-π) π, m (z + circleMap 0 r θ) = 2 * π * Real.circleAverage m z r := by
    rw [Real.circleAverage_eq_integral_add (-π), smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul,
      intervalIntegral.integral_comp_add_right (fun θ => m (circleMap z r θ)),
      zero_add, show 2 * π + -π = π by ring, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only [circleMap, zero_add]
  rw [integral_const_mul, integral_const_mul, hca]
  ring

/-- **Polar formula for the mollified field**: `∫_0^∞ 2π r φ(z + r) ⟨T, σ_{z,r} * ψ_n⟩ dr → ⟨T, φ⟩`
for `φ` radial about `z`. -/
theorem tendsto_polar_circBump (T : DistC) (φ : TestC) (z : ℂ)
    (hrad : ∀ w : ℂ, φ w = φ (z + ((‖w - z‖ : ℝ) : ℂ))) :
    Tendsto (fun n : ℕ => ∫ r in Ioi (0 : ℝ),
      2 * π * r * φ (z + (r : ℂ)) * T (CircleAvg.circBump n z r)) atTop (𝓝 (T φ)) := by
  refine (tendsto_integral_mul_pair_bumpTest T φ).congr fun n => ?_
  rw [integral_mul_eq_polar (m := fun x => T (bumpTest n x))
    (T.continuous.comp (continuous_bumpTest n)) φ z hrad]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [CircleAvg.circleAverage_pairing]

end LQGMetric.DFGPS
