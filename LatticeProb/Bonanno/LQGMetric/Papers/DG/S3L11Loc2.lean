/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Loc2 at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_eq_lintegral_rpow_enorm_toReal measurability side goal closed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc2
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of `μ_{ĥ^tr}` (P2-DGLOC, part 2): continuity of `z ↦ K^{tr}_{σ_{z,r}}` in `L²`

The kernel of the circle average `ĥ^tr(σ_{z,r}) = √π W(K^{tr}_{σ_{z,r}})` is the translate by `z`
of the kernel at `0` (DG:953, `scFun_trMeasKer` with `δ = 1`). Translation is continuous on
`L²(ℝ × ℂ)` (density of compactly supported continuous functions, `MemLp.exists_hasCompactSupport_
eLpNorm_sub_le`, and dominated convergence for those), so `z ↦ K^{tr}_{σ_{z,r}}` is continuous.
This gives jointly measurable versions of the circle averages of `ĥ^tr` that are measurable for
the local white noise (part 3). Own elementary glue (a standard fact).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent QuantumZipper

lemma trMeasKerScL2_one' (μ : Measure ℂ) : trMeasKerScL2 1 μ = trMeasKerL2 μ := by
  have h : trKerSc 1 = trKer := by
    funext z p; simp only [trKerSc, trKer, one_pow]
  have h2 : trMeasKerSc 1 μ = trMeasKer μ := by
    funext p; simp only [trMeasKerSc, trMeasKer, h]
  unfold trMeasKerScL2 trMeasKerL2
  rw [h2]

lemma scFun_one_eq (b : ℂ) (u : ℝ × ℂ → ℝ) : scFun 1 b u = fun p => u (p.1, p.2 - b) := by
  funext p; simp [scFun, scMap]

/-- translation is continuous on compactly supported continuous functions in `L²` -/
theorem tendsto_wnScale_one_of_cc {u : ℝ × ℂ → ℝ} (hu : Continuous u) (hc : HasCompactSupport u)
    (hm : MemLp u 2 volume) (b₀ : ℂ) :
    Tendsto (fun b => wnScale one_pos b (hm.toLp u)) (𝓝 b₀)
      (𝓝 (wnScale one_pos b₀ (hm.toLp u))) := by
  simp_rw [wnScale_toLp]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun b => scFun 1 b u) (fun b => memLp_scFun one_pos b hm)
    (scFun 1 b₀ u) (memLp_scFun one_pos b₀ hm)]
  simp_rw [scFun_one_eq]
  obtain ⟨M, hM⟩ : ∃ M, ∀ q, |u q| ≤ M := by
    obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hu
    exact ⟨M, fun q => by simpa [Real.norm_eq_abs] using hM q⟩
  set T : ℝ × ℂ → ℝ × ℂ := fun q => (q.1, q.2 + b₀)
  have hTc : Continuous T := by fun_prop
  set S : Set (ℝ × ℂ) := cthickening 1 (T '' tsupport u)
  have hS : IsCompact S := (hc.isCompact.image hTc).cthickening
  have hzero : ∀ b, dist b b₀ < 1 → ∀ p, p ∉ S → u (p.1, p.2 - b) = 0 := by
    intro b hb p hp
    by_contra h
    refine hp (mem_cthickening_of_dist_le p (T (p.1, p.2 - b)) 1 _
      (mem_image_of_mem _ (subset_tsupport _ h)) ?_)
    have hd : dist p (T (p.1, p.2 - b)) = dist b b₀ := by
      simp only [T, Prod.dist_eq, dist_self, Complex.dist_eq]
      rw [show p.2 - (p.2 - b + b₀) = b - b₀ by ring, max_eq_right (norm_nonneg _)]
    exact hd.le.trans hb.le
  set F : ℂ → ℝ × ℂ → ℝ≥0∞ := fun b p =>
    ‖u (p.1, p.2 - b) - u (p.1, p.2 - b₀)‖ₑ ^ (2 : ℝ)
  have hlin : Tendsto (fun b => ∫⁻ p, F b p) (𝓝 b₀) (𝓝 (∫⁻ _p : ℝ × ℂ, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (S.indicator fun _ => ENNReal.ofReal ((2 * M) ^ 2)) (Eventually.of_forall fun b => ?_)
      ?_ ?_ (ae_of_all _ fun p => ?_)
    · exact ((hu.comp (by fun_prop)).sub (hu.comp (by fun_prop))).measurable.enorm.pow_const _
    · filter_upwards [ball_mem_nhds b₀ one_pos] with b hb
      refine ae_of_all _ fun p => ?_
      by_cases hp : p ∈ S
      · rw [indicator_of_mem hp]
        simp only [F]
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [Real.norm_eq_abs]
        calc _ ≤ |u (p.1, p.2 - b)| + |u (p.1, p.2 - b₀)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hM _) (hM _)
          _ = 2 * M := by ring
      · simp only [F]
        rw [indicator_of_notMem hp, hzero b hb p hp, hzero b₀ (by simp) p hp]
        simp
    · rw [lintegral_indicator_const hS.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne
    · have h1 : Tendsto (fun b => u (p.1, p.2 - b) - u (p.1, p.2 - b₀)) (𝓝 b₀)
          (𝓝 (u (p.1, p.2 - b₀) - u (p.1, p.2 - b₀))) :=
        (((hu.comp (by fun_prop : Continuous fun b : ℂ => (p.1, p.2 - b))).tendsto b₀).sub
          tendsto_const_nhds)
      rw [sub_self] at h1
      have h2 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _ |>.comp
        (continuous_enorm.tendsto _ |>.comp h1)
      simpa [F, Function.comp_def] using h2
  rw [lintegral_zero] at hlin
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto _).comp hlin
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  refine h3.congr fun b => ?_
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [F, Pi.sub_apply, ENNReal.toReal_ofNat]
  exact ((hu.comp (by fun_prop)).sub (hu.comp (by fun_prop))).aestronglyMeasurable

/-- **translation is continuous on `L²(ℝ × ℂ)`** -/
theorem continuous_wnScale_one (g : WNSpace) : Continuous fun b : ℂ => wnScale one_pos b g := by
  refine continuous_of_uniform_approx_of_continuous fun V hV => ?_
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
  obtain ⟨u, huc, hgu, hu, hum⟩ := (Lp.memLp g).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_pos.2 (half_pos hε)).ne'
  refine ⟨fun b => wnScale one_pos b (hum.toLp u),
    continuous_iff_continuousAt.2 fun b => tendsto_wnScale_one_of_cc hu huc hum b, fun b => ?_⟩
  refine hεV ?_
  rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map]
  have e : g - hum.toLp u = ((Lp.memLp g).sub hum).toLp (⇑g - u) := by
    rw [MemLp.toLp_sub (Lp.memLp g) hum, Lp.toLp_coeFn g (Lp.memLp g)]
  rw [e, Lp.norm_toLp]
  exact (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le hgu).trans_lt (half_lt_self hε)

/-- the `ĥ^tr` kernel of `σ_{z,r}` is the translate of the kernel of `σ_{0,r}` (DG:953) -/
lemma trMeasKerL2_circle_eq (z : ℂ) {r : ℝ} (hr : 0 < r) :
    trMeasKerL2 (circleUnif z r) = wnScale one_pos z (trMeasKerL2 (circleUnif 0 r)) := by
  have hm := memLp_trMeasKer_circleUnif 0 hr
  have hk := scFun_trMeasKer one_pos z (circleUnif 0 r)
  rw [map_affineC_circleUnif] at hk
  have hm' := hk ▸ memLp_scFun one_pos z hm
  have hz : affineC 1 z 0 = z := by simp [affineC]
  have heq : wnScale one_pos z (trMeasKerL2 (circleUnif 0 r)) =
      trMeasKerScL2 1 (circleUnif (affineC 1 z 0) (1 * r)) := by
    simp only [trMeasKerL2, trMeasKerScL2, dite_eq_left_of_eq_true (eq_true hm),
      dite_eq_left_of_eq_true (eq_true hm')]
    rw [wnScale_toLp]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p => by rw [hk])
  rw [heq, hz, one_mul, trMeasKerScL2_one']

/-- **`z ↦ K^{tr}_{σ_{z,r}}` is continuous in `L²`** -/
theorem continuous_trMeasKerL2_circle {r : ℝ} (hr : 0 < r) :
    Continuous fun z => trMeasKerL2 (circleUnif z r) := by
  have e : (fun z => trMeasKerL2 (circleUnif z r)) =
      fun z => wnScale one_pos z (trMeasKerL2 (circleUnif 0 r)) :=
    funext fun z => trMeasKerL2_circle_eq z hr
  rw [e]
  exact continuous_wnScale_one _

end DG
end LQGMetric
