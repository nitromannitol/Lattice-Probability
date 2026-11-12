/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_12Ae at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12Loc
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# DFGPS Lemma 2.12: a.s. properties of the coupled limit `D_h`

In DFGPS Lemma 2.12 (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:1026–1031) `D_h` is the
a.s. limit (Skorokhod coupling) of `𝔞_{ε_n}⁻¹ D_h^{ε_n}`. We transfer to `D_h` the two facts the
proof (T:1039–1048) uses about it:

* `D_h` is a length metric (DFGPS Lemma 2.5, `lem2_5_lim`, for the law of `D_h`);
* the localization (eqn-square-bdy-weyl) of T:1041–1043 (`ae_agreeSetK`, from Lemma 2.10).

Both are statements about the law `μ` of `D_h`; since `D_h` is an a.s. limit of measurable maps it is
a.e.-measurable (mathlib `aemeasurable_of_tendsto_metrizable_ae'`), and a.s. convergence gives
convergence in law (mathlib `tendstoInDistribution_of_ae_tendsto`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- uniform convergence on all `B̄_R(0) × B̄_R(0)` is convergence in `C(ℂ × ℂ, ℝ)` -/
theorem tendsto_contMap_of_tendstoUniformlyOn_balls {F : ℕ → C(ℂ × ℂ, ℝ)} {G : C(ℂ × ℂ, ℝ)}
    (hF : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n p => F n p) G atTop
      (closedBall 0 R ×ˢ closedBall 0 R)) : Tendsto F atTop (𝓝 G) := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ × ℂ)
  refine (hF (max R 1) (lt_of_lt_of_le one_pos (le_max_right _ _))).mono fun p hp => ?_
  have h1 := closedBall_subset_closedBall (le_max_left R 1) (hR hp)
  rw [closedBall_prod_same]
  exact h1

/-- **DFGPS T:1026–1048, the a.s. inputs on `D_h`**: in the coupling of Lemma 2.12, a.s. `D_h` is a
length metric and satisfies the localization of T:1041–1043 for all `k, r ∈ ℕ`. -/
theorem ae_isLength_agree (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (Dh : Ω → ContMetric) (εn : ℕ → ℝ) (hh : IsGFFPlusBddCont h P) (hεp : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0))
    (hconv : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n p => (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p)
      (fun p => (Dh ω).1 p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) :
    ∀ᵐ ω ∂P, (Dh ω).IsLength ∧
      ∀ k r : ℕ, ∃ s : ℕ, (Dh ω).1 ∈ agreeSetK ((k : ℝ) + 1) ((r : ℝ) + 1) s := by
  set ξ := xiGamma γ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hε0.eventually (gt_mem_nhds one_pos))
  set ε' : ℕ → ℝ := fun n => εn (n + N)
  have hε' : ∀ n, ε' n ∈ Ioo (0 : ℝ) 1 := fun n => ⟨hεp _, hN _ (Nat.le_add_left _ _)⟩
  have hε'0 : Tendsto ε' atTop (𝓝 0) := hε0.comp (tendsto_add_atTop_nat N)
  set X : ℕ → Ω → C(ℂ × ℂ, ℝ) := fun n ω => lfppC ξ (ε' n) (h ω)
  set Z : Ω → C(ℂ × ℂ, ℝ) := fun ω => (Dh ω).1
  have hX : ∀ n, AEMeasurable (X n) P := fun n => aemeasurable_lfppC hh (hε' n).1.ne'
  have hcS : ∀ᵐ ω ∂P, ∀ n, Continuous (heatMollify (εn n) (h ω)) := ae_all_iff.2 fun n =>
    (hh.ae_tendstoLocallyUniformly_heatMollify (εn n) (hεp n).ne').mono fun ω hω => hω.2
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hconv, hcS] with ω hω hc
    have hfull : Tendsto (fun n => lfppC ξ (εn n) (h ω)) atTop (𝓝 (Z ω)) := by
      refine tendsto_contMap_of_tendstoUniformlyOn_balls fun R hR => ?_
      refine (hω R hR).congr (Eventually.of_forall fun n p _ => ?_)
      simp only [lfppC_apply_of_continuous (hc n)]
      rfl
    exact hfull.comp (tendsto_add_atTop_nat N)
  have hZ : AEMeasurable Z P := aemeasurable_of_tendsto_metrizable_ae' hX hlim
  have hD := tendstoInDistribution_of_ae_tendsto hX hZ hlim
  set ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ) := fun n => ⟨P.map (X n), inferInstance⟩
  set μ : ProbabilityMeasure C(ℂ × ℂ, ℝ) := ⟨P.map Z, inferInstance⟩
  have hνμ : Tendsto ν atTop (𝓝 μ) := hD.tendsto
  have hν : ∀ n, ε' n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppC (xiGamma γ) (ε' n) (h ω) := fun n => ⟨hε' n, rfl⟩
  have h1 := ae_of_ae_map hZ (lem2_5_lim h28 hγ hγ2 P h hh ε' ν μ hν hε'0 hνμ)
  have h2 := ae_of_ae_map hZ (ae_agreeSetK h28 hγ hγ2 P h hh ε' ν μ hν hε'0 hνμ)
  filter_upwards [h1, h2] with ω hω1 hω2
  obtain ⟨_, hl⟩ := hω1
  exact ⟨hl, hω2⟩

end LQGMetric.DFGPS
