/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.AssociationSets at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittLipschitz
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Positive association of increasing events of a Gaussian vector (Pitt)

For `X : Ω → (ι → ℝ)` with Gaussian law and nonnegative covariances, and measurable upper sets
`U, V ⊆ ι → ℝ`: `P(X ∈ U) P(X ∈ V) ≤ P(X ∈ U ∩ V)`
(`LQGMetric.Pitt.measureReal_mul_le_inter`), and for finitely many upper sets
`∏ P(X ∈ Uᵢ) ≤ P(X ∈ ⋂ Uᵢ)` (`LQGMetric.Pitt.prod_measureReal_le_biInter`).

This is the case of indicator functions of L. D. Pitt, *Positively correlated normal variables
are associated*, Ann. Probab. 10 (1982) 496–499. Reduction to Lipschitz functions (own
elementary argument): for a closed upper set `U`, `y ↦ max 0 (1 - (k+1) dist(y, U))` is
monotone, Lipschitz and decreases to `1_U`; a measurable upper set is approximated from inside,
in law, by the closed upper sets `K + [0, ∞)^ι` with `K ⊆ U` compact (inner regularity).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal Pointwise

namespace LQGMetric

namespace Pitt

variable {ι : Type*} [Fintype ι]

lemma infDist_antitone_of_isUpperSet {U : Set (ι → ℝ)} (hU : IsUpperSet U) (hne : U.Nonempty) :
    Antitone (fun y => Metric.infDist y U) := by
  intro y y' hyy'
  simp only [Metric.infDist_eq_iInf]
  have : Nonempty U := hne.to_subtype
  refine le_ciInf fun u => ?_
  have hu' : (u : ι → ℝ) + (y' - y) ∈ U :=
    hU (le_add_of_nonneg_right (sub_nonneg.2 hyy')) u.2
  refine (ciInf_le ⟨0, ?_⟩ (⟨_, hu'⟩ : U)).trans_eq ?_
  · rintro _ ⟨v, rfl⟩; exact dist_nonneg
  · simp only [dist_eq_norm]
    congr 1; abel

/-- The Lipschitz approximants of `1_U`. -/
def closedApprox (U : Set (ι → ℝ)) (k : ℕ) (y : ι → ℝ) : ℝ :=
  max 0 (1 - ((k : ℝ) + 1) * Metric.infDist y U)

lemma closedApprox_monotone {U : Set (ι → ℝ)} (hU : IsUpperSet U) (hne : U.Nonempty) (k : ℕ) :
    Monotone (closedApprox U k) := fun y y' h => by
  unfold closedApprox
  have := infDist_antitone_of_isUpperSet hU hne h
  gcongr

lemma abs_closedApprox_le (U : Set (ι → ℝ)) (k : ℕ) (y : ι → ℝ) : |closedApprox U k y| ≤ 1 := by
  unfold closedApprox
  have h1 : 0 ≤ ((k : ℝ) + 1) * Metric.infDist y U :=
    mul_nonneg (by positivity) Metric.infDist_nonneg
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (by linarith)

lemma closedApprox_lipschitz (U : Set (ι → ℝ)) (k : ℕ) :
    LipschitzWith ((k : ℝ≥0) + 1) (closedApprox U k) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [Real.dist_eq]
  unfold closedApprox
  rw [max_comm (0 : ℝ), max_comm (0 : ℝ)]
  refine (abs_max_sub_max_le_abs _ _ (0 : ℝ)).trans ?_
  have hd : |Metric.infDist y U - Metric.infDist z U| ≤ dist y z := by
    have := (Metric.lipschitz_infDist_pt (s := U)).dist_le_mul y z
    rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
  rw [show (1 - ((k : ℝ) + 1) * Metric.infDist y U) - (1 - ((k : ℝ) + 1) * Metric.infDist z U)
      = ((k : ℝ) + 1) * -(Metric.infDist y U - Metric.infDist z U) by ring, abs_mul, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  push_cast
  exact mul_le_mul_of_nonneg_left hd (by positivity)

lemma tendsto_closedApprox {U : Set (ι → ℝ)} (hUc : IsClosed U) (hne : U.Nonempty)
    (y : ι → ℝ) :
    Tendsto (fun k => closedApprox U k y) atTop (𝓝 (U.indicator 1 y)) := by
  by_cases hy : y ∈ U
  · simp [closedApprox, Metric.infDist_zero_of_mem hy, hy]
  · rw [indicator_of_notMem hy]
    have hpos : 0 < Metric.infDist y U := (hUc.notMem_iff_infDist_pos hne).1 hy
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / Metric.infDist y U)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    unfold closedApprox
    have : 1 ≤ ((k : ℝ) + 1) * Metric.infDist y U := by
      rw [div_lt_iff₀ hpos] at hk₀
      have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    show 0 = max 0 _
    exact (max_eq_left (by linarith)).symm

variable [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] [DecidableEq ι] in
lemma integral_indicator_comp {X : Ω → ι → ℝ} (hX : AEMeasurable X P) {U : Set (ι → ℝ)}
    (hU : MeasurableSet U) : ∫ ω, U.indicator 1 (X ω) ∂P = (P.map X).real U := by
  rw [← integral_map hX ((measurable_one.indicator hU).aestronglyMeasurable),
    integral_indicator_one hU]

/-- **Pitt's inequality for closed increasing events.** -/
theorem measureReal_mul_le_inter_of_isClosed {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P])
    {U V : Set (ι → ℝ)} (hUc : IsClosed U) (hVc : IsClosed V) (hU : IsUpperSet U)
    (hV : IsUpperSet V) :
    (P.map X).real U * (P.map X).real V ≤ (P.map X).real (U ∩ V) := by
  have := hX.isProbabilityMeasure
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · simp
  rcases V.eq_empty_or_nonempty with rfl | hVne
  · simp
  have hmeas := hX.aemeasurable
  have hn : ∀ k, (∫ ω, closedApprox U k (X ω) ∂P) * (∫ ω, closedApprox V k (X ω) ∂P) ≤
      ∫ ω, closedApprox U k (X ω) * closedApprox V k (X ω) ∂P := fun k =>
    integral_mul_le_of_lipschitz hX hcov (closedApprox_monotone hU hUne k)
      (closedApprox_monotone hV hVne k) (abs_closedApprox_le U k) (abs_closedApprox_le V k)
      (closedApprox_lipschitz U k) (closedApprox_lipschitz V k)
  have hF := tendsto_integral_comp_of_bdd hmeas
    (fun k => (closedApprox_lipschitz U k).continuous.measurable)
    (abs_closedApprox_le U) (tendsto_closedApprox hUc hUne)
  have hG := tendsto_integral_comp_of_bdd hmeas
    (fun k => (closedApprox_lipschitz V k).continuous.measurable)
    (abs_closedApprox_le V) (tendsto_closedApprox hVc hVne)
  have hFG := tendsto_integral_comp_of_bdd hmeas
    (h := fun k y => closedApprox U k y * closedApprox V k y)
    (h₀ := fun y => U.indicator 1 y * V.indicator 1 y) (C := 1 * 1)
    (fun k => ((closedApprox_lipschitz U k).continuous.mul
      (closedApprox_lipschitz V k).continuous).measurable)
    (fun k y => by
      rw [abs_mul]
      exact mul_le_mul (abs_closedApprox_le U k y) (abs_closedApprox_le V k y) (abs_nonneg _)
        zero_le_one)
    (fun y => (tendsto_closedApprox hUc hUne y).mul (tendsto_closedApprox hVc hVne y))
  have hlim := le_of_tendsto_of_tendsto' (hF.mul hG) hFG hn
  have hprod : ∀ y, U.indicator (1 : (ι → ℝ) → ℝ) y * V.indicator 1 y =
      (U ∩ V).indicator 1 y := fun y => by
    rw [inter_indicator_one]; rfl
  simp only [hprod] at hlim
  rw [integral_indicator_comp hmeas hUc.measurableSet,
    integral_indicator_comp hmeas hVc.measurableSet,
    integral_indicator_comp hmeas (hUc.inter hVc).measurableSet] at hlim
  exact hlim

end Pitt

end LQGMetric
