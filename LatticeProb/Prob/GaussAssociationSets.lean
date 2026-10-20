/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/AssociationSets.lean.
-/
import LatticeProb.Prob.GaussPittLipschitz
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Lipschitz approximation of indicators of closed upper sets

For an upper set `U ⊆ ι → ℝ` (`IsUpperSet U`) with `ι` finite, the distance `y ↦ infDist y U` is
antitone (`infDist_antitone_of_isUpperSet`). For a nonempty closed upper set `U`, the functions
`closedApprox U k y = max 0 (1 - (k + 1) * infDist y U)` are monotone, bounded by `1` in absolute
value, `(k + 1)`-Lipschitz, and converge pointwise to the indicator `1_U` as `k → ∞`
(`tendsto_closedApprox`). Finally, the integral of `1_U ∘ X` is the probability of `X ∈ U`
(`integral_indicator_comp`).

The product inequality for closed upper events, `measureReal_mul_le_inter_of_isClosed`, is proved
at the end of the file from the Lipschitz product inequality `integral_mul_le_of_lipschitz`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace LatticeProb

namespace Pitt

variable {ι : Type*} [Fintype ι]

/-- For a nonempty upper set `U`, the distance `y ↦ infDist y U` is antitone: moving a point up in
the coordinatewise order does not increase its distance to `U`. -/
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

/-- The Lipschitz approximants `max 0 (1 - (k + 1) * infDist y U)` of the indicator of `U`.
For a nonempty closed `U` they converge pointwise to `1_U` (`tendsto_closedApprox`). -/
def closedApprox (U : Set (ι → ℝ)) (k : ℕ) (y : ι → ℝ) : ℝ :=
  max 0 (1 - ((k : ℝ) + 1) * Metric.infDist y U)

/-- For a nonempty upper set `U`, each approximant `closedApprox U k` is monotone. -/
lemma closedApprox_monotone {U : Set (ι → ℝ)} (hU : IsUpperSet U) (hne : U.Nonempty) (k : ℕ) :
    Monotone (closedApprox U k) := fun y y' h => by
  unfold closedApprox
  have := infDist_antitone_of_isUpperSet hU hne h
  gcongr

/-- Each approximant `closedApprox U k` is bounded by `1` in absolute value. -/
lemma abs_closedApprox_le (U : Set (ι → ℝ)) (k : ℕ) (y : ι → ℝ) : |closedApprox U k y| ≤ 1 := by
  unfold closedApprox
  have h1 : 0 ≤ ((k : ℝ) + 1) * Metric.infDist y U :=
    mul_nonneg (by positivity) Metric.infDist_nonneg
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (by linarith)

/-- Each approximant `closedApprox U k` is `(k + 1)`-Lipschitz. -/
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

/-- For a nonempty closed set `U`, the approximants `closedApprox U k y` converge as `k → ∞` to
the indicator `1_U y`, at every point `y`. -/
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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] in
/-- For a measurable set `U`, the integral of `1_U ∘ X` is the probability that `X` lies in `U`. -/
lemma integral_indicator_comp {X : Ω → ι → ℝ} (hX : AEMeasurable X P) {U : Set (ι → ℝ)}
    (hU : MeasurableSet U) : ∫ ω, U.indicator 1 (X ω) ∂P = (P.map X).real U := by
  rw [← integral_map hX ((measurable_one.indicator hU).aestronglyMeasurable),
    integral_indicator_one hU]

/-! ### Nonvacuity: the hypotheses of the lemmas above are satisfied by a closed upper half-line. -/

namespace Example

example : Antitone (fun y : Fin 1 → ℝ => Metric.infDist y {z | 0 ≤ z 0}) :=
  infDist_antitone_of_isUpperSet (U := {z : Fin 1 → ℝ | 0 ≤ z 0})
    (fun _ _ hab ha => le_trans ha (hab 0)) ⟨0, by simp⟩

example (y : Fin 1 → ℝ) :
    Tendsto (fun k => closedApprox {z : Fin 1 → ℝ | 0 ≤ z 0} k y) atTop
      (𝓝 (({z : Fin 1 → ℝ | 0 ≤ z 0}).indicator 1 y)) :=
  tendsto_closedApprox (isClosed_Ici.preimage (continuous_apply 0)) ⟨0, by simp⟩ y

end Example

variable [DecidableEq ι]

/-- **Pitt's inequality for closed upper sets.** For a Gaussian vector `X` with nonnegative
covariances and closed upper sets `U` and `V` of `ι → ℝ`,
`P(X ∈ U) * P(X ∈ V) ≤ P(X ∈ U ∩ V)`. -/
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

/-! ### Nonvacuity: the hypotheses of `measureReal_mul_le_inter_of_isClosed` are satisfied by the
Gaussian vector on `ℝ` whose coordinates all equal the standard Gaussian variable, with `U = V`
the closed upper half-line. -/

namespace ClosedExample

example :
    ((stdGaussian ℝ).map (fun ω : ℝ => fun _ : Fin 1 => ω)).real {z : Fin 1 → ℝ | 0 ≤ z 0} *
      ((stdGaussian ℝ).map (fun ω : ℝ => fun _ : Fin 1 => ω)).real {z : Fin 1 → ℝ | 0 ≤ z 0} ≤
    ((stdGaussian ℝ).map (fun ω : ℝ => fun _ : Fin 1 => ω)).real
      ({z : Fin 1 → ℝ | 0 ≤ z 0} ∩ {z : Fin 1 → ℝ | 0 ≤ z 0}) := by
  have hX : HasGaussianLaw (fun ω : ℝ => fun _ : Fin 1 => ω) (stdGaussian ℝ) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian ℝ)).map_fun
      (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
  have hcov : ∀ _ _ : Fin 1, 0 ≤ cov[fun ω : ℝ => ω, fun ω : ℝ => ω; stdGaussian ℝ] :=
    fun _ _ => by
      rw [covariance_self measurable_id'.aemeasurable]
      exact variance_nonneg _ _
  have hc : IsClosed {z : Fin 1 → ℝ | 0 ≤ z 0} := isClosed_Ici.preimage (continuous_apply 0)
  have hup : IsUpperSet {z : Fin 1 → ℝ | 0 ≤ z 0} := fun _ _ hab ha => le_trans ha (hab 0)
  exact measureReal_mul_le_inter_of_isClosed hX hcov hc hc hup hup

end ClosedExample

end Pitt

end LatticeProb
