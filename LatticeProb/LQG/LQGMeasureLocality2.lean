import Mathlib
import LatticeProb.Gauss.CircleAverageApprox2
import LatticeProb.LQG.LQGMeasureLocality
import LatticeProb.LQG.LQGMeasureSquare

/-!
# The circle-average link from the whole-plane GFF, and unconditional locality of the LQG measure

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Fact 2.1 II. The circle-average chain is imported from the modules `LatticeProb.Gauss.CircleAverageApprox` and
`LatticeProb.Gauss.CircleAverageApprox2`.

* `LatticeProb.Gauss.IsWholePlaneGFF.wholePlaneCircleAverageLimit`: the whole-plane circle-average limit.
  Unit-mass test functions supported in an arbitrary open `O ⊇ sphere z r` whose pairings converge almost surely to the
  circle average. The test functions are the annular densities `unitCircleDensity r (r η₀ (1/2)^j)` with
  `η₀ ≤ min (r/4) (δ₀/2)`, `δ₀` a thickening radius of the sphere inside `O`. The only new ingredient with respect to
  `ae_tendsto_circleApprox` (module `LatticeProb.Gauss.CircleAverageApprox2`) is the width `η₀`, which keeps the annuli inside `O`.
* `LatticeProb.LQG.lqgCircleAverageLink_of_gff`: `LQGCircleAverageLink` under the whole-plane GFF premise.
* `LatticeProb.LQG.lqgLocality_of_gff`: locality of the LQG area measure (Fact 2.1 II), with no circle-average link
  hypothesis.
* `LatticeProb.LQG.aemeasurable_lqgMeasure_closedDyadicSquare_of_gff`: the measurability statement for closed dyadic
  squares, with no locality hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

/-- The annulus `{x | | |x - z| - r | ≤ η}` lies in the `δ`-thickening of the circle `sphere z r` when `η < r` and
`η < δ` (the distance from `x` to the circle is `| |x - z| - r |`; the nearest point is `z + (r/|x-z|)(x-z)`). -/
theorem annulus_subset_thickening_sphere {r δ η : ℝ} (hr : 0 < r) (z : ℂ) (hηr : η < r) (hηδ : η < δ) :
    {x : ℂ | |‖x - z‖ - r| ≤ η} ⊆ thickening δ (sphere z r) := by
  intro x hx
  change |‖x - z‖ - r| ≤ η at hx
  by_cases hxz : x = z
  · subst hxz
    rw [sub_self, norm_zero, zero_sub, abs_neg, abs_of_pos hr] at hx
    linarith
  · have hn : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    set n := ‖x - z‖ with hn_def
    have hn0 : n ≠ 0 := hn.ne'
    refine mem_thickening_iff.mpr ⟨z + (r / n) • (x - z), ?_, ?_⟩
    · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr hn), ← hn_def, div_mul_cancel₀ _ hn0]
    · rw [dist_eq_norm]
      have key : x - (z + (r / n) • (x - z)) = (1 - r / n) • (x - z) := by
        rw [sub_smul, one_smul]
        abel
      have h2 : |1 - r / n| * n = |n - r| := by
        rw [show 1 - r / n = (n - r) / n by field_simp, abs_div, abs_of_pos hn,
          div_mul_cancel₀ _ hn0]
      rw [key, norm_smul, Real.norm_eq_abs, ← hn_def, h2]
      linarith

/-- Annular density of the circle `(r, z)` at the geometric widths `η₀ (1/2)^j`: the `unitCircleDensity`
with annulus width `r η₀ (1/2)^j`. -/
noncomputable def circleApproxW {r : ℝ} (hr : 0 < r) {η₀ : ℝ} (hη₀ : 0 < η₀) (z : ℂ) (j : ℕ) : ℂ → ℝ :=
  unitCircleDensity r (r * (η₀ * (1 / 2) ^ j)) (mul_pos hr (mul_pos hη₀ (by positivity))) z

theorem isTestFunction_circleApproxW {O : Set ℂ} {r : ℝ} (hr : 0 < r) {η₀ : ℝ} (hη₀ : 0 < η₀) (z : ℂ) (j : ℕ)
    (hO : {x : ℂ | |‖x - z‖ - r| ≤ η₀ * (1 / 2) ^ j} ⊆ O) :
    IsTestFunction O (circleApproxW hr hη₀ z j) :=
  isTestFunction_unitCircleDensity z hr (mul_pos hη₀ (by positivity)) hO

theorem integral_circleApproxW {r : ℝ} (hr : 0 < r) {η₀ : ℝ} (hη₀ : 0 < η₀) (z : ℂ) (j : ℕ) :
    ∫ x, circleApproxW hr hη₀ z j x = 1 :=
  integral_unitCircleDensity hr.le (mul_pos hr (mul_pos hη₀ (by positivity))) z

/-- **A.s. convergence of the width-`η₀ (1/2)^j` annular approximants** (the argument of `ae_tendsto_circleApprox`,
with the width `η₀ (1/2)^j` in place of `(r/4)(1/2)^j`; the bound `η₀ ≤ r/4` keeps the second moment `≤ 8 (r/4)/r (1/2)^j`). -/
theorem ae_tendsto_circleApproxW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r η₀ : ℝ} (hr : 0 < r) (hη₀ : 0 < η₀) (hη₀r : η₀ ≤ r / 4) (z : ℂ) :
    ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (circleApproxW hr hη₀ z j)) atTop (𝓝 (hcirc ω r z)) := by
  have huniv : ∀ j, IsTestFunction univ (circleApproxW hr hη₀ z j) :=
    fun j => isTestFunction_circleApproxW hr hη₀ z j (subset_univ _)
  have hD : ∀ j, MemLp (fun ω => hC ω (circleApproxW hr hη₀ z j) - hcirc ω r z) 2 P := by
    intro j
    have hp : MemLp (fun ω => hC ω (circleApproxW hr hη₀ z j)) 2 P :=
      (hGFF.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing _, huniv j⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
    exact hp.sub hz
  have hbound : ∀ j, ∫ ω, (hC ω (circleApproxW hr hη₀ z j) - hcirc ω r z) ^ 2 ∂P ≤
      8 * (r / 4) / r * (1 / 2) ^ j := by
    intro j
    rw [integral_sq_pairing_sub_circle_eq_variance hGFF hr z _ (huniv j),
      variance_pairing_sub_circle_eq hGFF hr z _ (huniv j)]
    have hpow : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hwle : η₀ * (1 / 2) ^ j ≤ r / 2 := by
      have := mul_le_of_le_one_right hη₀.le hpow
      linarith
    have hwpos : 0 < η₀ * (1 / 2) ^ j := mul_pos hη₀ (by positivity)
    have hc := abs_unitCircleDensity_covariance_combination (r := r) (δ := r * (η₀ * (1 / 2) ^ j))
      (η := η₀ * (1 / 2) ^ j) hr (mul_pos hr hwpos) (by linarith) le_rfl z
    have hl := log_add_sub_log_sub_le_four_mul hr hwpos hwle
    refine le_trans (le_abs_self _) (le_trans hc ?_)
    have hscale : 2 * (4 * (η₀ * (1 / 2) ^ j) / r) ≤ 8 * (r / 4) / r * (1 / 2) ^ j := by
      have h1 : η₀ * (1 / 2) ^ j ≤ (r / 4) * (1 / 2) ^ j :=
        mul_le_mul_of_nonneg_right hη₀r (by positivity)
      have h2 : 2 * (4 * ((r / 4) * (1 / 2) ^ j) / r) = 8 * (r / 4) / r * (1 / 2) ^ j := by
        field_simp
        ring
      have h3 : 4 * (η₀ * (1 / 2) ^ j) / r ≤ 4 * ((r / 4) * (1 / 2) ^ j) / r := by
        apply div_le_div_of_nonneg_right _ hr.le
        linarith
      linarith
    linarith
  have hsum : Summable (fun j : ℕ => 8 * (r / 4) / r * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  filter_upwards [ae_tendsto_zero_of_summable_integral_sq
    (fun j ω => hC ω (circleApproxW hr hη₀ z j) - hcirc ω r z) hD _ hsum hbound] with ω hω
  exact tendsto_sub_nhds_zero_iff.mp hω

/-- **The whole-plane circle-average limit.** For an open `O` containing the circle `sphere z r`, there are unit-mass test functions supported in `O` whose pairings
converge almost surely to the circle average `hcirc ω r z`. -/
theorem IsWholePlaneGFF.wholePlaneCircleAverageLimit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (O : Set ℂ) (hO : IsOpen O) {r : ℝ} (hr : 0 < r) (z : ℂ) (hsph : sphere z r ⊆ O) :
    ∃ ψ : ℕ → ℂ → ℝ, (∀ j, IsTestFunction O (ψ j) ∧ ∫ x, ψ j x = 1) ∧
      ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω r z)) := by
  obtain ⟨δ₀, hδ₀, hthick⟩ := (isCompact_sphere z r).exists_thickening_subset_open hO hsph
  obtain ⟨η₀, hη₀, hη₀r, hη₀δ⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ r / 4 ∧ η₀ ≤ δ₀ / 2 :=
    ⟨min (r / 4) (δ₀ / 2), lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hsub : ∀ j : ℕ, {x : ℂ | |‖x - z‖ - r| ≤ η₀ * (1 / 2) ^ j} ⊆ O := by
    intro j
    have hpow : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hwle : η₀ * (1 / 2) ^ j ≤ η₀ := mul_le_of_le_one_right hη₀.le hpow
    have hηr : η₀ * (1 / 2) ^ j < r := by linarith
    have hηδ : η₀ * (1 / 2) ^ j < δ₀ := by linarith
    exact (annulus_subset_thickening_sphere (δ := δ₀) (η := η₀ * (1 / 2) ^ j) hr z hηr hηδ).trans hthick
  exact ⟨circleApproxW hr hη₀ z, fun j =>
    ⟨isTestFunction_circleApproxW hr hη₀ z j (hsub j), integral_circleApproxW hr hη₀ z j⟩,
    ae_tendsto_circleApproxW hGFF hr hη₀ hη₀r z⟩

end LatticeProb.Gauss

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- **Circle-average link under the whole-plane GFF premise.** For an open `U` and a closed ball `closedBall z r ⊆ U`,
the circle average `fieldCircleAverage α₀ (hcirc ω) r z` is a.s. equal to a `σ(h|_U)`-measurable function. Route: the
test functions `ψ j` of `wholePlaneCircleAverageLimit` are supported in `U`, so `ω ↦ hC ω (ψ j)` is `σ(h|_U)`-measurable
(`measurable_gff_pairing`); their limit is measurable (`StronglyMeasurable.limUnder`) and equals the circle average up
to the deterministic shift `α₀ ∫ log‖·‖` a.s. -/
theorem lqgCircleAverageLink_of_gff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    LQGCircleAverageLink P α₀ hC hcirc := by
  intro U hU r z hr hsub
  have := hGFF.isProbabilityMeasure
  obtain ⟨ψ, hψ, hconv⟩ := hGFF.wholePlaneCircleAverageLimit U hU hr z
    (Metric.sphere_subset_closedBall.trans hsub)
  refine ⟨fun ω => limUnder atTop (fun j => hC ω (ψ j)) -
    α₀ * Real.circleAverage (fun x => Real.log ‖x‖) z r, ?_, ?_⟩
  · have hm : ∀ j, @Measurable Ω ℝ (fieldSigmaAlgebra α₀ hC U) _ (fun ω => hC ω (ψ j)) :=
      fun j => measurable_gff_pairing α₀ hC U (ψ j) (hψ j).1
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    exact ((StronglyMeasurable.limUnder (l := atTop)
      (fun j => (hm j).stronglyMeasurable)).measurable).sub_const _
  · filter_upwards [hconv] with ω hω
    simp only [fieldCircleAverage]
    rw [hω.limUnder_eq]

/-- **Locality of the LQG area measure, unconditional (Fact 2.1 II).** Same statement as
`lqgLocality_of_circleLink` with the circle-average link discharged by `lqgCircleAverageLink_of_gff`. -/
theorem lqgLocality_of_gff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGLocality P γ α₀ hC hcirc :=
  lqgLocality_of_circleLink P γ α₀ hC hcirc (fun hGFF => lqgCircleAverageLink_of_gff P α₀ hC hcirc hGFF)

/-- **Square measurability, unconditional.** `aemeasurable_lqgMeasure_closedDyadicSquare` with the locality
hypothesis discharged by `lqgLocality_of_gff`. -/
theorem aemeasurable_lqgMeasure_closedDyadicSquare_of_gff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {S : Set ℂ} (hS : LatticeProb.Topology.IsClosedDyadicSquare S) :
    AEMeasurable (fun ω => μ ω S) P :=
  aemeasurable_lqgMeasure_closedDyadicSquare hγ hγ2 hα hGFF hμ (lqgLocality_of_gff P γ α₀ hC hcirc) hS

end LatticeProb.LQG
