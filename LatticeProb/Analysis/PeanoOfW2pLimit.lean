import Mathlib
import LatticeProb.Analysis.GradientLimit
import LatticeProb.Analysis.GradientUniformCauchy
import LatticeProb.Analysis.HessianGradientBound
import LatticeProb.Analysis.LpLebesguePoints
import LatticeProb.Analysis.PeanoOfFderiv

/-! # Peano expansions of `W^{2,p}` limits

Let `uε n` be smooth approximations of `u` on an open set `U` of a finite-dimensional inner
product space `E`, converging to `u` uniformly on compact subsets of `U`, whose Hessians converge in
`L^p` on compact subsets of `U` to a measurable `G`, with `d < p < ∞` where `d` is the dimension of
`E`. Then `u` has a second-order Taylor expansion with Peano remainder at almost every point of `U`.

The proof combines the following facts, assuming the differentiability of the limit gradient at the
strong `L^p` Lebesgue points of `G` (the hypothesis of
`LatticeProb.PegdenSmart.peanoOfW2pLimit_of_hessianExpansion`).

* The gradients of the approximations converge uniformly on compact subsets of `U` to a function
  `V`, and `u` has derivative `V` on `U` (`gradientLimit_of_uniformCauchy`).
* `‖G‖ ^ p` is integrable over every compact subset `C` of `U`: for large `n` the Hessian of
  `uε n` is continuous near `C`, and its distance to `G` in `L^p(C)` is finite.
* Almost every point of `U` is a strong `L^p` Lebesgue point of `G` (`lp_lebesgue_points`).
* At a point `x` where `V` has derivative `G x`, the function `u` has a Peano expansion
  (`peano_of_fderiv`).

If `E` is a subsingleton, every function has a Peano expansion at every point.

## Main statements

* `LatticeProb.PegdenSmart.peanoAt_of_subsingleton`
* `LatticeProb.PegdenSmart.lintegral_enorm_rpow_lt_top_of_isW2pApprox`
* `LatticeProb.PegdenSmart.peanoOfW2pLimit_of_hessianExpansion`
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal

namespace LatticeProb.PegdenSmart

/-- In a subsingleton space every function has a Peano expansion at every point. -/
theorem peanoAt_of_subsingleton {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Subsingleton E] (u : E → ℝ) (x : E) : PeanoAt u x := by
  refine ⟨0, 0, IsSelfAdjoint.zero _, (isLittleO_zero _ _).congr_left fun y => ?_⟩
  rw [Subsingleton.elim y x]
  simp

/-- A bound for the `L^p` seminorm of an indicator bounds the `L^p` seminorm on the restriction. -/
private lemma eLpNorm_restrict_lt_of_indicator_lt {α F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup F] {p : ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    {f : α → F} {c : ℝ≥0∞} (h : eLpNorm (s.indicator f) p μ < c) :
    eLpNorm f p (μ.restrict s) < c := by
  rwa [eLpNorm_indicator_eq_eLpNorm_restrict hs] at h

/-- If `f` and `f - g` have finite `L^p` seminorm with `1 ≤ p`, then so does `g`. -/
private lemma eLpNorm_lt_top_of_sub_lt_top {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f g : α → F} (hf : eLpNorm f p μ < ⊤)
    (hfg : eLpNorm (fun x => f x - g x) p μ < ⊤) : eLpNorm g p μ < ⊤ := by
  have h := eLpNorm_sub_le (μ := μ) hp1 (f := f) (g := fun x => f x - g x)
  have heq : (f - fun x => f x - g x) = g := by
    funext x
    simp
  rw [heq] at h
  exact h.trans_lt (ENNReal.add_lt_top.2 ⟨hf, hfg⟩)

/-- For `W^{2,p}` approximations with `1 ≤ p < ∞`, the limit `G` of the Hessians has `‖G‖ ^ p`
integrable over every compact subset of `U`. -/
theorem lintegral_enorm_rpow_lt_top_of_isW2pApprox {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    {U : Set E} {u : E → ℝ} {uε : ℕ → E → ℝ} {ε : ℕ → ℝ} {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (h : IsW2pApprox μ p U u uε ε G) {C : Set E} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∫⁻ x in C, ‖G x‖ₑ ^ p.toReal ∂μ < ⊤ := by
  obtain ⟨hU, -, hε, hsm, -, -, hL⟩ := h
  obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
  obtain ⟨n, hεn, hn⟩ := (((tendsto_order.1 hε).2 (δ / 2) (half_pos hδ)).and
    ((tendsto_order.1 (hL C hC hCU)).2 1 zero_lt_one)).exists
  have hW : thickening (δ / 2) C ⊆ {x | closedBall x (ε n) ⊆ U} := by
    intro x hx y hy
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
    refine hδU (mem_cthickening_of_dist_le y z δ C hz ?_)
    have := dist_triangle y x z
    rw [mem_closedBall] at hy
    linarith
  have h2 : ContDiffOn ℝ 2 (uε n) (thickening (δ / 2) C) := ((hsm n).mono hW).of_le (by simp)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (uε n))) (thickening (δ / 2) C) :=
    (h2.fderiv_of_isOpen isOpen_thickening (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      isOpen_thickening le_rfl
  obtain ⟨M, hM⟩ :=
    hC.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ (uε n)))
      (hcont.mono (self_subset_thickening (half_pos hδ) C))
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hD : eLpNorm (fderiv ℝ (fderiv ℝ (uε n))) p (μ.restrict C) < ⊤ :=
    (MemLp.of_bound (measurable_fderiv ℝ _).aestronglyMeasurable M
      ((ae_restrict_iff' hC.measurableSet).2 (Eventually.of_forall hM))).eLpNorm_lt_top
  have hDG : eLpNorm (fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x) p (μ.restrict C) < ⊤ :=
    eLpNorm_restrict_lt_of_indicator_lt (F := E →L[ℝ] E →L[ℝ] ℝ) hC.measurableSet
      (hn.trans ENNReal.one_lt_top)
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (zero_lt_one.trans_le hp1).ne' hpt
    (eLpNorm_lt_top_of_sub_lt_top (F := E →L[ℝ] E →L[ℝ] ℝ) hp1 hD hDG)

/-- A `W^{2,p}` limit with `d < p < ∞` has a second-order Taylor expansion with Peano remainder at
almost every point of `U`, provided the limit gradient is differentiable with derivative `G x` at
every strong `L^p` Lebesgue point `x` of `G` in `U`. -/
theorem peanoOfW2pLimit_of_hessianExpansion
    (h8 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞), (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∃ C : ℝ≥0, ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ)
        (G : E → E →L[ℝ] E →L[ℝ] ℝ), IsW2pApprox μ p U u uε ε G → ∀ V : E → E →L[ℝ] ℝ,
        (∀ K : Set E, IsCompact K → K ⊆ U →
          TendstoUniformlyOn (fun n => fderiv ℝ (uε n)) V atTop K) →
        (∀ (x : E) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ y ∈ ball x r,
          ‖V y - V x - G x (y - x)‖ₑ ≤
            (C : ℝ≥0∞) * ENNReal.ofReal r ^ (1 - (Module.finrank ℝ E : ℝ) / p.toReal) *
              eLpNorm (fun w => G w - G x) p (μ.restrict (ball x r))) ∧
        (∀ x ∈ U, Tendsto
          (fun r => (∫⁻ y in closedBall x r, ‖G y - G x‖ₑ ^ p.toReal ∂μ) / μ (closedBall x r))
          (𝓝[>] 0) (𝓝 0) → HasFDerivAt V (G x) x)) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞),
      (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ),
      IsOpen U → (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U}) →
      (∀ C : Set E, IsCompact C → C ⊆ U → TendstoUniformlyOn uε u atTop C) →
      Measurable G →
      (∀ C : Set E, IsCompact C → C ⊆ U →
        Tendsto (fun n => eLpNorm (C.indicator fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x) p μ)
          atTop (𝓝 0)) →
      ∀ᵐ x ∂(μ.restrict U), PeanoAt u x := by
  intro E _ _ _ _ _ μ _ p hdp hpt U u uε ε G hU hε hε0 hsm hconv hG hL
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Eventually.of_forall fun x => peanoAt_of_subsingleton u x
  have hA : IsW2pApprox μ p U u uε ε G := ⟨hU, hε, hε0, hsm, hconv, hG, hL⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_trans (by exact_mod_cast Module.finrank_pos) hdp.le
  obtain ⟨V, -, hVconv, hVd⟩ := gradientLimit_of_uniformCauchy
    (gradientUniformCauchy_of_supBound gradient_sup_bound) E μ p hdp hpt U u uε ε G hA
  obtain ⟨K, hK⟩ := h8 E μ p hdp hpt
  have hdiff := (hK U u uε ε G hA V hVconv).2
  have hleb := lp_lebesgue_points E μ p.toReal (by simpa using ENNReal.toReal_mono hpt hp1)
    (E →L[ℝ] E →L[ℝ] ℝ) U G hU hG fun C hC hCU =>
      lintegral_enorm_rpow_lt_top_of_isW2pApprox hp1 hpt hA hC hCU
  filter_upwards [hleb, ae_restrict_mem hU.measurableSet] with x hx hxU
  exact (peano_of_fderiv E u V (G x) x (eventually_of_mem (hU.mem_nhds hxU) hVd)
    (hdiff x hxU hx)).2.2

end LatticeProb.PegdenSmart
