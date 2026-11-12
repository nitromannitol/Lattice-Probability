import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Weak convergence and integrals of bounded almost-everywhere continuous functions

If probability measures `μᵢ` converge weakly to `ν` along a countably generated filter, and
`g` is a bounded Borel function that is continuous `ν`-almost everywhere, then
`∫ g dμᵢ → ∫ g dν` (Billingsley, *Convergence of Probability Measures*, Theorem 2.7, the
continuous mapping theorem for functions with a `ν`-null set of discontinuities).

The proof writes the integral of `g ≥ 0` by the layer cake formula as `∫₀^M μ{g ≥ t} dt`; the
frontier of `{g ≥ t}` lies in the discontinuity set of `g` together with the level set `{g = t}`,
which is `ν`-null for all but countably many `t`, so the integrands converge for almost every `t`
by the portmanteau theorem and dominated convergence applies.

* `LatticeProb.frontier_setOf_le_subset`: the frontier of `{t ≤ g}`.
* `LatticeProb.tendsto_integral_of_ae_continuousAt`: the theorem.
-/

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace LatticeProb

variable {E : Type*} [TopologicalSpace E]

/-- The frontier of the superlevel set `{x | t ≤ g x}` lies in the set of discontinuity points of
`g` together with the level set `{g = t}`. -/
theorem frontier_setOf_le_subset (g : E → ℝ) (t : ℝ) :
    frontier {x | t ≤ g x} ⊆ {x | ¬ ContinuousAt g x} ∪ {x | g x = t} := by
  intro x hx
  by_contra hxn
  have hcont : ContinuousAt g x := not_not.1 fun h => hxn (Or.inl h)
  have hne : g x ≠ t := fun h => hxn (Or.inr h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hU : {y | g y < t} ∈ 𝓝 x := hcont.eventually (gt_mem_nhds hlt)
    have hcl : x ∈ closure {x | t ≤ g x} := hx.1
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hcl _ hU
    exact absurd (show t ≤ g y from hy2) (not_le.2 hy1)
  · have hU : {y | t < g y} ∈ 𝓝 x := hcont.eventually (lt_mem_nhds hgt)
    exact hx.2 (mem_interior_iff_mem_nhds.2 (mem_of_superset hU fun y hy => show t ≤ g y from (show t < g y from hy).le))

variable [MeasurableSpace E] [PseudoMetrizableSpace E] [BorelSpace E]
  {I : Type*} {l : Filter I} [l.IsCountablyGenerated]

/-- The nonnegative case of `tendsto_integral_of_ae_continuousAt`. -/
theorem tendsto_integral_of_ae_continuousAt_of_nonneg {mu : I → ProbabilityMeasure E}
    {nu : ProbabilityMeasure E} (h : Tendsto mu l (𝓝 nu)) {g : E → ℝ} (hg : Measurable g)
    {M : ℝ} (h0 : ∀ x, 0 ≤ g x) (hM : ∀ x, g x ≤ M)
    (hc : ∀ᵐ x ∂(nu : Measure E), ContinuousAt g x) :
    Tendsto (fun i => ∫ x, g x ∂(mu i : Measure E)) l (𝓝 (∫ x, g x ∂(nu : Measure E))) := by
  have hI : ∀ p : Measure E, IsProbabilityMeasure p →
      ∫ x, g x ∂p = ∫ t in Ioc 0 M, p.real {a | t ≤ g a} := fun p _ =>
    (Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hM x)).integral_eq_integral_Ioc_meas_le
      (ae_of_all _ h0) (ae_of_all _ hM)
  have hfun : (fun i => ∫ x, g x ∂(mu i : Measure E)) =
      fun i => ∫ t in Ioc 0 M, (mu i : Measure E).real {a | t ≤ g a} :=
    funext fun i => hI _ inferInstance
  rw [hfun, hI _ inferInstance]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun i => ?_
    refine (Antitone.measurable fun s t hst => ?_).aestronglyMeasurable
    exact measureReal_mono (fun a ha => hst.trans ha)
  · refine Eventually.of_forall fun i => Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  · exact integrable_const _
  · have hcount : {t : ℝ | 0 < (nu : Measure E) {a | g a = t}}.Countable :=
      Measure.countable_meas_level_set_pos hg
    have hae : ∀ᵐ t : ℝ, (nu : Measure E) {a | g a = t} = 0 := by
      have := hcount.measure_zero (volume : Measure ℝ)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with t ht
      simpa using ht
    refine ae_restrict_of_ae ?_
    filter_upwards [hae] with t ht
    have hfr : (nu : Measure E) (frontier {a | t ≤ g a}) = 0 :=
      measure_mono_null (frontier_setOf_le_subset g t)
        (measure_union_null (ae_iff.1 hc) ht)
    have := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hfr
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this

/-- **Integrals of bounded almost-everywhere continuous functions converge under weak
convergence.** If `μᵢ → ν` weakly along a countably generated filter and `g` is a bounded Borel
function that is continuous `ν`-almost everywhere, then `∫ g dμᵢ → ∫ g dν`. -/
theorem tendsto_integral_of_ae_continuousAt {mu : I → ProbabilityMeasure E}
    {nu : ProbabilityMeasure E} (h : Tendsto mu l (𝓝 nu)) {g : E → ℝ} (hg : Measurable g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) (hc : ∀ᵐ x ∂(nu : Measure E), ContinuousAt g x) :
    Tendsto (fun i => ∫ x, g x ∂(mu i : Measure E)) l (𝓝 (∫ x, g x ∂(nu : Measure E))) := by
  obtain ⟨C, hC⟩ := hb
  have hint : ∀ p : Measure E, IsProbabilityMeasure p → Integrable g p := fun p _ =>
    Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have key : ∀ p : Measure E, IsProbabilityMeasure p →
      ∫ x, (g x + C) ∂p = ∫ x, g x ∂p + C := fun p hp => by
    rw [integral_add (hint p hp) (integrable_const C), integral_const]
    simp
  have h1 := tendsto_integral_of_ae_continuousAt_of_nonneg h (g := fun x => g x + C)
    (hg.add_const C) (M := 2 * C) (fun x => by linarith [(abs_le.1 (hC x)).1])
    (fun x => by linarith [(abs_le.1 (hC x)).2])
    (hc.mono fun x hx => hx.add_const C)
  have h2 := h1.sub_const C
  simp only [key _ inferInstance, add_sub_cancel_right] at h2
  exact h2

end LatticeProb
