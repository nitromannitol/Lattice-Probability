import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Metrizable.ContinuousMap
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-!
# The open-set half of the portmanteau theorem, without measurability of the random elements

Let `Q` be a probability measure on `Ω`, `Y i : Ω → X` a family of maps into a topological space
`X` in which closed sets have continuous outer approximations (e.g. a pseudo-metrizable space), and
`μ` a Borel probability measure on `X`. Suppose that `∫ G (Y i ω) ∂Q → ∫ G ∂μ` along a filter `L`
for every bounded continuous `G : X → ℝ`. Then for every open `U ⊆ X`,
`μ U ≤ liminf_L Q {ω | Y i ω ∈ U}` (outer measure on the right).

No measurability of the maps `Y i` is assumed: a bounded continuous minorant of the indicator of
`U` is integrated against `Q` through a measurable hull of `{Y i ∈ U}` (if `G ∘ Y i` is not
integrable its Bochner integral vanishes). This is the form of the portmanteau theorem used to
transfer open path events from a Brownian limit to a random walk (Billingsley, *Convergence of
Probability Measures*, Theorem 2.1; Gwynne, Miller and Sheffield, *An invariance principle for
ergodic scale-free random environments*, arXiv 1807.07515, proof of Lemma 3.14).

## Main statements

* `LatticeProb.Portmanteau.le_liminf_measure_setOf_mem_of_isOpen`: the general statement.
* `LatticeProb.Portmanteau.le_liminf_measure_setOf_mem_of_convergesWeaklyInC`: the case of weak
  convergence in `C([0,∞), ℝ²)` towards a Brownian law, as in Theorem 1.16 of
  Gwynne, Miller and Sheffield.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace LatticeProb.Portmanteau

variable {X Ω ι : Type*} [MeasurableSpace Ω]

/-- A function bounded by `1` with values in `[0, 1]` and vanishing off `U` integrates to at most
the outer measure of `{ω | Y ω ∈ U}`, without any measurability of `Y`. -/
theorem integral_comp_le_toReal_measure_setOf_mem (Q : Measure Ω) [IsFiniteMeasure Q]
    (Y : Ω → X) (G : X → ℝ) (hG0 : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1)
    {U : Set X} (hGU : ∀ x, x ∉ U → G x = 0) :
    ∫ ω, G (Y ω) ∂Q ≤ (Q {ω | Y ω ∈ U}).toReal := by
  set T := toMeasurable Q {ω | Y ω ∈ U}
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hle : ∀ ω, G (Y ω) ≤ T.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : Y ω ∈ U
    · rw [indicator_of_mem (subset_toMeasurable Q _ hω)]
      exact hG1 _
    · rw [hGU _ hω]
      exact indicator_nonneg (fun _ _ => zero_le_one) ω
  calc ∫ ω, G (Y ω) ∂Q ≤ ∫ ω, T.indicator (fun _ => (1 : ℝ)) ω ∂Q :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => hG0 _)
          ((integrable_const (1 : ℝ)).indicator hT) (Eventually.of_forall hle)
    _ = (Q {ω | Y ω ∈ U}).toReal := by
        rw [integral_indicator hT, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
          measure_toMeasurable]

variable [TopologicalSpace X] [MeasurableSpace X] [HasOuterApproxClosed X] [OpensMeasurableSpace X]

/-- **Portmanteau, open sets.** If `∫ G (Y i ω) ∂Q → ∫ G ∂μ` along `L` for every bounded
continuous `G : X → ℝ`, then `μ U ≤ liminf_L Q {ω | Y i ω ∈ U}` for every open `U`. -/
theorem le_liminf_measure_setOf_mem_of_isOpen {L : Filter ι} (Q : Measure Ω)
    [IsProbabilityMeasure Q] (Y : ι → Ω → X) (μ : Measure X) [IsProbabilityMeasure μ]
    (h : ∀ G : X → ℝ, Continuous G → (∃ C, ∀ x, |G x| ≤ C) →
      Tendsto (fun i => ∫ ω, G (Y i ω) ∂Q) L (𝓝 (∫ x, G x ∂μ)))
    {U : Set X} (hU : IsOpen U) :
    μ U ≤ L.liminf (fun i => Q {ω | Y i ω ∈ U}) := by
  have hF : IsClosed Uᶜ := hU.isClosed_compl
  set g := hF.apprSeq
  set G : ℕ → X → ℝ := fun n x => 1 - (g n x : ℝ) with hGdef
  have hg1 : ∀ n x, (g n x : ℝ) ≤ 1 := fun n x => by
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
  have hG0 : ∀ n x, 0 ≤ G n x := fun n x => sub_nonneg.2 (hg1 n x)
  have hG1 : ∀ n x, G n x ≤ 1 := fun n x => sub_le_self _ (NNReal.coe_nonneg _)
  have hGU : ∀ n x, x ∉ U → G n x = 0 := fun n x hx => by
    have h1 : g n x = 1 := HasOuterApproxClosed.apprSeq_apply_eq_one hF n (show x ∈ Uᶜ from hx)
    simp [hGdef, h1]
  have hGc : ∀ n, Continuous (G n) := fun n =>
    continuous_const.sub (NNReal.continuous_coe.comp (g n).continuous)
  have hGb : ∀ n, ∃ C, ∀ x, |G n x| ≤ C := fun n =>
    ⟨1, fun x => abs_le.2 ⟨by linarith [hG0 n x], hG1 n x⟩⟩
  -- each approximant gives a lower bound for the liminf
  have hstep : ∀ n, ENNReal.ofReal (∫ x, G n x ∂μ) ≤ L.liminf (fun i => Q {ω | Y i ω ∈ U}) := by
    intro n
    have ht := ENNReal.tendsto_ofReal (h (G n) (hGc n) (hGb n))
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [ht.eventually (lt_mem_nhds hb)] with i hi
    refine hi.le.trans ?_
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact integral_comp_le_toReal_measure_setOf_mem Q (Y i) (G n) (hG0 n) (hG1 n) (hGU n)
  -- the approximants integrate to `μ U` in the limit
  have hgm : ∀ n, Measurable fun x => (g n x : ℝ) :=
    fun n => (NNReal.continuous_coe.comp (g n).continuous).measurable
  have hint : ∀ n, ∫ x, G n x ∂μ = 1 - (∫⁻ x, (g n x : ℝ≥0∞) ∂μ).toReal := by
    intro n
    have hgi : Integrable (fun x => (g n x : ℝ)) μ :=
      Integrable.of_bound (hgm n).aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]; exact hg1 n x)
    rw [hGdef, integral_sub (integrable_const 1) hgi, integral_const, probReal_univ, one_smul,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => NNReal.coe_nonneg (g n x))
        (hgm n).aestronglyMeasurable]
    simp only [ENNReal.ofReal_coe_nnreal]
  have hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (μ U).toReal) := by
    have h1 := HasOuterApproxClosed.tendsto_lintegral_apprSeq hF μ
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top μ Uᶜ)).comp h1
    have h3 := h2.const_sub (1 : ℝ)
    simp only [Function.comp_def] at h3
    rw [show (μ U).toReal = 1 - (μ Uᶜ).toReal by
      rw [prob_compl_eq_one_sub hU.measurableSet,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]; ring]
    simpa only [hint] using h3
  have hlim' := ENNReal.tendsto_ofReal hlim
  rw [ENNReal.ofReal_toReal (measure_ne_top μ U)] at hlim'
  exact le_of_tendsto hlim' (Eventually.of_forall hstep)

/-- **Portmanteau for Theorem 1.16 of Gwynne, Miller and Sheffield.** If the rescaled paths
`Y ε` under `Q` converge weakly in `C([0,∞), ℝ²)` to the Brownian law of `target` as `ε ↓ 0`,
then for every open set `U` of paths, `P_target(U) ≤ liminf_{ε ↓ 0} Q {Y ε ∈ U}`. -/
theorem le_liminf_measure_setOf_mem_of_convergesWeaklyInC {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2)
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget)
    (hY : ReflectedGMS.GMS.ConvergesWeaklyInC Q Y target)
    {U : Set (BouRabeeGwynne.BrownianPath 2)} (hU : IsOpen U) :
    (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) U ≤
      (𝓝[>] (0 : ℝ≥0)).liminf (fun ε => Q {ω | Y ε ω ∈ U}) :=
  le_liminf_measure_setOf_mem_of_isOpen Q Y _ hY hU

end LatticeProb.Portmanteau
