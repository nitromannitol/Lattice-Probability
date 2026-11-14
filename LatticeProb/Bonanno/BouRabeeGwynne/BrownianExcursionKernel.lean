/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExcursionKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedBrownianMeasurable
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianHarmonicExit
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Actual Brownian excursion laws as a kernel in the starting point

Spatial translation reduces joint starting-point measurability to the already
proved fixed-start stopping map. The kernel retains the full normalized
continuous excursion, not merely its exit point.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BouRabeeGwynne

noncomputable def translatedBrownianPath {d : ℕ} (z : Euc d) (ω : BrownianPath d) :
    BrownianPath d := ⟨fun t ↦ z + ω t, continuous_const.add ω.continuous⟩

lemma continuous_translatedBrownianPath {d : ℕ} :
    Continuous (fun p : Euc d × BrownianPath d ↦ translatedBrownianPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (Euc d × BrownianPath d) × ℝ≥0 ↦ p.1.1 + p.1.2 p.2)
  fun_prop

lemma continuousExitTime_translated {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ω : BrownianPath d) :
    continuousExitTime U 0 (translatedBrownianPath z ω) = continuousExitTime U z ω := by
  unfold continuousExitTime
  change (⨅ t : {t : ℝ≥0 // 0 + (z + ω t) ∉ U}, (t.val : ℝ≥0∞)) = _
  apply le_antisymm
  · apply le_iInf
    intro t
    exact iInf_le_of_le ⟨t.val, by simpa only [zero_add] using t.property⟩ le_rfl
  · apply le_iInf
    intro t
    exact iInf_le_of_le ⟨t.val, by simpa only [zero_add] using t.property⟩ le_rfl

lemma stoppedBrownianRepresentative_translated {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ω : BrownianPath d) :
    stoppedBrownianRepresentative U 0 (translatedBrownianPath z ω) =
      stoppedBrownianRepresentative U z ω := by
  apply ContinuousMap.ext
  intro t
  let s₁ : ℝ≥0 := ⟨(t : ℝ) *
    ((continuousExitTime U 0 (translatedBrownianPath z ω)).toNNReal : ℝ),
    mul_nonneg t.property.1 (NNReal.coe_nonneg _)⟩
  let s₂ : ℝ≥0 := ⟨(t : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
    mul_nonneg t.property.1 (NNReal.coe_nonneg _)⟩
  change 0 + (z + ω s₁) = z + ω s₂
  have hs : s₁ = s₂ := by
    apply Subtype.ext
    exact congrArg (fun τ : ℝ≥0∞ ↦ (t : ℝ) * (τ.toNNReal : ℝ))
      (continuousExitTime_translated U z ω)
  rw [zero_add, hs]

lemma measurable_stoppedBrownianRepresentative_joint {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) :
    Measurable (fun p : Euc d × BrownianPath d ↦ stoppedBrownianRepresentative U p.1 p.2) := by
  have heq : (fun p : Euc d × BrownianPath d ↦ stoppedBrownianRepresentative U p.1 p.2) =
      (fun p ↦ stoppedBrownianRepresentative U 0 (translatedBrownianPath p.1 p.2)) := by
    funext p
    exact (stoppedBrownianRepresentative_translated U p.1 p.2).symm
  rw [heq]
  exact (measurable_stoppedBrownianRepresentative hU 0).comp
    continuous_translatedBrownianPath.measurable

/-- The actual pushforward law of the whole stopped excursion, varying
measurably with its spatial starting point. -/
noncomputable def brownianExcursionKernel {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] :
    Kernel (Euc d) C(unitInterval, Euc d) where
  toFun z := μ.map (stoppedBrownianRepresentative U z)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hpre := (measurable_stoppedBrownianRepresentative_joint hU) hA
    have hsection := measurable_measure_prodMk_left (ν := μ) hpre
    simp only [Measure.map_apply (measurable_stoppedBrownianRepresentative hU _) hA]
    exact hsection

lemma brownianExcursionKernel_apply {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] (z : Euc d) :
    brownianExcursionKernel hU μ z = μ.map (stoppedBrownianRepresentative U z) := rfl

instance brownianExcursionKernel_isMarkov {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (brownianExcursionKernel hU μ) where
  isProbabilityMeasure z :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_stoppedBrownianRepresentative hU z).aemeasurable).mpr inferInstance

lemma brownianExcursionKernel_ae_start {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) (z : Euc d) :
    ∀ᵐ c ∂brownianExcursionKernel hU μ z, c 0 = z := by
  rw [brownianExcursionKernel_apply]
  apply (ae_map_iff (measurable_stoppedBrownianRepresentative hU z).aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)).mpr
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
  simpa [stoppedBrownianRepresentative, hω]

lemma stoppedBrownianRepresentative_mem_closure {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) {z : Euc d} {ω : BrownianPath d} (hstart : z + ω 0 ∈ U)
    (hfinite : continuousExitTime U z ω ≠ ∞) (t : unitInterval) :
    stoppedBrownianRepresentative U z ω t ∈ closure U := by
  let s : ℝ≥0 := ⟨(t : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
    mul_nonneg t.property.1 (continuousExitTime U z ω).toNNReal.property⟩
  change z + ω s ∈ closure U
  have hs : s ≤ (continuousExitTime U z ω).toNNReal := by
    apply NNReal.coe_le_coe.mp
    exact mul_le_of_le_one_left (NNReal.coe_nonneg _) t.property.2
  rcases eq_or_lt_of_le hs with heq | hlt
  · rw [heq]
    exact frontier_subset_closure (continuousExitTime_mem_frontier hU hstart hfinite)
  · apply subset_closure
    apply mem_of_lt_continuousExitTime
    rw [← ENNReal.coe_toNNReal hfinite]
    exact ENNReal.coe_lt_coe.mpr hlt

/-- The whole genuine excursion stays in the domain closure, including its
terminal exit point. This supplies the ball oscillation bound used in coupling. -/
lemma brownianExcursionKernel_ae_mem_closure {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) {z : Euc d} (hz : z ∈ U) :
    ∀ᵐ c ∂brownianExcursionKernel hU μ z, ∀ t, c t ∈ closure U := by
  have hset : MeasurableSet {c : C(unitInterval, Euc d) | ∀ t, c t ∈ closure U} := by
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun t ↦ isClosed_closure.preimage
      (continuous_eval_const t)).measurableSet
  rw [brownianExcursionKernel_apply]
  apply (ae_map_iff (measurable_stoppedBrownianRepresentative hU z).aemeasurable hset).mpr
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
    standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω hzero hfinite
  exact fun t ↦ stoppedBrownianRepresentative_mem_closure hU (by simpa [hzero] using hz)
    hfinite t

lemma brownianExcursionKernel_project {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] (z : Euc d) :
    (brownianExcursionKernel hU μ z).map CurveSpace.project = stoppedBrownianLaw U z μ := by
  rw [brownianExcursionKernel_apply, Measure.map_map CurveSpace.continuous_project.measurable
    (measurable_stoppedBrownianRepresentative hU z)]
  rfl

end BouRabeeGwynne
