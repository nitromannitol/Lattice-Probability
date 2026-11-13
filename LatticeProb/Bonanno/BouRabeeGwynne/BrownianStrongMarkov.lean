/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStrongMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BoundedBrownianMarkov
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteExit
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Brownian strong Markov at actual finite exit times

The bounded theorem is extended by intersecting the observed event with
`{τ ≤ n}` and letting n grow. The first-exit specialization uses the proved
almost-sure finite exit, with infinity totalized only on a null set.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

private lemma tendsto_measure_truncated_by_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : Ω → ℝ≥0∞} (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞) (A : Set Ω) :
    Tendsto (fun n : ℕ ↦ μ (A ∩ {ω | τ ω ≤ (n : ℝ≥0∞)})) atTop (𝓝 (μ A)) := by
  have hmono : Monotone (fun n : ℕ ↦ A ∩ {ω | τ ω ≤ (n : ℝ≥0∞)}) := by
    intro n m hnm ω hω
    refine ⟨hω.1, ?_⟩
    change τ ω ≤ (m : ℝ≥0∞)
    exact hω.2.trans (show (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) by exact_mod_cast hnm)
  have hunion : (⋃ n : ℕ, A ∩ {ω | τ ω ≤ (n : ℝ≥0∞)}) =ᵐ[μ] A := by
    filter_upwards [hfinite] with ω hω
    apply propext
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact hn.1
    · intro hA
      obtain ⟨n, hn⟩ := exists_nat_gt ((τ ω).toNNReal : ℝ)
      refine mem_iUnion.mpr ⟨n, hA, ?_⟩
      change τ ω ≤ (n : ℝ≥0∞)
      rw [← ENNReal.coe_toNNReal hω]
      exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hn.le)
  simpa only [measure_congr hunion, Function.comp_def] using
    (tendsto_measure_iUnion_atTop (μ := μ) hmono)

/-- The actual continuous Brownian future is independent of every event
observable by an almost surely finite stopping time, and has the original law. -/
theorem standardBrownianLaw_aeFiniteStopping_map_restrict {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞)
    {A : Set (BrownianPath d)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) = μ A • μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hm : Measurable (fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) :=
    measurable_variable_shiftedBrownianPath (ENNReal.measurable_toNNReal.comp hτ.measurable')
  ext S hS
  rw [Measure.map_apply hm hS, Measure.restrict_apply (hm hS),
    Measure.smul_apply, smul_eq_mul]
  have heq (n : ℕ) :
      μ (((fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) ⁻¹' S ∩ A) ∩
        {ω | τ ω ≤ (n : ℝ≥0∞)}) = μ S * μ (A ∩ {ω | τ ω ≤ (n : ℝ≥0∞)}) := by
    let An : Set (BrownianPath d) := A ∩ {ω | τ ω ≤ (n : ℝ≥0∞)}
    have hAn : MeasurableSet[(hτ.min_const (n : ℝ≥0)).measurableSpace] An := by
      apply (hτ.measurableSet_inter_le_const_iff A (n : ℝ≥0)).mp
      exact hA.inter (hτ.measurableSet_le' (n : ℝ≥0))
    have hlaw := standardBrownianLaw_boundedStoppingENNReal_map_restrict hμ
      (hτ.min_const (n : ℝ≥0)) (n : ℝ≥0) (fun ω ↦ min_le_right _ _) hAn
    have hmtrunc : Measurable (fun ω ↦
        shiftedBrownianPath (min (τ ω) (n : ℝ≥0∞)).toNNReal ω) :=
      measurable_variable_shiftedBrownianPath
        (ENNReal.measurable_toNNReal.comp (hτ.min_const (n : ℝ≥0)).measurable')
    have heval := congrArg (fun ρ : Measure (BrownianPath d) ↦ ρ S) hlaw
    change ((μ.restrict An).map (fun ω ↦ shiftedBrownianPath
      (min (τ ω) (n : ℝ≥0∞)).toNNReal ω)) S = (μ An • μ) S at heval
    rw [Measure.map_apply hmtrunc hS, Measure.restrict_apply (hmtrunc hS),
      Measure.smul_apply, smul_eq_mul] at heval
    have hsets : ((fun ω ↦ shiftedBrownianPath
        (min (τ ω) (n : ℝ≥0∞)).toNNReal ω) ⁻¹' S ∩ An) =
        (((fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) ⁻¹' S ∩ A) ∩
          {ω | τ ω ≤ (n : ℝ≥0∞)}) := by
      ext ω
      by_cases h : τ ω ≤ (n : ℝ≥0∞)
      · simp only [mem_inter_iff, mem_preimage, An, mem_setOf_eq, h,
          min_eq_left h, and_true]
      · simp only [mem_inter_iff, mem_preimage, An, mem_setOf_eq, h, and_false]
    rw [hsets] at heval
    exact heval.trans (mul_comm _ _)
  have hleft := tendsto_measure_truncated_by_ae_finite μ hfinite
    ((fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) ⁻¹' S ∩ A)
  have hright := (ENNReal.continuous_const_mul (measure_ne_top μ S)).tendsto (μ A) |>.comp
    (tendsto_measure_truncated_by_ae_finite μ hfinite A)
  have hevent := tendsto_nhds_unique hleft (hright.congr fun n ↦ (heq n).symm)
  exact hevent.trans (mul_comm _ _)

/-- The random-time law needed for the domain and ball exit skeletons in
Section 4, specialized to the genuine first exit of the canonical path. -/
theorem standardBrownianLaw_exit_map_restrict {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z : Euc d)
    {A : Set (BrownianPath d)}
    (hA : MeasurableSet[(isStoppingTime_continuousExitTime hU z).measurableSpace] A) :
    (μ.restrict A).map (fun ω ↦
      shiftedBrownianPath (continuousExitTime U z ω).toNNReal ω) = μ A • μ :=
  standardBrownianLaw_aeFiniteStopping_map_restrict hμ
    (isStoppingTime_continuousExitTime hU z) (standardBrownianLaw_ae_finiteExit hd hμ hUb z) hA

end BouRabeeGwynne
