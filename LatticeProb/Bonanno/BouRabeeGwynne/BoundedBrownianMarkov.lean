/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BoundedBrownianMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppingApprox
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppingLimit

/-!
# The actual Brownian strong Markov identity at bounded stopping times

The proof constructs finite dyadic upper approximations, applies the proved
finite-stopping identity, and passes to the limit by continuous path shifts
and dominated convergence. No Markov property at random times is assumed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

private lemma stoppingTime_measurableSpace_congr {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {τ π : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hπ : IsStoppingTime F π) (heq : τ = π) :
    hτ.measurableSpace = hπ.measurableSpace := by
  subst π
  rfl

theorem standardBrownianLaw_boundedStopping_map_restrict {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {σ : BrownianPath d → ℝ≥0}
    (hσ : IsStoppingTime (brownianNaturalFiltration d) (fun ω ↦ (σ ω : ℝ≥0∞)))
    (N : ℝ≥0) (hN : ∀ ω, σ ω ≤ N)
    {A : Set (BrownianPath d)} (hA : MeasurableSet[hσ.measurableSpace] A) :
    (μ.restrict A).map (fun ω ↦ shiftedBrownianPath (σ ω) ω) = μ A • μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hmσ : Measurable σ := by
    have hcoe : Measurable (fun ω ↦ (σ ω : ℝ≥0∞)) := hσ.measurable'
    simpa only [Function.comp_def, ENNReal.toNNReal_coe] using
      ENNReal.measurable_toNNReal.comp hcoe
  have hstop (n : ℕ) := isStoppingTime_dyadicStoppingTime (brownianNaturalFiltration d) hσ n
  have hm (n : ℕ) : Measurable (dyadicStoppingTime σ n) := by
    have hcoe : Measurable (fun ω ↦ (dyadicStoppingTime σ n ω : ℝ≥0∞)) :=
      (hstop n).measurable'
    simpa only [Function.comp_def, ENNReal.toNNReal_coe] using
      ENNReal.measurable_toNNReal.comp hcoe
  apply map_eq_of_ae_tendsto_of_map_eq
    (measurable_variable_shiftedBrownianPath hmσ)
    (fun n ↦ measurable_variable_shiftedBrownianPath (hm n))
  · intro n
    apply standardBrownianLaw_finiteStopping_map_restrict hμ (hstop n)
      (dyadicStoppingRange N n) (dyadicStoppingTime_mem_range hN n)
    exact IsStoppingTime.measurableSpace_mono hσ (hstop n)
      (fun ω ↦ ENNReal.coe_le_coe.mpr (le_dyadicStoppingTime σ n ω)) _ hA
  · exact Filter.Eventually.of_forall fun ω ↦
      (continuous_shiftedBrownianPath.tendsto (σ ω, ω)).comp
        ((tendsto_dyadicStoppingTime σ ω).prodMk_nhds tendsto_const_nhds)

/-- The bounded identity for an extended-valued stopping time. The finite
bound proves that the concrete `toNNReal` representative equals the original
time, including in its stopping-time sigma algebra. -/
theorem standardBrownianLaw_boundedStoppingENNReal_map_restrict {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (N : ℝ≥0) (hN : ∀ ω, τ ω ≤ (N : ℝ≥0∞))
    {A : Set (BrownianPath d)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (fun ω ↦ shiftedBrownianPath (τ ω).toNNReal ω) = μ A • μ := by
  have heq : (fun ω ↦ ((τ ω).toNNReal : ℝ≥0∞)) = τ := by
    funext ω
    exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hN ω))
  have hstop : IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ ((τ ω).toNNReal : ℝ≥0∞)) := heq.symm ▸ hτ
  have hA' : MeasurableSet[hstop.measurableSpace] A :=
    (stoppingTime_measurableSpace_congr hstop hτ heq).symm ▸ hA
  exact standardBrownianLaw_boundedStopping_map_restrict hμ hstop N
    (fun ω ↦ ENNReal.coe_le_coe.mp (ENNReal.coe_toNNReal_le_self.trans (hN ω))) hA'

end BouRabeeGwynne
