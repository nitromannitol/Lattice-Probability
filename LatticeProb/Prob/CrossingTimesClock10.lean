/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesClock8
import LatticeProb.Prob.CondIndepEvMarkov

/-!
# Conditional independence at the inverse crossing clock

Let `K : E → Prob C(ℝ≥0, E)` be a continuous family of path laws with the Markov property at
deterministic times, started at `z`, and let `A_t = pathClockInv m · t` be the inverse crossing
clock, almost surely finite.  Write `x_A = x (A_t)`, `x^A = stopPath x A_t` (the path stopped at
`A_t`) and `θ_A x = pathShift x A_t` (the path after `A_t`).  The strong Markov property at the
strict stopping time `A_t` (`strongMarkov_pathClockInv`) says that, given the stopped path, the
shifted path has law `K (x_A)`.  Consequently the shifted path `θ_A x` is conditionally
independent of the stopped path `x^A` given the value `x_A`
(`condIndepEv_pathClockInv`; this uses `condIndepEv_of_kernel_markov`, and that `x_A` is a
measurable function of the stopped path, `measurable_value_stopPath`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

/-- A sequential pointwise limit of measurable functions into a metrizable space is measurable,
for an arbitrary σ-algebra on the domain. -/
theorem measurable_of_tendsto_metrizable_of_sigma {α β : Type*} {mα : MeasurableSpace α}
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : ℕ → α → β} {g : α → β} (hf : ∀ i, Measurable[mα] (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable[mα] g :=
  measurable_of_tendsto_metrizable hf lim

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [SecondCountableTopology E] in
/-- **The value of the path at `A_t` is a measurable function of the path stopped at `A_t`.** -/
theorem measurable_value_stopPath (m : ℝ≥0∞) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap
      (fun x : C(ℝ≥0, E) => stopPath x (pathClockInv m x t).toNNReal) inferInstance]
      fun x : C(ℝ≥0, E) => x (pathClockInv m x t).toNNReal := by
  have hn : ∀ n : ℕ, Measurable[MeasurableSpace.comap
      (fun x : C(ℝ≥0, E) => stopPath x (pathClockInv m x t).toNNReal) inferInstance]
      fun x : C(ℝ≥0, E) => (stopPath x (pathClockInv m x t).toNNReal) (n : ℝ≥0) := fun n =>
    (continuous_eval_const (n : ℝ≥0)).measurable.comp (comap_measurable _)
  refine measurable_of_tendsto_metrizable_of_sigma hn ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (pathClockInv m x t).toNNReal
  filter_upwards [eventually_ge_atTop N] with n hn'
  have h1 : (pathClockInv m x t).toNNReal ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn')
  simp [stopPath_apply, min_eq_right h1]

/-- **Conditional independence at the inverse crossing clock**: under `K z`, the path after `A_t`
is conditionally independent of the path stopped at `A_t` given the value `x (A_t)`. -/
theorem condIndepEv_pathClockInv {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    {z : E} (hM : ∀ t, MarkovAt K z t) (m : ℝ≥0∞) (t : ℝ≥0)
    (hfin : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), pathClockInv m x t < ⊤) :
    CondIndepEv
      (MeasurableSpace.comap
        (fun x : C(ℝ≥0, E) => x (pathClockInv m x t).toNNReal) inferInstance)
      (MeasurableSpace.comap
        (fun x : C(ℝ≥0, E) => pathShift x (pathClockInv m x t).toNNReal) inferInstance)
      (MeasurableSpace.comap
        (fun x : C(ℝ≥0, E) => stopPath x (pathClockInv m x t).toNNReal) inferInstance)
      (K z : Measure C(ℝ≥0, E)) := by
  have hT : Measurable fun x : C(ℝ≥0, E) => (pathClockInv m x t).toNNReal :=
    (measurable_pathClockInv m t).ennreal_toNNReal
  have hS : Measurable fun x : C(ℝ≥0, E) => stopPath x (pathClockInv m x t).toNNReal :=
    continuous_stopPath_uncurry.measurable.comp (measurable_id.prodMk hT)
  have hsh : Measurable fun x : C(ℝ≥0, E) => pathShift x (pathClockInv m x t).toNNReal :=
    continuous_pathShift_uncurry.measurable.comp (measurable_id.prodMk hT)
  let kE : Kernel E C(ℝ≥0, E) :=
    ⟨fun z => (K z : Measure C(ℝ≥0, E)), measurable_measure_comp_of_continuous hK measurable_id⟩
  have : IsMarkovKernel kE :=
    ⟨fun z => by
      show IsProbabilityMeasure (K z : Measure C(ℝ≥0, E))
      infer_instance⟩
  refine condIndepEv_of_kernel_markov (measurable_value_stopPath m t).comap_le hS.comap_le
    (comap_measurable _) hsh kE ?_
  intro a ha β hβ
  obtain ⟨a', ha', rfl⟩ := ha
  have hg : Measurable fun p : C(ℝ≥0, E) × C(ℝ≥0, E) =>
      a'.indicator (fun _ => (1 : ℝ)) p.1 * β.indicator (fun _ => (1 : ℝ)) p.2 :=
    ((measurable_const.indicator ha').comp measurable_fst).mul
      ((measurable_const.indicator hβ).comp measurable_snd)
  have hSM := strongMarkov_pathClockInv hK (hM) m t hfin hg (C := 1) (fun p => by
    by_cases h1 : p.1 ∈ a' <;> by_cases h2 : p.2 ∈ β <;> simp [h1, h2])
  rw [← integral_indicator (hS ha'), ← integral_indicator (hS ha')]
  have e1 : ∀ x : C(ℝ≥0, E),
      ((fun x => stopPath x (pathClockInv m x t).toNNReal) ⁻¹' a').indicator
        (fun x => ((fun x => pathShift x (pathClockInv m x t).toNNReal) ⁻¹' β).indicator
          (fun _ => (1 : ℝ)) x) x =
      a'.indicator (fun _ => (1 : ℝ)) (stopPath x (pathClockInv m x t).toNNReal) *
        β.indicator (fun _ => (1 : ℝ)) (pathShift x (pathClockInv m x t).toNNReal) := by
    intro x
    by_cases h1 : stopPath x (pathClockInv m x t).toNNReal ∈ a' <;>
      by_cases h2 : pathShift x (pathClockInv m x t).toNNReal ∈ β <;>
      simp [Set.indicator, h1, h2]
  have e2 : ∀ x : C(ℝ≥0, E),
      ((fun x => stopPath x (pathClockInv m x t).toNNReal) ⁻¹' a').indicator
        (fun x => (kE (x (pathClockInv m x t).toNNReal) β).toReal) x =
      ∫ w, a'.indicator (fun _ => (1 : ℝ)) (stopPath x (pathClockInv m x t).toNNReal) *
        β.indicator (fun _ => (1 : ℝ)) w
        ∂(K (x (pathClockInv m x t).toNNReal) : Measure C(ℝ≥0, E)) := by
    intro x
    rw [integral_const_mul]
    have h3 : ∫ w, β.indicator (fun _ => (1 : ℝ)) w
        ∂(K (x (pathClockInv m x t).toNNReal) : Measure C(ℝ≥0, E)) =
        (kE (x (pathClockInv m x t).toNNReal) β).toReal := by
      exact integral_indicator_one (μ := (K (x (pathClockInv m x t).toNNReal) :
        Measure C(ℝ≥0, E))) hβ
    rw [h3]
    by_cases h1 : stopPath x (pathClockInv m x t).toNNReal ∈ a' <;> simp [Set.indicator, h1]
  simp_rw [e1, e2]
  exact hSM

end LatticeProb
