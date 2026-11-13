import Mathlib
import LatticeProb.Prob.MarkovStepCriterion
import LatticeProb.Prob.ConvergenceInLawDeterministicTime
import LatticeProb.Prob.StopPathMeasurable
import LatticeProb.Prob.PathSpaceDUnif

/-!
# Markov property at a fixed time for limits of walks in a random environment

Let `D n` be random elements of a pseudo-metric space `S₀` (the environment, including a continuous
field `K : S₀ → C(E, Prob C(ℝ≥0, E))` of path laws) and `X n` random continuous paths in a locally compact
Polish metric space `E`, such that `(D n, X n)` converges in law to `ν` on `S₀ × C(ℝ≥0, E)`.  Let
`s n → t` be deterministic times.  Assume that, given a σ-algebra `G n` containing the environment and the
path stopped at time `s n`, the shifted path `u ↦ X n (s n + u)` has the quenched conditional law `κ n`
(a random probability measure on `C(ℝ≥0, E)`), and that `κ n` is close in probability, in the Lévy-Prokhorov
distance, to the law `K (D n) (X n (s n))` attached by the environment to the current position.  Then under
`ν` the shifted path `x (t + ·)` has regular conditional law `K d (x t)` given the environment `d` and the
stopped path `x (· ∧ t)`: this is the Markov property at the time `t` of the limit with the kernel field `K`.

* `LatticeProb.pathShift`: the shifted path `u ↦ x (s + u)`; `continuous_pathShift_uncurry`: it is jointly
  continuous in `(x, s)` for the compact-open topology.
* `LatticeProb.compProd_eq_of_markov_step_pathShift`: the statement above, from the abstract Markov step
  (`LatticeProb.compProd_eq_of_markov_step`) and convergence in law with a deterministic time coordinate
  (`LatticeProb.tendsto_integral_prod_of_tendsto_nnreal`).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

section PathShift

variable {E : Type*} [MetricSpace E]

/-- The path `u ↦ x (s + u)` shifted forward by the time `s`. -/
def pathShift (x : C(ℝ≥0, E)) (s : ℝ≥0) : C(ℝ≥0, E) :=
  x.comp ⟨fun u => s + u, continuous_const.add continuous_id⟩

@[simp] lemma pathShift_apply (x : C(ℝ≥0, E)) (s u : ℝ≥0) : pathShift x s u = x (s + u) := rfl

/-- The map `s ↦ (u ↦ s + u)` into the continuous self-maps of `ℝ≥0` is continuous. -/
theorem continuous_timeShiftCM : Continuous fun s : ℝ≥0 =>
    (⟨fun u => s + u, continuous_const.add continuous_id⟩ : C(ℝ≥0, ℝ≥0)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.add continuous_snd)

/-- The shifted path `(x, s) ↦ x (s + ·)` is jointly continuous for the compact-open topology. -/
theorem continuous_pathShift_uncurry :
    Continuous fun p : C(ℝ≥0, E) × ℝ≥0 => pathShift p.1 p.2 :=
  ContinuousMap.continuous_comp'.comp
    ((continuous_timeShiftCM.comp continuous_snd).prodMk continuous_fst)

end PathShift

attribute [local instance] dUnifMetricSpace

/-- **Markov property at a deterministic time for limits of walks in a random environment.**  See the
module documentation.  The conditional law of the shifted limit path `x (t + ·)` given the environment `d`
and the stopped path `x (· ∧ t)` is `K d (x t)`; here `T ≥ t` and the kernel is read off at the endpoint of
the stopped path at the time `T`. -/
theorem compProd_eq_of_markov_step_pathShift
    {Ω S₀ E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀] [BorelSpace S₀]
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [LocallyCompactSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    [MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E)))]
    [BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E)))]
    {D : ℕ → Ω → S₀} {X : ℕ → Ω → C(ℝ≥0, E)} (hD : ∀ n, Measurable (D n))
    (hX : ∀ n, Measurable (X n))
    {ν : Measure (S₀ × C(ℝ≥0, E))} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (S₀ × C(ℝ≥0, E)) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (D n ω, X n ω) ∂μ) atTop (𝓝 (∫ q, g q ∂ν)))
    {s : ℕ → ℝ≥0} {t T : ℝ≥0} (hs : Tendsto s atTop (𝓝 t)) (hsT : ∀ n, s n ≤ T)
    {K : S₀ → C(E, ProbabilityMeasure C(ℝ≥0, E))} (hK : Continuous K)
    {G : ℕ → MeasurableSpace Ω}
    (hYG : ∀ n, MeasurableSpace.comap (fun ω => (D n ω, stopPath (X n ω) (s n))) inferInstance ≤ G n)
    (hG : ∀ n, G n ≤ m₀)
    {κ : ℕ → Ω → ProbabilityMeasure C(ℝ≥0, E)}
    (hκ : ∀ n, AEMeasurable (fun ω => LevyProkhorov.ofMeasure (κ n ω)) μ)
    (hMarkov : ∀ (n : ℕ) (f : C(ℝ≥0, E) →ᵇ ℝ),
      μ[fun ω => f (pathShift (X n ω) (s n)) | G n] =ᵐ[μ]
        fun ω => ∫ x, f x ∂(κ n ω : Measure C(ℝ≥0, E)))
    (hclose : TendstoInMeasure μ
      (fun n ω => levyProkhorovDist (κ n ω : Measure C(ℝ≥0, E))
        (K (D n ω) (X n ω (s n)) : Measure C(ℝ≥0, E))) atTop 0) :
    ∃ κ' : Kernel (S₀ × C(ℝ≥0, E)) C(ℝ≥0, E), IsMarkovKernel κ' ∧
      (∀ y, κ' y = K y.1 (y.2 T)) ∧
      ν.map (fun q => ((q.1, stopPath q.2 t), pathShift q.2 t)) =
        (ν.map fun q => (q.1, stopPath q.2 t)) ⊗ₘ κ' := by
  classical
  have hlawS : ∀ g : ((S₀ × C(ℝ≥0, E)) × ℝ≥0) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g ((D n ω, X n ω), s n) ∂μ) atTop
        (𝓝 (∫ d, g d ∂(ν.map fun q => (q, t)))) := by
    intro g
    have h := tendsto_integral_prod_of_tendsto_nnreal (P := μ)
      (D := fun n ω => (D n ω, X n ω)) (fun n => ((hD n).prodMk (hX n)).aemeasurable) hlaw hs g
    have h2 : ∫ d, g d ∂(ν.map fun q => (q, t)) = ∫ q, g (q, t) ∂ν :=
      integral_map (measurable_id.prodMk measurable_const).aemeasurable
        g.continuous.aestronglyMeasurable
    rw [h2]
    exact h
  have hΦ : Continuous fun q : (S₀ × C(ℝ≥0, E)) × ℝ≥0 => pathShift q.1.2 q.2 :=
    continuous_pathShift_uncurry.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hΨ : Continuous fun q : (S₀ × C(ℝ≥0, E)) × ℝ≥0 => (q.1.1, stopPath q.1.2 q.2) :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_stopPath_uncurry.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have hp : Continuous fun y : S₀ × C(ℝ≥0, E) => K y.1 (y.2 T) :=
    ContinuousEval.continuous_eval.comp
      ((hK.comp continuous_fst).prodMk ((continuous_eval_const T).comp continuous_snd))
  have hEq : ∀ n ω, K (D n ω) ((stopPath (X n ω) (s n)) T) = K (D n ω) (X n ω (s n)) := fun n ω => by
    rw [stopPath_apply, min_eq_right (hsT n)]
  have hclose' : TendstoInMeasure μ
      (fun n ω => levyProkhorovDist (κ n ω : Measure C(ℝ≥0, E))
        (K (D n ω) ((stopPath (X n ω) (s n)) T) : Measure C(ℝ≥0, E))) atTop 0 := by
    simpa only [hEq] using hclose
  obtain ⟨κ', hκ'M, hκ'p, hκ'⟩ := compProd_eq_of_markov_step (μ := μ)
    (D := fun n ω => ((D n ω, X n ω), s n))
    (fun n => ((hD n).prodMk (hX n)).prodMk measurable_const) hlawS hΦ hΨ hp hYG hG hκ hMarkov hclose'
  refine ⟨κ', hκ'M, hκ'p, ?_⟩
  have hm : Measurable fun q : S₀ × C(ℝ≥0, E) => (q, t) := measurable_id.prodMk measurable_const
  have hΘ : Measurable fun d : (S₀ × C(ℝ≥0, E)) × ℝ≥0 =>
      (pathShift d.1.2 d.2, (d.1.1, stopPath d.1.2 d.2)) := (hΦ.prodMk hΨ).measurable
  have e1 : ((ν.map fun q => (q, t)).map fun d : (S₀ × C(ℝ≥0, E)) × ℝ≥0 =>
      (pathShift d.1.2 d.2, (d.1.1, stopPath d.1.2 d.2))).map Prod.swap =
      ν.map (fun q => ((q.1, stopPath q.2 t), pathShift q.2 t)) := by
    rw [Measure.map_map measurable_swap hΘ, Measure.map_map (measurable_swap.comp hΘ) hm]
    rfl
  have e2 : ((ν.map fun q => (q, t)).map fun d : (S₀ × C(ℝ≥0, E)) × ℝ≥0 =>
      (pathShift d.1.2 d.2, (d.1.1, stopPath d.1.2 d.2))).snd =
      ν.map fun q => (q.1, stopPath q.2 t) := by
    rw [Measure.snd, Measure.map_map measurable_snd hΘ, Measure.map_map (measurable_snd.comp hΘ) hm]
    rfl
  rw [← e1, ← e2]
  exact hκ'

end LatticeProb
