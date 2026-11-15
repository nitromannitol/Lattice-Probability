import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonPrefix
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionOscillation

/-! # Support of Brownian skeleton excursion marginals -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set BouRabeeGwynne
open scoped ENNReal unitInterval

namespace LatticeProb

/-- A Brownian skeleton has compatible finite prefixes and the prescribed
initial point, and any assumed oscillation bound is preserved by its law. -/
theorem brownian_skeleton_marginal_support
    {d K : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (hselector : ∀ n, Measurable (selector n))
    {S : ℝ}
    (hrange : ∀ᵐ ω ∂μ, ∀ i ≤ K,
      (brownianSkeletonExcursion U z j₀ selector i ω).2 ∈ curveOscillationLe S) :
    ∀ᵐ b ∂μ.map (fun ω i => brownianSkeletonExcursion U z j₀ selector i ω),
      (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      (b 0).2 0 = z ∧ ∀ i ≤ K, (b i).2 ∈ curveOscillationLe S := by
  let B : Set (ℕ → Bool × C(unitInterval, Euc d)) := {b |
    (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      (b 0).2 0 = z ∧ ∀ i ≤ K, (b i).2 ∈ curveOscillationLe S}
  have hB : MeasurableSet B := by
    have hr : MeasurableSet {b : ℕ → Bool × C(unitInterval, Euc d) |
        ∀ i ≤ K, (b i).2 ∈ curveOscillationLe S} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        (measurable_pi_apply i).snd (measurableSet_curveOscillationLe S)
    exact ((ExcursionTrajectory.measurableSet_compatiblePaths K d).preimage
      (Measurable.of_eval fun i => (measurable_pi_apply i).snd)).inter
      ((measurableSet_eq_fun ((ContinuousMap.measurable_eval 0).comp
        (measurable_pi_apply 0).snd) measurable_const).inter hr)
  have hstart : ∀ᵐ ω ∂μ, (brownianSkeletonExcursion U z j₀ selector 0 ω).2 0 = z := by
    exact ae_of_ae_map (measurable_stoppedBrownianRepresentative (hU j₀) z).aemeasurable
      (brownianExcursionKernel_ae_start (hU j₀) μ hμ z)
  have hactual : ∀ᵐ ω ∂μ,
      (fun i => brownianSkeletonExcursion U z j₀ selector i ω) ∈ B := by
    filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ U hU hUb z j₀ hselector K,
      hstart, hrange] with ω hfinite hs hr
    refine ⟨?_, hs, hr⟩
    have hchain := brownianSkeletonPhysicalKnots_chain_apply U z j₀ selector K ω hfinite
    intro i j hij
    change (brownianSkeletonExcursion U z j₀ selector i.val ω).2 1 =
      (brownianSkeletonExcursion U z j₀ selector j.val ω).2 0
    rw [← hchain i, ← hchain j]
    exact ((brownianSkeletonPhysicalKnots U z j₀ selector K ω hfinite).chain
      z ω).property i j hij
  exact (ae_map_iff (Measurable.of_eval fun i =>
    measurable_brownianSkeletonExcursion U hU z j₀ hselector i).aemeasurable hB).mpr hactual

end LatticeProb
