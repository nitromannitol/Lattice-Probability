import LatticeProb.Prob.ConditionalLawCriterion
import LatticeProb.Prob.ExtendedMappingAE

/-!
# Limits of regular conditional laws

Let `(X n, Y n)` converge in law to `ν` on `E × F`, and suppose that `κ n (Y n)` is a regular
conditional law of `X n` given `Y n`, where `κ n : F → Measure E` is a family of probability
measures with measurable integrals of bounded continuous functions.  If, for every bounded continuous
`f` and `ν.snd`-almost every `y`, the maps `y' ↦ ∫ f d(κ n y')` converge to the number `∫ f d(P y)`
uniformly on a small ball around `y`, then `P` is a regular conditional law of `X` given `Y` under `ν`.

This is the form in which the criterion for convergence of conditional laws
(`LatticeProb.compProd_eq_of_condexp_tendsto`) is used for limits of Markov kernels: the conditional
expectations are the values of the discrete kernels, and the kernels converge locally uniformly at
the continuity points of the limit kernel.

* `LatticeProb.compProd_eq_of_kernel_locally_uniform`: the statement
  `ν.map Prod.swap = ν.snd ⊗ₘ P`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology BoundedContinuousFunction ProbabilityTheory MeasurableSpace
open scoped ENNReal NNReal

namespace LatticeProb

variable {E F : Type*}
  [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
  [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- **Regular conditional law of a limit of kernels.**  Let `(X n, Y n) → ν` in law on `E × F`
and let `κ n : F → Measure E` be probability measures whose integrals of bounded continuous
functions are measurable and such that `E[f (X n) | Y n] = ∫ f d(κ n (Y n))` almost surely.  If `P`
is a family of probability measures with measurable integrals and, for every bounded continuous `f`
and `ν.snd`-almost every `y`, the functions `y' ↦ ∫ f d(κ n y')` converge to `∫ f d(P y)` uniformly
on a small ball around `y`, then `P` is a Markov kernel and a regular conditional law of `X` given
`Y`: `ν.map Prod.swap = ν.snd ⊗ₘ P`. -/
theorem compProd_eq_of_kernel_locally_uniform
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)] {X : ∀ n, Ω n → E} {Y : ∀ n, Ω n → F}
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    {ν : Measure (E × F)} [IsProbabilityMeasure ν]
    (hlaw : ∀ g : (E × F) →ᵇ ℝ, Tendsto (fun n => ∫ ω, g (X n ω, Y n ω) ∂μ n) atTop
      (𝓝 (∫ p, g p ∂ν)))
    {κ : ℕ → F → Measure E} [∀ n y, IsProbabilityMeasure (κ n y)]
    (hκm : ∀ n (f : E →ᵇ ℝ), Measurable fun y => ∫ x, f x ∂κ n y)
    (hκ : ∀ n (f : E →ᵇ ℝ), condExpGiven (μ n) (X n) (Y n) f
      =ᵐ[μ n] fun ω => ∫ x, f x ∂κ n (Y n ω))
    {P : F → Measure E} [∀ y, IsProbabilityMeasure (P y)]
    (hP : ∀ f : E →ᵇ ℝ, Measurable fun y => ∫ x, f x ∂P y)
    (hlu : ∀ f : E →ᵇ ℝ, ∀ᵐ y ∂ν.snd, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n → ∀ y' : F, dist y' y < δ → |∫ x, f x ∂κ n y' - ∫ x, f x ∂P y| ≤ ε) :
    ∃ κ' : Kernel F E, IsMarkovKernel κ' ∧ (∀ y, κ' y = P y) ∧
      ν.map Prod.swap = ν.snd ⊗ₘ κ' := by
  classical
  refine compProd_eq_of_condexp_tendsto (l := atTop) hX hY hlaw hP ?_
  intro f g
  have hlimY : ∀ G : F →ᵇ ℝ, Tendsto (fun n => ∫ y, G y ∂((μ n).map (Y n))) atTop
      (𝓝 (∫ y, G y ∂ν.snd)) := by
    intro G
    have h := hlaw (G.compContinuous ⟨Prod.snd, continuous_snd⟩)
    have e1 : ∀ n, ∫ y, G y ∂((μ n).map (Y n)) = ∫ ω, G (Y n ω) ∂μ n := fun n =>
      integral_map (hY n).aemeasurable G.continuous.aestronglyMeasurable
    have e2 : ∫ y, G y ∂ν.snd = ∫ p, G p.2 ∂ν :=
      integral_map measurable_snd.aemeasurable G.continuous.aestronglyMeasurable
    simpa [e1, e2] using h
  have hlu' : ∀ᵐ y ∂ν.snd, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ y' : F, dist y' y < δ →
        dist (∫ x, f x ∂κ n y') (∫ x, f x ∂P y) ≤ ε := by
    filter_upwards [hlu f] with y hy ε hε
    obtain ⟨δ, hδ, N, hN⟩ := hy ε hε
    exact ⟨δ, hδ, N, fun n hn y' hy' => by simpa [Real.dist_eq] using hN n hn y' hy'⟩
  have hmain := tendsto_integral_comp_prod_of_ae_locally_uniform ν.snd
    (fun n => (μ n).map (Y n)) hlimY (fun y => ∫ x, f x ∂P y) (fun n y => ∫ x, f x ∂κ n y)
    (fun n => hκm n f) (hP f) hlu' g
  have e1 : ∀ n, ∫ ω, g (condExpGiven (μ n) (X n) (Y n) f ω, Y n ω) ∂μ n =
      ∫ y, g (∫ x, f x ∂κ n y, y) ∂((μ n).map (Y n)) := by
    intro n
    have hm : Measurable fun y => g (∫ x, f x ∂κ n y, y) :=
      g.continuous.measurable.comp ((hκm n f).prodMk measurable_id)
    rw [integral_map (hY n).aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hκ n f] with ω hω
    simp only [hω]
  have e2 : ∫ p, g (∫ x, f x ∂P p.2, p.2) ∂ν = ∫ y, g (∫ x, f x ∂P y, y) ∂ν.snd := by
    have hm : Measurable fun y => g (∫ x, f x ∂P y, y) :=
      g.continuous.measurable.comp ((hP f).prodMk measurable_id)
    exact (integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable).symm
  rw [funext e1, e2]
  exact hmain

end LatticeProb
