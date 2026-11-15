import LatticeProb.Prob.BrownianFiniteDomainSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton

/-! # Brownian skeletons reaching an outer exit -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- A finite Brownian skeleton reaches the first outer exit with uniformly high
probability when its selector remains active throughout the outer set. -/
theorem brownian_finiteDomain_outerExit_skeleton_tail
    {d : ℕ} {J : Type*} [Finite J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    {Z : Set (Euc d)} (hZ : Bornology.IsBounded Z)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ z ∈ Z, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J),
        (∀ n, Measurable (selector n)) →
        (∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j) →
        ∀ outer : Set (Euc d),
        (∀ n x, x ∈ outer → selector n x ≠ none) →
        μ {ω | (brownianSkeletonClock U z j₀ selector K ω).2 <
          continuousExitTime outer z ω} ≤ ENNReal.ofReal η := by
  obtain ⟨K, hK⟩ := brownian_finiteDomain_activeSkeleton_tail hd hμ U hU hUb hZ hε hη
  refine ⟨K, ?_⟩
  intro z hz j₀ selector hselector hmargin outer hactive
  apply (measure_mono_ae ?_).trans (hK z hz j₀ selector hselector hmargin)
  filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ U hU hUb z j₀ hselector K] with ω hfinite hlate
  cases hflag : (brownianSkeletonClock U z j₀ selector K ω).1 with
  | false => rfl
  | true =>
    have hnone : ∀ n x, selector n x = none → x ∉ outer := by
      intro n x hn hx
      exact hactive n x hx hn
    have hexit := brownianSkeletonClock_exit_le_of_stopped U z j₀ selector hnone K ω hfinite hflag
    exact (not_lt_of_ge hexit hlate).elim

end LatticeProb
