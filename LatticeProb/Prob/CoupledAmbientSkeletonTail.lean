import LatticeProb.Prob.CoupledSkeletonActiveTail

/-! # Coupled Brownian skeleton tails in a bounded ambient set -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal unitInterval

namespace LatticeProb

/-- A common horizon bounds the Brownian active flag under every coupling with
its exact skeleton marginal, uniformly over excursion domains contained in a
fixed bounded ambient set. -/
theorem brownian_ambient_coupled_sequence_active_tail
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {V : Set (Euc d)} (hV : Bornology.IsBounded V)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (U : J → Set (Euc d)), (∀ j, IsOpen (U j)) →
      (∀ j, U j ⊆ V) → ∀ z ∈ V, ∀ j₀ : J,
      ∀ (selector : ℕ → Euc d → Option J),
        (∀ n, Measurable (selector n)) →
        (∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j) →
        ∀ (A : Type*) [MeasurableSpace A]
          (ρ : Measure (A × (ℕ → Bool × C(unitInterval, Euc d)))),
          ρ.snd = μ.map (fun ω k => brownianSkeletonExcursion U z j₀ selector k ω) →
          ρ {p | (p.2 K).1 = false} ≤ ENNReal.ofReal η := by
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_activeSkeletonTail (J := J)
    hd hμ hV hε hη
  refine ⟨K, ?_⟩
  intro U hU hUV z hz j₀ selector hs hm A _ ρ hρ
  have hseq : Measurable (fun ω k => brownianSkeletonExcursion U z j₀ selector k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion U hU z j₀ hs k
  have hactive : MeasurableSet {s : ℕ → Bool × C(unitInterval, Euc d) | (s K).1 = false} :=
    (measurable_pi_apply K).fst (measurableSet_singleton false)
  calc
    ρ {p | (p.2 K).1 = false} = ρ.snd {s | (s K).1 = false} :=
      (Measure.snd_apply hactive).symm
    _ = μ {ω | (brownianSkeletonExcursion U z j₀ selector K ω).1 = false} := by
      rw [hρ, Measure.map_apply hseq hactive]
      rfl
    _ = μ {ω | (brownianSkeletonClock U z j₀ selector K ω).1 = false} := by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, brownianSkeletonExcursion_flag]
    _ ≤ ENNReal.ofReal η := hK U hU hUV z hz j₀ selector hs hm

end LatticeProb
