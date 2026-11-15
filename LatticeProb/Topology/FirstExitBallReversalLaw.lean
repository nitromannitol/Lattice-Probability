import LatticeProb.Topology.FirstExitBallReversal
import Mathlib.Probability.IdentDistrib

/-! # Time reversal and first-exit ball probabilities -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Time reversal identifies the directional closed-ball failure events. -/
theorem forwardExitBallFailure_eq_backward_of_reverse {β : Type*} {d : ℕ}
    (f g : β → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (h : ∀ ω t, g ω t = f ω (-t)) (ε : ℝ) (k : ℤ) :
    forwardExitBallFailure g ε k = backwardExitBallFailure f ε k := by
  ext ω
  have hclock :
      (fun (s : ℝ≥0) (_ : Unit) => g ω (0 + (s : ℝ))) =
        (fun (s : ℝ≥0) (_ : Unit) => f ω (0 - (s : ℝ))) := by
    funext s u
    simp only [zero_add, zero_sub, h]
  let A : Set ℝ := {t | t ≤ 0 ∧ f ω t ∉ ball 0 (Real.exp (k : ℝ))}
  have htimes : {t : ℝ | 0 ≤ t ∧ g ω t ∉ ball 0 (Real.exp (k : ℝ))} = -A := by
    ext t
    simp only [mem_ofPred_eq, mem_neg, A, h, neg_nonpos]
  have hendpoint :
      sInf {t : ℝ | 0 ≤ t ∧ g ω t ∉ ball 0 (Real.exp (k : ℝ))} = -sSup A := by
    rw [htimes, Real.sInf_neg]
  have htrace : g ω '' Icc 0 (-sSup A) = f ω '' Icc (sSup A) 0 := by
    ext x
    constructor
    · rintro ⟨t, ⟨ht₀, ht⟩, rfl⟩
      refine ⟨-t, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · exact (h ω t).symm
    · rintro ⟨t, ⟨ht, ht₀⟩, rfl⟩
      refine ⟨-t, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · simpa only [neg_neg] using h ω (-t)
  simp only [forwardExitBallFailure, backwardExitBallFailure, mem_ofPred_eq]
  rw [hclock, hendpoint, htrace]

/-- A measurable random curve has a measurable forward closed-ball failure event. -/
theorem measurableSet_forwardExitBallFailure {β : Type*} [MeasurableSpace β] {d : ℕ}
    {f : β → C(ℝ, EuclideanSpace ℝ (Fin d))} (hf : Measurable f)
    (ε : ℝ) (k : ℤ) : MeasurableSet (forwardExitBallFailure f ε k) := by
  exact (measurableSet_forward_firstExitTrace_contains_closedBall hf
    (measurable_const : Measurable (fun _ : β => ε * Real.exp (k : ℝ) / 2))
    (ball 0 (Real.exp (k : ℝ))) isOpen_ball 0).compl

/-- A reversed curve and a forward reference curve with the same law have matching failure probabilities. -/
theorem measure_backwardExitBallFailure_eq_of_identDistrib_reverse
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ] {d : ℕ}
    (μ : Measure β) (ν : Measure γ)
    (f g : β → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (η : γ → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (hrev : ∀ ω t, g ω t = f ω (-t))
    (hlaw : IdentDistrib g η μ ν) (ε : ℝ) (k : ℤ) :
    μ (backwardExitBallFailure f ε k) = ν (forwardExitBallFailure η ε k) := by
  rw [← forwardExitBallFailure_eq_backward_of_reverse f g hrev ε k]
  exact hlaw.measure_mem_eq (measurableSet_forwardExitBallFailure measurable_id ε k)

/-- A forward open-ball estimate transfers to the backward closed-ball event under a reversed law. -/
theorem measure_backwardExitBallFailure_le_of_identDistrib_reverse
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ] {d : ℕ}
    (μ : Measure β) (ν : Measure γ)
    (f g : β → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (η : γ → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (hrev : ∀ ω t, g ω t = f ω (-t))
    (hlaw : IdentDistrib g η μ ν) {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    μ (backwardExitBallFailure f ε k) ≤ ν (forwardExitOpenBallFailure η ε k) := by
  rw [measure_backwardExitBallFailure_eq_of_identDistrib_reverse μ ν f g η hrev hlaw ε k]
  exact measure_mono (forwardExitBallFailure_subset_open η hε k)

end LatticeProb
