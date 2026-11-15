import LatticeProb.Topology.FirstExitBallOpen

/-! # Reversal of directional first-exit traces -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Time reversal identifies the forward and backward open-ball failure events. -/
theorem forwardExitOpenBallFailure_eq_backward_of_reverse {β : Type*} {d : ℕ}
    (f g : β → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (h : ∀ ω t, g ω t = f ω (-t)) (ε : ℝ) (k : ℤ) :
    forwardExitOpenBallFailure g ε k = backwardExitOpenBallFailure f ε k := by
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
  simp only [forwardExitOpenBallFailure, backwardExitOpenBallFailure, mem_ofPred_eq]
  rw [hclock, hendpoint, htrace]

end LatticeProb
