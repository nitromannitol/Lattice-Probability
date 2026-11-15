import LatticeProb.Walk.ActiveConductanceStep
import LatticeProb.Prob.FiniteConductanceRestriction
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-! # Edges of a restricted walk before exit -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory MatedCRTHarmonic.Markov

namespace LatticeProb

/-- Before its first exit from an ambient set, a restricted conductance walk
follows positive ambient conductance edges, provided its active set is the
restriction of that set. The exit time may be infinite. -/
theorem finiteConductanceRestriction_ae_pos_before_exit
    {V : Type*} (c : V → V → ℝ)
    (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (R : Set V) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R) (B : Set V) (hAB : ∀ v : R, v ∈ A ↔ (v : V) ∈ B)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (v : R) :
    ∀ᵐ ω ∂(finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw A hA v,
      ∀ j : ℕ, (j : ℕ∞) < hitTime Bᶜ (fun n => (ω n : V)) →
        0 < c (ω j) (ω (j + 1)) := by
  filter_upwards [(finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw_ae_pos_of_mem A hA v] with ω hω
  intro j hj
  have hjB : (ω j : V) ∈ B := by
    exact not_not.mp (notMem_of_lt_hitTime hj)
  exact hω j ((hAB (ω j)).2 hjB)

end LatticeProb
end
