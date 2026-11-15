import LatticeProb.Bonanno.BouRabeeGwynne.FiniteExit
import LatticeProb.Walk.SourceStoppedCurveFinalEdge
import LatticeProb.Walk.AmbientRestrictedExitEdges

/-! # Exterior hitting for finite restricted walks -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory MatedCRTHarmonic.Markov
open BouRabeeGwynne.FiniteConductanceNetwork

namespace LatticeProb

/-- A finite restricted walk whose active region has accessible boundary hits
its ambient exterior almost surely. -/
theorem finiteConductanceRestriction_map_ae_exterior_hit
    {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (c : V → V → ℝ) (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (R : Set V) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R) (B : Set V) (hAB : ∀ v : R, v ∈ A ↔ (v : V) ∈ B)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (haccess : (finiteConductanceRestriction c hsymm hnonneg hloop R).BoundaryAccessible A)
    (v : R) :
    ∀ᵐ ω ∂((finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw A hA v).map
        (fun p n => (p n : V)), hitTime Bᶜ ω ≠ ⊤ := by
  have hmap : Measurable (fun p : ℕ → R => fun n => (p n : V)) :=
    Measurable.of_eval fun n => (measurable_of_countable (fun x : R => (x : V))).comp
      (measurable_pi_apply n)
  have htarget : MeasurableSet {ω : ℕ → V | hitTime Bᶜ ω ≠ ⊤} :=
    (measurableSet_hitTime_eq_top (Set.to_countable _).measurableSet).compl
  apply (ae_map_iff hmap.aemeasurable htarget).2
  filter_upwards [(finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw_ae_finiteExit
    A hA haccess v] with p hp
  rw [exitTime_eq_hitTime_compl] at hp
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hp
  apply hitTime_ne_top_iff.mpr
  exact ⟨n, fun h => hn ((hAB (p n)).2 h)⟩

end LatticeProb
end
