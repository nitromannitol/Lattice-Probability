import LatticeProb.Prob.FiniteConductanceRegionIndependence

/-! # Stopped step laws in finite conductance regions -/

set_option autoImplicit false

namespace LatticeProb

open BouRabeeGwynne.FiniteConductanceNetwork

/-- At a common vertex, finite stopped walks have the same ambient step law
when active membership agrees and active conductance neighbors are retained. -/
theorem finiteConductanceRestriction_stoppedStepPMF_map_eq
    {V : Type*} (c : V → V → ℝ)
    (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (R S : Set V) [Fintype R] [Fintype S] (A : Set R) (B : Set S)
    (hR : ∀ v ∈ A,
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (hS : ∀ v ∈ B,
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop S).totalConductance v)
    (v : R) (u : S) (hvu : (v : V) = u) (hactive : v ∈ A ↔ u ∈ B)
    (hretainR : v ∈ A → ∀ w, w ∉ R → c v w = 0)
    (hretainS : u ∈ B → ∀ w, w ∉ S → c u w = 0) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF A hR v).map
        Subtype.val =
      ((finiteConductanceRestriction c hsymm hnonneg hloop S).stepPMF B hS u).map
        Subtype.val := by
  by_cases hv : v ∈ A
  · have hu := hactive.mp hv
    exact finiteConductanceRestriction_stepPMF_map_eq_of_retains c hsymm hnonneg hloop
      R S A B hR hS v u hvu hv hu (hretainR hv) (hretainS hu)
  · have hu : u ∉ B := fun h => hv (hactive.mpr h)
    rw [(finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF_of_not_mem A hR hv,
      (finiteConductanceRestriction c hsymm hnonneg hloop S).stepPMF_of_not_mem B hS hu,
      PMF.pure_map, PMF.pure_map, hvu]

end LatticeProb
