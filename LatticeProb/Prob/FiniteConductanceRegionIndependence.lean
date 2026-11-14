import LatticeProb.Prob.FiniteConductanceStepLaw

/-! # Independence of finite conductance regions

Finite restrictions have the same ambient step law at an active vertex when
both retain its conductance neighbors.
-/

set_option autoImplicit false

namespace LatticeProb

open BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} (c : V → V → ℝ)
variable (hsymm : ∀ v w, c v w = c w v)
variable (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)

/-- The ambient mass of an active finite step is the normalized ambient
conductance, including at vertices outside the finite restriction. -/
theorem finiteConductanceRestriction_stepPMF_map_apply_ambient
    (R : Set V) [Fintype R] (A : Set R)
    (hpos : ∀ v ∈ A,
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (v : R) (hv : v ∈ A) (hretain : ∀ w, w ∉ R → c v w = 0) (w : V) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF A hpos v).map
      Subtype.val w = ENNReal.ofReal (c v w / (∑' z, c v z)) := by
  classical
  by_cases hw : w ∈ R
  · exact finiteConductanceRestriction_stepPMF_map_apply c hsymm hnonneg hloop R A hpos
      v ⟨w, hw⟩ hv hretain
  · rw [finiteConductanceRestriction_stepPMF_map_apply_of_not_mem c hsymm hnonneg hloop
      R A hpos v hw, hretain w hw, zero_div, ENNReal.ofReal_zero]

/-- Two finite restrictions retaining the same vertex's neighbors give the
same ambient one-step distribution at that vertex. -/
theorem finiteConductanceRestriction_stepPMF_map_eq_of_retains
    (R S : Set V) [Fintype R] [Fintype S] (A : Set R) (B : Set S)
    (hR : ∀ v ∈ A,
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (hS : ∀ v ∈ B,
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop S).totalConductance v)
    (v : R) (u : S) (hvu : (v : V) = u) (hv : v ∈ A) (hu : u ∈ B)
    (hretainR : ∀ w, w ∉ R → c v w = 0)
    (hretainS : ∀ w, w ∉ S → c u w = 0) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF A hR v).map
        Subtype.val =
      ((finiteConductanceRestriction c hsymm hnonneg hloop S).stepPMF B hS u).map
        Subtype.val := by
  ext w
  rw [finiteConductanceRestriction_stepPMF_map_apply_ambient c hsymm hnonneg hloop
      R A hR v hv hretainR w,
    finiteConductanceRestriction_stepPMF_map_apply_ambient c hsymm hnonneg hloop
      S B hS u hu hretainS w, hvu]

end LatticeProb
