import LatticeProb.Prob.FiniteConductanceRestriction

/-! # Ambient step laws for finite conductance restrictions -/

set_option autoImplicit false

namespace LatticeProb

open BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} (c : V → V → ℝ)
variable (hsymm : ∀ v w, c v w = c w v)
variable (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
variable (R : Set V) [Fintype R] (A : Set R)
variable (hpos : ∀ v ∈ A,
  0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)

/-- The ambient image of an active finite step has the ambient conductance row. -/
theorem finiteConductanceRestriction_stepPMF_map_apply (v w : R) (hv : v ∈ A)
    (hretain : ∀ z, z ∉ R → c v z = 0) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF A hpos v).map
      Subtype.val w = ENNReal.ofReal (c v w / (∑' z, c v z)) := by
  classical
  rw [PMF.map_apply]
  simp only [Subtype.val_inj]
  rw [tsum_eq_single w]
  · rw [ite_eq_left rfl, stepPMF_apply,
      finiteConductanceRestriction_transition c hsymm hnonneg hloop R A v w hv hretain]
  · intro b hb
    simp [Ne.symm hb]

/-- The ambient image of a finite step is supported on the region. -/
theorem finiteConductanceRestriction_stepPMF_map_apply_of_not_mem (v : R) {w : V}
    (hw : w ∉ R) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF A hpos v).map
      Subtype.val w = 0 := by
  classical
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  exact ite_eq_right (fun (h : w = (z : V)) => hw (h.symm ▸ z.property))

/-- An ambient step with the same retained probabilities and no mass outside the
region is the pushforward of the finite restricted step. -/
theorem finiteConductanceRestriction_stepPMF_map_eq (v : R) (hv : v ∈ A)
    (hretain : ∀ z, z ∉ R → c v z = 0) (p : PMF V)
    (hinside : ∀ w : R, p w = ENNReal.ofReal (c v w / (∑' z, c v z)))
    (houtside : ∀ w ∉ R, p w = 0) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF A hpos v).map
      Subtype.val = p := by
  ext w
  by_cases hw : w ∈ R
  · let wR : R := ⟨w, hw⟩
    exact (finiteConductanceRestriction_stepPMF_map_apply c hsymm hnonneg hloop R A hpos
      v wR hv hretain).trans (hinside wR).symm
  · rw [finiteConductanceRestriction_stepPMF_map_apply_of_not_mem c hsymm hnonneg hloop
      R A hpos v hw, houtside w hw]

end LatticeProb
