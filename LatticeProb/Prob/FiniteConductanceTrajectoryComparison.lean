import LatticeProb.Prob.FiniteConductanceTrajectoryInclusion

/-! # Comparing stopped walks in finite conductance regions -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

open BouRabeeGwynne.FiniteConductanceNetwork

/-- Two finite restrictions retaining their active neighbors have the same
stopped trajectory law after embedding in their union. -/
theorem finiteConductanceRestriction_trajectoryLaw_union
    {V : Type*} (c : V → V → ℝ)
    (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (R S : Set V) [Fintype R] [Fintype S] [Fintype ↥(R ∪ S)] (B : Set V)
    [MeasurableSpace R] [MeasurableSingletonClass R]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace ↥(R ∪ S)] [MeasurableSingletonClass ↥(R ∪ S)]
    (hretainR : ∀ v : R, (v : V) ∈ B → ∀ w, w ∉ R → c v w = 0)
    (hretainS : ∀ v : S, (v : V) ∈ B → ∀ w, w ∉ S → c v w = 0)
    (hR : ∀ v ∈ (Subtype.val ⁻¹' B : Set R),
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (hS : ∀ v ∈ (Subtype.val ⁻¹' B : Set S),
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop S).totalConductance v)
    (v : R) (u : S) (hvu : (v : V) = u) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw
      (Subtype.val ⁻¹' B) hR v).map
        (fun ω n => finiteRegionInclusion (S := R ∪ S) Set.subset_union_left (ω n)) =
    ((finiteConductanceRestriction c hsymm hnonneg hloop S).trajectoryLaw
      (Subtype.val ⁻¹' B) hS u).map
        (fun ω n => finiteRegionInclusion (S := R ∪ S) Set.subset_union_right (ω n)) := by
  have hU : ∀ x ∈ (Subtype.val ⁻¹' B : Set ↥(R ∪ S)),
      0 < (finiteConductanceRestriction c hsymm hnonneg hloop (R ∪ S)).totalConductance x := by
    intro x hx
    rcases x.property with hxR | hxS
    · let y : R := ⟨x, hxR⟩
      have hzero : ∀ w, w ∉ R ∪ S → c x w = 0 := by
        intro w hw
        exact hretainR y hx w (fun hwR => hw (Or.inl hwR))
      rw [finiteConductanceRestriction_total c hsymm hnonneg hloop (R ∪ S) x hzero]
      rw [← finiteConductanceRestriction_total c hsymm hnonneg hloop R y (hretainR y hx)]
      exact hR y hx
    · let y : S := ⟨x, hxS⟩
      have hzero : ∀ w, w ∉ R ∪ S → c x w = 0 := by
        intro w hw
        exact hretainS y hx w (fun hwS => hw (Or.inr hwS))
      rw [finiteConductanceRestriction_total c hsymm hnonneg hloop (R ∪ S) x hzero]
      rw [← finiteConductanceRestriction_total c hsymm hnonneg hloop S y (hretainS y hx)]
      exact hS y hx
  rw [finiteConductanceRestriction_trajectoryLaw_inclusion c hsymm hnonneg hloop
      R (R ∪ S) Set.subset_union_left B hretainR hR hU v,
    finiteConductanceRestriction_trajectoryLaw_inclusion c hsymm hnonneg hloop
      S (R ∪ S) Set.subset_union_right B hretainS hS hU u]
  congr 1
  exact Subtype.ext hvu

end LatticeProb
