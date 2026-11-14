import LatticeProb.Prob.FiniteConductanceStoppedRegion
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedWalk
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling

/-! # Trajectories in finite conductance regions -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

open BouRabeeGwynne.FiniteConductanceNetwork

private theorem pmf_map_injective {X Y : Type*} (f : X → Y) (hf : Function.Injective f)
    {p q : PMF X} (h : p.map f = q.map f) : p = q := by
  classical
  ext x
  have heval (r : PMF X) : r.map f (f x) = r x := by
    rw [PMF.map_apply]
    simp only [hf.eq_iff]
    simp
  rw [← heval p, ← heval q, h]

/-- The inclusion of a finite region in a larger one. -/
def finiteRegionInclusion {V : Type*} {R S : Set V} (hRS : R ⊆ S) : R → S :=
  fun v => ⟨v, hRS v.property⟩

variable {V : Type*} (c : V → V → ℝ)
variable (hsymm : ∀ v w, c v w = c w v)
variable (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
variable (R S : Set V) [Fintype R] [Fintype S] (hRS : R ⊆ S) (B : Set V)
variable (hretain : ∀ v : R, (v : V) ∈ B → ∀ w, w ∉ R → c v w = 0)
variable (hR : ∀ v ∈ (Subtype.val ⁻¹' B : Set R),
  0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
variable (hS : ∀ v ∈ (Subtype.val ⁻¹' B : Set S),
  0 < (finiteConductanceRestriction c hsymm hnonneg hloop S).totalConductance v)

include hretain in
/-- Inclusion intertwines stopped transition probabilities when all active
neighbors are retained by the smaller region. -/
theorem finiteConductanceRestriction_stepPMF_inclusion (v : R) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF
      (Subtype.val ⁻¹' B) hR v).map (finiteRegionInclusion hRS) =
    (finiteConductanceRestriction c hsymm hnonneg hloop S).stepPMF
      (Subtype.val ⁻¹' B) hS (finiteRegionInclusion hRS v) := by
  apply pmf_map_injective (Subtype.val : S → V) Subtype.val_injective
  rw [PMF.map_comp]
  exact finiteConductanceRestriction_stoppedStepPMF_map_eq c hsymm hnonneg hloop
    R S (Subtype.val ⁻¹' B) (Subtype.val ⁻¹' B) hR hS v (finiteRegionInclusion hRS v)
    rfl Iff.rfl (hretain v) (fun hv w hw => hretain v hv w (fun hwR => hw (hRS hwR)))

variable [MeasurableSpace R] [MeasurableSingletonClass R]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

include hretain in
/-- A stopped conductance walk has the same whole trajectory law when its
finite region is enlarged without losing any active neighbor. -/
theorem finiteConductanceRestriction_trajectoryLaw_inclusion (v : R) :
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw
      (Subtype.val ⁻¹' B) hR v).map (fun ω n => finiteRegionInclusion hRS (ω n)) =
    (finiteConductanceRestriction c hsymm hnonneg hloop S).trajectoryLaw
      (Subtype.val ⁻¹' B) hS (finiteRegionInclusion hRS v) := by
  apply BouRabeeGwynne.TrajectoryCoupling.map_trajectory_law (Measure.dirac v)
    ((finiteConductanceRestriction c hsymm hnonneg hloop R).historyKernel (Subtype.val ⁻¹' B) hR)
    (Measure.dirac (finiteRegionInclusion hRS v))
    ((finiteConductanceRestriction c hsymm hnonneg hloop S).historyKernel (Subtype.val ⁻¹' B) hS)
    (finiteRegionInclusion hRS) (measurable_of_finite _)
  · exact Measure.map_dirac' (measurable_of_finite _) _
  · intro n h
    change ((finiteConductanceRestriction c hsymm hnonneg hloop R).stepPMF
      (Subtype.val ⁻¹' B) hR (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure.map
        (finiteRegionInclusion hRS) = _
    rw [PMF.toMeasure_map _ _ (measurable_of_finite _),
      finiteConductanceRestriction_stepPMF_inclusion c hsymm hnonneg hloop R S hRS B
        hretain hR hS]
    rfl

end LatticeProb
