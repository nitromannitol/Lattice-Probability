import LatticeProb.Prob.CombinedExitTransform

/-! # Exit endpoints under spatial maps and clock changes -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A continuous spatial map and increasing clock transform a finite exit
endpoint into the image of the original endpoint. -/
theorem openExit_endpoint_comp_spatial_orderIso
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (w : C(ℝ≥0, E)) (f : C(E, F)) (φ : ℝ≥0 ≃o ℝ≥0)
    (V : Set F) (hV : IsOpen V)
    (hfin : openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) () ≠ ⊤) :
    f (w (φ (openExitTime (fun t (_ : Unit) => f (w (φ t))) V ()).toNNReal)) =
      f (w (openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) ()).toNNReal) := by
  have hf : openExitTime (fun t (_ : Unit) => f (w t)) V () ≠ ⊤ := by
    simpa only [openExitTime_comp_spatial] using hfin
  rw [openExitTime_comp_orderIso_toNNReal (fun t => f (w t)) V φ hV
    (f.continuous.comp w.continuous) hf, φ.apply_symm_apply,
    openExitTime_comp_spatial]

end LatticeProb
