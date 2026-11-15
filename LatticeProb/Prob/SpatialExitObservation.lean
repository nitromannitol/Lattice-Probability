import LatticeProb.Prob.BrownianOpenExit
import LatticeProb.Prob.ContinuousStoppedPath

/-! # Spatial maps of stopped paths and exit segments -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A spatial map preserves the exit time from the preimage of a set. -/
theorem openExitTime_comp_spatial {E F : Type*} (w : ℝ≥0 → E)
    (f : E → F) (V : Set F) :
    openExitTime (fun t (_ : Unit) => f (w t)) V () =
      openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) () := rfl

/-- A continuous spatial map commutes with stopping, including at infinity. -/
theorem stoppedPath_comp_spatial {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (w : C(ℝ≥0, E)) (f : C(E, F)) (T : ℝ≥0∞) :
    stoppedPath T (f.comp w) = f.comp (stoppedPath T w) := by
  ext t
  simp only [stoppedPath_apply, ContinuousMap.coe_comp, Function.comp_apply]

/-- The stopped observation of a transformed path is the transformed observation. -/
theorem stoppedPath_openExit_comp_spatial {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (w : C(ℝ≥0, E)) (f : C(E, F)) (V : Set F) :
    stoppedPath (openExitTime (fun t (_ : Unit) => f (w t)) V ()) (f.comp w) =
      f.comp (stoppedPath (openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) ()) w) := by
  rw [openExitTime_comp_spatial]
  exact stoppedPath_comp_spatial w f _

/-- The trace between two exits is mapped to the corresponding transformed trace. -/
theorem openExit_segment_comp_spatial {E F : Type*} (w : ℝ≥0 → E)
    (f : E → F) (U V : Set F) :
    (fun t => f (w t)) '' Icc
      (openExitTime (fun t (_ : Unit) => f (w t)) U ()).toNNReal
      (openExitTime (fun t (_ : Unit) => f (w t)) V ()).toNNReal =
    f '' (w '' Icc
      (openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' U) ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) ()).toNNReal) := by
  rw [openExitTime_comp_spatial, openExitTime_comp_spatial, ← Set.image_comp]
  rfl

end LatticeProb
