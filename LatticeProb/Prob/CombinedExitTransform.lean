import LatticeProb.Prob.SpatialExitObservation
import LatticeProb.Prob.StoppedExitTimeChange

/-! # Spatial maps and deterministic clock changes at open-set exits -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A spatial map and an increasing change of clock commute with stopping at
an open-set exit, provided the original exit from the preimage is finite. -/
theorem stoppedPath_openExit_comp_spatial_orderIso
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (w : C(ℝ≥0, E)) (f : C(E, F)) (φ : ℝ≥0 ≃o ℝ≥0)
    (V : Set F) (hV : IsOpen V)
    (hfin : openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) () ≠ ⊤) :
    let v := (f.comp w).comp ⟨φ, φ.continuous⟩
    stoppedPath (openExitTime (fun t (_ : Unit) => v t) V ()) v =
      (f.comp (stoppedPath (openExitTime (fun t (_ : Unit) => w t)
        (f ⁻¹' V) ()) w)).comp ⟨φ, φ.continuous⟩ := by
  dsimp only
  have hf : openExitTime (fun t (_ : Unit) => (f.comp w) t) V () ≠ ⊤ := by
    simpa only [ContinuousMap.coe_comp, Function.comp_apply, openExitTime_comp_spatial] using hfin
  rw [stoppedPath_openExit_comp_orderIso (f.comp w) V φ hV hf]
  exact congrArg (fun q : C(ℝ≥0, F) => q.comp ⟨φ, φ.continuous⟩)
    (stoppedPath_openExit_comp_spatial w f V)

/-- A spatial map and an increasing change of clock transform a trace between
finite open-set exits into the image of the original trace. -/
theorem openExit_segment_comp_spatial_orderIso
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (w : C(ℝ≥0, E)) (f : C(E, F)) (φ : ℝ≥0 ≃o ℝ≥0)
    (U V : Set F) (hU : IsOpen U) (hV : IsOpen V)
    (hUfin : openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' U) () ≠ ⊤)
    (hVfin : openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) () ≠ ⊤) :
    (fun t => f (w (φ t))) '' Icc
      (openExitTime (fun t (_ : Unit) => f (w (φ t))) U ()).toNNReal
      (openExitTime (fun t (_ : Unit) => f (w (φ t))) V ()).toNNReal =
    f '' (w '' Icc
      (openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' U) ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w t) (f ⁻¹' V) ()).toNNReal) := by
  have hUf : openExitTime (fun t (_ : Unit) => (f.comp w) t) U () ≠ ⊤ := by
    simpa only [ContinuousMap.coe_comp, Function.comp_apply, openExitTime_comp_spatial] using hUfin
  have hVf : openExitTime (fun t (_ : Unit) => (f.comp w) t) V () ≠ ⊤ := by
    simpa only [ContinuousMap.coe_comp, Function.comp_apply, openExitTime_comp_spatial] using hVfin
  calc
    _ = (fun t => f (w t)) '' Icc
        (openExitTime (fun t (_ : Unit) => f (w t)) U ()).toNNReal
        (openExitTime (fun t (_ : Unit) => f (w t)) V ()).toNNReal := by
      simpa only [ContinuousMap.coe_comp, Function.comp_apply] using
        (openExit_segment_comp_orderIso (f.comp w) U V φ hU hV hUf hVf)
    _ = _ := openExit_segment_comp_spatial w f U V

end LatticeProb
