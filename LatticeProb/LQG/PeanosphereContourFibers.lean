import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Topology.FiberSharedFrontierArc

/-! # Peanosphere curves with the same contour -/

set_option autoImplicit false

open Set Function Topology
open scoped unitInterval

namespace LatticeProb

open MatedCRTHarmonic MatedCRTHarmonic.RouteM

/-- Two Peanosphere curves with the same contour identify precisely the same times. -/
theorem Peanosphere.same_fibers {w : MatedCRT.Path2} {η ξ : ℝ → ℂ}
    (hη : Peanosphere w η) (hξ : Peanosphere w ξ) (s t : ℝ) :
    η s = η t ↔ ξ s = ξ t := by
  constructor
  · intro h
    exact eta_eq_of_eqvGen hξ (hη.onlyMerge s t h)
  · intro h
    exact eta_eq_of_eqvGen hη (hξ.onlyMerge s t h)

/-- The common contour determines the curve up to a parameter-preserving
homeomorphism of the plane. -/
theorem Peanosphere.exists_homeomorph {w : MatedCRT.Path2} {η ξ : ℝ → ℂ}
    (hη : Peanosphere w η) (hξ : Peanosphere w ξ) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ t, e (η t) = ξ t := by
  have hpη : IsProperMap η := isProperMap_iff_tendsto_cocompact.2 ⟨hη.cont, hη.transient⟩
  have hpξ : IsProperMap ξ := isProperMap_iff_tendsto_cocompact.2 ⟨hξ.cont, hξ.transient⟩
  obtain ⟨e, he, _⟩ := exists_homeomorph_of_proper_maps_same_fibers_components
    η ξ hpη hpξ hη.surj hξ.surj (Peanosphere.same_fibers hη hξ)
  exact ⟨e, he⟩

/-- Shared frontier arcs of images of the same time sets are preserved between
Peanosphere curves with a common contour. -/
theorem Peanosphere.shared_frontier_arc_iff {w : MatedCRT.Path2} {η ξ : ℝ → ℂ}
    (hη : Peanosphere w η) (hξ : Peanosphere w ξ) (A B : Set ℝ) :
    (∃ p : C(unitInterval, ℂ), Injective p ∧
      (∀ t, p t ∈ frontier (ξ '' A)) ∧ (∀ t, p t ∈ frontier (ξ '' B))) ↔
    (∃ p : C(unitInterval, ℂ), Injective p ∧
      (∀ t, p t ∈ frontier (η '' A)) ∧ (∀ t, p t ∈ frontier (η '' B))) := by
  have hpη : IsProperMap η := isProperMap_iff_tendsto_cocompact.2 ⟨hη.cont, hη.transient⟩
  have hpξ : IsProperMap ξ := isProperMap_iff_tendsto_cocompact.2 ⟨hξ.cont, hξ.transient⟩
  exact exists_shared_frontier_arc_of_proper_maps_same_fibers_iff
    η ξ hpη hpξ hη.surj hξ.surj (Peanosphere.same_fibers hη hξ) A B

end LatticeProb
