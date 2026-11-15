import LatticeProb.LQG.HullDiscreteFieldCode

/-! # Locally gated phase observations on dyadic hulls -/

set_option autoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The anchor phase is recorded only when its support lies inside the hull. -/
def localHullFieldPhase {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (ψ : TestC) {p : ℝ} (hp : 0 < p) : Ω → ℝ :=
  ({ω | tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))} : Set Ω).indicator
    (fun ω => toIcoMod hp 0 (h ω ψ))

/-- Mean-zero hull observations together with the locally gated anchor phase. -/
def localHullFieldSigma {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (ψ : TestC) {p : ℝ} (hp : 0 < p) : MeasurableSpace Ω :=
  hullSigma0 h A n ⊔ MeasurableSpace.comap (localHullFieldPhase h A n ψ hp) inferInstance

/-- Local phase observations require no more information than the hull and the
unconditionally adjoined anchor phase. -/
theorem localHullFieldSigma_le {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ) (ψ : TestC)
    {p : ℝ} (hp : 0 < p) :
    localHullFieldSigma h A n ψ hp ≤ hullDiscreteFieldSigma h A n ψ hp := by
  apply sup_le le_sup_left
  apply Measurable.comap_le
  let : MeasurableSpace Ω := hullDiscreteFieldSigma h A n ψ hp
  exact (show Measurable (fun ω => toIcoMod hp 0 (h ω ψ)) from
    (comap_measurable _).mono le_sup_right le_rfl).indicator
      ((le_sup_left : hullSigma0 h A n ≤ hullDiscreteFieldSigma h A n ψ hp) _
        (measurableSet_subset_interior_dyadicHull h A hA n _))

/-- The phase of the anchor is zero when the anchor is not supported in the hull. -/
theorem localHullFieldPhase_eq_zero {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (ψ : TestC) {p : ℝ} (hp : 0 < p) (ω : Ω)
    (hψ : ¬ tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))) :
    localHullFieldPhase h A n ψ hp ω = 0 := by
  exact Set.indicator_of_notMem hψ _

/-- A phase gated by containment of both supports is observable from the
locally gated phase and the hull observation. -/
theorem measurable_hull_joint_gated_phase {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ ψ : TestC) {p : ℝ} (hp : 0 < p) :
    Measurable[localHullFieldSigma h A n ψ hp] (fun ω =>
      ({ω | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω))} : Set Ω).indicator
        (fun ω => toIcoMod hp 0 (h ω ψ)) ω) := by
  classical
  let E : Set Ω := {ω | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
    interior (dyadicHull n (A ω))}
  let F : Set Ω := {ω | tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))}
  have hEF : E ⊆ F := fun ω hω => subset_union_right.trans hω
  let : MeasurableSpace Ω := localHullFieldSigma h A n ψ hp
  have hE : MeasurableSet E :=
    (le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n ψ hp) _
      (measurableSet_subset_interior_dyadicHull h A hA n _)
  have hm : Measurable (E.indicator (localHullFieldPhase h A n ψ hp)) :=
    ((comap_measurable _).mono le_sup_right le_rfl).indicator hE
  have heq : E.indicator (localHullFieldPhase h A n ψ hp) =
      E.indicator (fun ω => toIcoMod hp 0 (h ω ψ)) := by
    funext ω
    by_cases hω : ω ∈ E
    · have hf : ω ∈ F := hEF hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact Set.indicator_of_mem hf _
    · simp [hω]
  rw [heq] at hm
  exact hm

/-- The centered coordinate is also observable from the local phase sigma algebra. -/
theorem measurable_hull_joint_gated_centered {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ ψ : TestC) (hψ : ∫ z, ψ z = 1) {p : ℝ} (hp : 0 < p) :
    Measurable[localHullFieldSigma h A n ψ hp] (fun ω =>
      ({ω | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω))} : Set Ω).indicator
        (fun ω => h ω φ - (∫ z, φ z) * h ω ψ) ω) :=
  (measurable_hull_gated_centered_pairing h A hA n φ ψ hψ).mono le_sup_left le_rfl

end LatticeProb.LQG
