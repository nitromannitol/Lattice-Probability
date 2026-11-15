import LatticeProb.LQG.HullGatedPairing
import LatticeProb.LQG.HullContainmentEvent
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

/-! # Centered field observations in random dyadic hulls -/

set_option autoImplicit false

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A centered pairing is observable when both test supports lie in the hull. -/
theorem measurable_hull_gated_centered_pairing {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ ψ : TestC) (hψ : ∫ z, ψ z = 1) :
    Measurable[hullSigma0 h A n] (fun ω =>
      ({ω | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
        interior (dyadicHull n (A ω))} : Set Ω).indicator
        (fun ω => h ω φ - (∫ z, φ z) * h ω ψ) ω) := by
  classical
  let θ : TestC := φ - (∫ z, φ z) • ψ
  let E : Set Ω := {ω | tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
    interior (dyadicHull n (A ω))}
  let F : Set Ω := {ω | tsupport (θ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))}
  have hθ0 : ∫ z, θ z = 0 := LQGMetric.GFFLaw.integral_sub_smul hψ φ
  have hsupport : tsupport (θ : ℂ → ℝ) ⊆
      tsupport (φ : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) := by
    have he : (θ : ℂ → ℝ) = fun x => φ x - (∫ z, φ z) * ψ x := by
      ext x
      simp [θ]
    rw [he]
    exact (tsupport_sub _ _).trans (union_subset_union_right _ tsupport_mul_subset_right)
  have hEF : E ⊆ F := fun ω hω => hsupport.trans hω
  have hE : MeasurableSet[hullSigma0 h A n] E :=
    measurableSet_subset_interior_dyadicHull h A hA n _
  have hm := (measurable_hull_gated_pairing h A hA n θ hθ0).indicator hE
  have heq : (fun ω => E.indicator (F.indicator (fun ω => h ω θ)) ω) =
      (fun ω => E.indicator (fun ω => h ω φ - (∫ z, φ z) * h ω ψ) ω) := by
    funext ω
    by_cases hω : ω ∈ E
    · have hf : ω ∈ F := hEF hω
      simp only [Set.indicator_of_mem hω, Set.indicator_of_mem hf]
      simp only [θ, map_sub, map_smul, smul_eq_mul]
    · simp only [Set.indicator_of_notMem hω]
  change Measurable[hullSigma0 h A n]
    (fun ω => E.indicator (F.indicator (fun ω => h ω θ)) ω) at hm
  rw [heq] at hm
  exact hm

end LatticeProb.LQG
