import LatticeProb.LQG.LocalHullFieldPhase

/-! # Gated restrictions of field observations on random hulls -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A set-measurable support gate contained in a random hull allows the
corresponding centered pairing and the anchor phase to be read from the hull. -/
theorem measurable_gated_restriction_of_localHullFieldSigma {Ω : Type} {I : Type*}
    (h : Ω → DistC) (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω))
    (n : ℕ) (φ : I → TestC) (ψ : TestC) (hψ : ∫ z, ψ z = 1)
    (E : I → Set Ω) (hE : ∀ i, MeasurableSet[setSigma A] (E i))
    (hφ : ∀ i ω, ω ∈ E i → tsupport (φ i : ℂ → ℝ) ⊆
      interior (dyadicHull n (A ω)))
    (hsupp : ∀ ω, tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)))
    {p : ℝ} (hp : 0 < p) :
    Measurable[localHullFieldSigma h A n ψ hp] (fun (ω : Ω) =>
      ((fun i => ((E i).indicator (fun _ => (1 : ℝ)) ω,
        (E i).indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ) ω)),
       toIcoMod hp 0 (h ω ψ))) := by
  classical
  let : MeasurableSpace Ω := localHullFieldSigma h A n ψ hp
  have hset : setSigma A ≤ localHullFieldSigma h A n ψ hp :=
    (le_sup_left : setSigma A ≤ hullSigma0 h A n).trans le_sup_left
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    have hEi : MeasurableSet (E i) := hset _ (hE i)
    apply Measurable.prodMk (measurable_const.indicator hEi)
    let F : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
      interior (dyadicHull n (A ω))}
    have hEF : E i ⊆ F := fun ω hω => union_subset (hφ i ω hω) (hsupp ω)
    have hm := (measurable_hull_joint_gated_centered h A hA n (φ i) ψ hψ hp).indicator hEi
    have heq : (fun ω => (E i).indicator (F.indicator
        (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ)) ω) =
        (fun ω => (E i).indicator
          (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ) ω) := by
      funext ω
      by_cases hω : ω ∈ E i
      · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hEF hω)]
      · simp only [Set.indicator_of_notMem hω]
    change Measurable (fun ω => (E i).indicator (F.indicator
      (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ)) ω) at hm
    rwa [heq] at hm
  · have hm : Measurable (localHullFieldPhase h A n ψ hp) :=
      (comap_measurable _).mono le_sup_right le_rfl
    have heq : localHullFieldPhase h A n ψ hp = fun ω => toIcoMod hp 0 (h ω ψ) := by
      funext ω
      exact Set.indicator_of_mem (hsupp ω) _
    rwa [heq] at hm

end LatticeProb.LQG
