import LatticeProb.LQG.HullCenteredObservation
import LatticeProb.Prob.UniformModShift

/-! # Discrete-period field observations on random dyadic hulls -/

set_option autoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The hull observation together with the phase of an anchor pairing. -/
def hullDiscreteFieldSigma {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (ψ : TestC) {p : ℝ} (hp : 0 < p) : MeasurableSpace Ω :=
  hullSigma0 h A n ⊔ MeasurableSpace.comap (fun ω => toIcoMod hp 0 (h ω ψ)) inferInstance

/-- Containment indicators and centered pairings, together with the anchor phase. -/
def hullDiscreteFieldCode {Ω : Type} {I : Type*} (h : Ω → DistC) (A : Ω → Set ℂ)
    (n : ℕ) (φ : I → TestC) (ψ : TestC) {p : ℝ} (hp : 0 < p) :
    Ω → ((I → ℝ × ℝ) × ℝ) :=
  fun ω => (fun i =>
    let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ) ⊆
      interior (dyadicHull n (A ω))}
    (E.indicator (fun _ => 1) ω,
      E.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω ψ) ω),
    toIcoMod hp 0 (h ω ψ))

/-- The discrete-period hull code is measurable in the hull observation with
its anchor phase adjoined. -/
theorem measurable_hullDiscreteFieldCode {Ω : Type} {I : Type*} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (φ : I → TestC) (ψ : TestC) (hψ : ∫ z, ψ z = 1)
    {p : ℝ} (hp : 0 < p) :
    Measurable[hullDiscreteFieldSigma h A n ψ hp] (hullDiscreteFieldCode h A n φ ψ hp) := by
  let : MeasurableSpace Ω := hullDiscreteFieldSigma h A n ψ hp
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    exact ((measurable_indicator_subset_interior_dyadicHull h A hA n
      (tsupport (φ i : ℂ → ℝ) ∪ tsupport (ψ : ℂ → ℝ))).mono le_sup_left le_rfl).prodMk
      ((measurable_hull_gated_centered_pairing h A hA n (φ i) ψ hψ).mono le_sup_left le_rfl)
  · exact (comap_measurable _).mono le_sup_right le_rfl

end LatticeProb.LQG
