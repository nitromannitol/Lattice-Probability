import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Prob.UniformModShift
import LatticeProb.Topology.CompactThickeningEvent

/-! # Discrete-period field observations near a random compact set -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- Each coordinate records compact containment and, when containment holds,
the corresponding centered field pairing. The anchor phase is recorded separately. -/
def randomDiscreteFieldCode {Ω I J : Type*} (K : Ω → NonemptyCompacts ℂ)
    (h : Ω → DistC) (S : I → Set ℂ) (φ : I → TestC) (ψ : J → TestC)
    (r : J → ℝ) {p : ℝ} (hp : 0 < p) : Ω → ((J → I → ℝ × ℝ) × (J → ℝ)) :=
  fun ω => (fun j i =>
    let A : Set Ω := {ω | S i ⊆ thickening (r j) (K ω : Set ℂ)}
    (A.indicator (fun _ => 1) ω,
      A.indicator (fun ω => h ω (φ i) - (∫ z, φ i z) * h ω (ψ j)) ω),
    fun j => toIcoMod hp 0 (h ω (ψ j)))

/-- The random-neighborhood code is measurable for compact test supports and
measurable compact set and field. -/
theorem measurable_randomDiscreteFieldCode {Ω I J : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    {K : Ω → NonemptyCompacts ℂ} {h : Ω → DistC} (hK : Measurable K)
    (hh : Measurable h) (S : I → Set ℂ) (hS : ∀ i, IsCompact (S i))
    (φ : I → TestC) (ψ : J → TestC) (r : J → ℝ) {p : ℝ} (hp : 0 < p) :
    Measurable (randomDiscreteFieldCode K h S φ ψ r hp) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro i
    have hA : MeasurableSet {ω | S i ⊆ thickening (r j) (K ω : Set ℂ)} :=
      measurableSet_compact_subset_thickening hK (hS i) (r j)
    exact (measurable_const.indicator hA).prodMk
      ((((LQGMetric.GFFInv.measurable_pair (φ i)).comp hh).sub
        (measurable_const.mul ((LQGMetric.GFFInv.measurable_pair (ψ j)).comp hh))).indicator hA)
  · apply measurable_pi_iff.mpr
    intro j
    exact (LatticeProb.measurable_toIcoMod_zero hp).comp
      ((LQGMetric.GFFInv.measurable_pair (ψ j)).comp hh)

end LatticeProb.LQG
