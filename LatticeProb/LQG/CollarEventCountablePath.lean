import LatticeProb.LQG.CollarOpenContainment
import LatticeProb.Bonanno.SupercriticalConformalCovariance.TV.LocalCountablePath

/-! # Countable quotient observations on collar containment events -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric
open SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- On the event that a fixed open set lies in the random collar, its
countable mean-zero field coordinates and unit-integral phase are observable
from the collar code. Both coordinates are set to zero outside the event. -/
theorem measurable_event_localCountablePath_phase_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ z, ρ z = 1) :
    let E := {ω | (O : Set ℂ) ⊆ thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (fun ω =>
        ((fun n => E.indicator (fun x => localCountablePath O ρ hρO hρ1 (h x) n) ω),
          E.indicator (fun x => toIcoMod hp 0 (h x ρ)) ω)) := by
  let E := {ω | (O : Set ℂ) ⊆ thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
  have hE : MeasurableSet[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] E :=
    measurableSet_open_subset_collar_of_collarFieldCode h K ψ hp k O
  have hO : ∀ ω ∈ E, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ) := fun _ hω => hω
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro n
    have hm := measurable_indicator_centered_pairing_of_collarFieldCode
      h K ψ hp k O E hE hO (localMeanZeroGen O ρ hρO hρ1 n).1.1
      (localMeanZeroGen O ρ hρO hρ1 n).2
    simpa only [(localMeanZeroGen O ρ hρO hρ1 n).1.2, zero_mul, sub_zero,
      localCountablePath] using hm
  · exact measurable_indicator_phase_of_collarFieldCode h K ψ hp k O E hE hO ρ hρO hρ1

end LatticeProb.LQG
