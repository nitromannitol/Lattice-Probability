import LatticeProb.Prob.Strassen.Defs

/-!
# Converse (easy): a monotone coupling gives domination

The easy converse of Strassen's theorem: a coupling `π` with marginals `μ, ν` supported a.e. on
`couplingSupport S` implies every measurable increasing event is at least as likely under `μ` as
under `ν` (`domination_of_monotone_coupling`).
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- **Converse of Strassen's theorem.** A coupling `π` with marginals `μ, ν` supported a.e. on `{p.2
≤ p.1}` implies every measurable increasing event is at least as likely under `μ` as under `ν`. -/
theorem domination_of_monotone_coupling {S : Type} (μ ν : Measure (S → Bool))
    (π : Measure ((S → Bool) × (S → Bool)))
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hmono : ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true) :
    ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A := by
  intro A hA hA'
  rw [← hsnd, Measure.map_apply measurable_snd hA, ← hfst, Measure.map_apply measurable_fst hA]
  apply measure_mono_ae
  filter_upwards [hmono] with p hp hpA
  exact hA' p.2 p.1 hpA hp

end StrassenAux

end LatticeProb
