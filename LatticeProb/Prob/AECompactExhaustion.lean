import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Almost sure properties on compact sets -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A property inherited by subsets holds almost surely on every compact set
simultaneously if it holds almost surely on each member of a compact exhaustion. -/
theorem ae_forall_isCompact_of_exhaustion
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    (μ : Measure Ω) (K : CompactExhaustion X) (P : Ω → Set X → Prop)
    (hmono : ∀ ω A B, A ⊆ B → P ω B → P ω A)
    (hK : ∀ n, ∀ᵐ ω ∂μ, P ω (K n)) :
    ∀ᵐ ω ∂μ, ∀ A : Set X, IsCompact A → P ω A := by
  filter_upwards [ae_all_iff.2 hK] with ω hω
  intro A hA
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
  exact hmono ω A (K n) hn (hω n)

/-- On a weakly locally compact, sigma-compact space, separate almost-sure
statements for each compact set can be made simultaneous when they pass to subsets. -/
theorem ae_forall_isCompact_of_forall
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    (μ : Measure Ω) (P : Ω → Set X → Prop)
    (hmono : ∀ ω A B, A ⊆ B → P ω B → P ω A)
    (h : ∀ A : Set X, IsCompact A → ∀ᵐ ω ∂μ, P ω A) :
    ∀ᵐ ω ∂μ, ∀ A : Set X, IsCompact A → P ω A := by
  let K := CompactExhaustion.choice X
  exact ae_forall_isCompact_of_exhaustion μ K P hmono fun n => h (K n) (K.isCompact n)

end LatticeProb
