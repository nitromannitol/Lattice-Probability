import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of a distance function from its behaviour at the diagonal

Let `d : α → α → ℝ≥0∞` be symmetric and satisfy the triangle inequality on a set `D`. If for every `p ∈ D` the
distance `d w p` tends to `0` as `w → p` within `D`, then `(x, y) ↦ d x y` is continuous on `D × D`, as a map into
`ℝ≥0∞` (the value `⊤` is allowed).

The two-sided estimate is `d x y ≤ d x x₀ + d x₀ y₀ + d y₀ y` together with
`d x₀ y₀ - d x₀ x - d y y₀ ≤ d x y`.
-/

open Set Filter Topology
open scoped ENNReal

namespace LatticeProb.Topology

variable {α : Type*} [TopologicalSpace α]

/-- **Continuity from the diagonal.** A function `d : α → α → ℝ≥0∞` that is symmetric and satisfies the triangle
inequality on `D`, and whose distance to a point `p ∈ D` tends to `0` at `p` within `D`, is continuous on
`D × D`. -/
theorem continuousOn_uncurry_of_tendsto_diag {D : Set α} {d : α → α → ℝ≥0∞}
    (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    (hsymm : ∀ x ∈ D, ∀ y ∈ D, d x y = d y x)
    (hdiag : ∀ p ∈ D, Tendsto (fun w => d w p) (𝓝[D] p) (𝓝 0)) :
    ContinuousOn (fun q : α × α => d q.1 q.2) (D ×ˢ D) := by
  rintro ⟨u₀, v₀⟩ ⟨hu₀, hv₀⟩
  rw [ContinuousWithinAt, nhdsWithin_prod_eq]
  have h1 : Tendsto (fun q : α × α => d q.1 u₀) (𝓝[D] u₀ ×ˢ 𝓝[D] v₀) (𝓝 0) :=
    (hdiag u₀ hu₀).comp tendsto_fst
  have h2 : Tendsto (fun q : α × α => d q.2 v₀) (𝓝[D] u₀ ×ˢ 𝓝[D] v₀) (𝓝 0) :=
    (hdiag v₀ hv₀).comp tendsto_snd
  have hmemu : ∀ᶠ q in 𝓝[D] u₀ ×ˢ 𝓝[D] v₀, q.1 ∈ D :=
    tendsto_fst.eventually eventually_mem_nhdsWithin
  have hmemv : ∀ᶠ q in 𝓝[D] u₀ ×ˢ 𝓝[D] v₀, q.2 ∈ D :=
    tendsto_snd.eventually eventually_mem_nhdsWithin
  have hc : Tendsto (fun _ : α × α => d u₀ v₀) (𝓝[D] u₀ ×ˢ 𝓝[D] v₀) (𝓝 (d u₀ v₀)) :=
    tendsto_const_nhds
  have hup : Tendsto (fun q : α × α => d q.1 u₀ + (d u₀ v₀ + d q.2 v₀))
      (𝓝[D] u₀ ×ˢ 𝓝[D] v₀) (𝓝 (d u₀ v₀)) := by
    have h3 := h1.add (hc.add h2)
    rwa [add_zero, zero_add] at h3
  have hlow : Tendsto (fun q : α × α => d u₀ v₀ - d q.1 u₀ - d q.2 v₀)
      (𝓝[D] u₀ ×ˢ 𝓝[D] v₀) (𝓝 (d u₀ v₀)) := by
    have h3 := ENNReal.Tendsto.sub (ENNReal.Tendsto.sub hc h1
      (Or.inr ENNReal.zero_ne_top)) h2 (Or.inr ENNReal.zero_ne_top)
    rwa [tsub_zero, tsub_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hmemu, hmemv] with q hq1 hq2
    rw [tsub_le_iff_right, tsub_le_iff_right]
    calc d u₀ v₀ ≤ d u₀ q.1 + d q.1 v₀ := htri _ hu₀ _ hq1 _ hv₀
      _ ≤ d u₀ q.1 + (d q.1 q.2 + d q.2 v₀) := add_le_add le_rfl (htri _ hq1 _ hq2 _ hv₀)
      _ = d q.1 q.2 + d q.2 v₀ + d q.1 u₀ := by rw [hsymm u₀ hu₀ q.1 hq1]; ring
  · filter_upwards [hmemu, hmemv] with q hq1 hq2
    calc d q.1 q.2 ≤ d q.1 u₀ + d u₀ q.2 := htri _ hq1 _ hu₀ _ hq2
      _ ≤ d q.1 u₀ + (d u₀ v₀ + d v₀ q.2) := add_le_add le_rfl (htri _ hu₀ _ hv₀ _ hq2)
      _ = d q.1 u₀ + (d u₀ v₀ + d q.2 v₀) := by rw [hsymm v₀ hv₀ q.2 hq2]

end LatticeProb.Topology
