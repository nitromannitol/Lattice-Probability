import LatticeProb.LQG.LQGMetricMeasurable

/-! # Finite internal diameters of compact connected sets inside open sets

Let `D` be a Euclidean length metric on `ℂ` (`IsEuclideanLengthMetric`). For an open set `U` and a compact preconnected
set `K ⊆ U`, the internal metric `D(·, ·; U)` is bounded on `K × K`:
  `sup_{u, v ∈ K} D(u, v; U) < ∞`.
The proof is deterministic: `D(u, v; U)` is finite for `v` near `u` (short paths stay in `U`), finiteness is symmetric
and transitive (triangle inequality for internal metrics), so it holds on all of the preconnected set `K`; then the
internal metric is continuous on `U × U` and attains its maximum on the compact set `K × K`.

Consequently, for a closed set `S` and a compact preconnected `K ⊆ int S`, the internal diameter of `K` in `S` is
finite. This is the interior part of the internal-diameter estimates for the LQG metric; the bound for a closed square
in its own internal metric needs, in addition, control of paths near the boundary of the square.

Main results:
* `IsEuclideanLengthMetric.internalMetric_lt_top_of_isPreconnected`: `D(u, v; U) < ∞` for `u, v` in a preconnected
  `K ⊆ U`, `U` open.
* `IsEuclideanLengthMetric.exists_internalMetric_le_ofReal_of_isCompact`: the uniform bound on a compact preconnected
  `K ⊆ U`.
* `IsEuclideanLengthMetric.exists_internalMetric_le_ofReal_of_subset_interior`: the same bound for `D(·, ·; S)` when
  `K ⊆ int S`.
-/

namespace LatticeProb.LQG

open Set Filter Topology
open scoped ENNReal

/-- For a Euclidean length metric, an open set `U` and a preconnected set `K ⊆ U`, the internal metric `D(u, v; U)`
is finite for all `u, v ∈ K`. -/
theorem IsEuclideanLengthMetric.internalMetric_lt_top_of_isPreconnected {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {K U : Set ℂ} (hKc : IsPreconnected K) (hU : IsOpen U) (hKU : K ⊆ U)
    {u v : ℂ} (hu : u ∈ K) (hv : v ∈ K) : internalMetric D U u v < ∞ := by
  have hnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  refine hKc.induction₂ (fun x y => internalMetric D U x y < ∞) (fun x hx => ?_)
    (fun x y z _ _ _ hxy hyz => ?_) (fun x y _ _ hxy => by rwa [hD.internalMetric_symm]) hu hv
  · have hc := hD.continuousAt_internalMetric_self hnn hU (hKU hx)
    have h0 : internalMetric D U x x < ∞ := by
      rw [hD.internalMetric_self_of_mem_open hnn hU (hKU hx)]
      exact ENNReal.zero_lt_top
    exact nhdsWithin_le_nhds (hc.eventually (eventually_lt_nhds h0))
  · exact lt_of_le_of_lt (hD.internalMetric_triangle U x y z) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩)

/-- **Finite internal diameter of a compact connected set inside an open set.** For a Euclidean length metric `D`, an
open set `U` and a compact preconnected set `K ⊆ U`, there is a real `A` with `D(u, v; U) ≤ A` for all `u, v ∈ K`. -/
theorem IsEuclideanLengthMetric.exists_internalMetric_le_ofReal_of_isCompact {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {K U : Set ℂ} (hK : IsCompact K) (hKc : IsPreconnected K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ A : ℝ, ∀ u ∈ K, ∀ v ∈ K, internalMetric D U u v ≤ ENNReal.ofReal A := by
  have hnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun u hu => hu.elim⟩
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D U p.1 p.2) (K ×ˢ K) :=
    (hD.continuousOn_internalMetric_pair hnn hU).mono (prod_mono hKU hKU)
  obtain ⟨p, hp, hmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne) hcont
  refine ⟨(internalMetric D U p.1 p.2).toReal, fun u hu v hv => ?_⟩
  rw [ENNReal.ofReal_toReal (hD.internalMetric_lt_top_of_isPreconnected hKc hU hKU hp.1 hp.2).ne]
  exact isMaxOn_iff.1 hmax (u, v) (mk_mem_prod hu hv)

/-- For a Euclidean length metric `D`, a set `S` and a compact preconnected set `K` contained in the interior of `S`,
there is a real `A` with `D(u, v; S) ≤ A` for all `u, v ∈ K`. -/
theorem IsEuclideanLengthMetric.exists_internalMetric_le_ofReal_of_subset_interior {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {K S : Set ℂ} (hK : IsCompact K) (hKc : IsPreconnected K)
    (hKS : K ⊆ interior S) : ∃ A : ℝ, ∀ u ∈ K, ∀ v ∈ K, internalMetric D S u v ≤ ENNReal.ofReal A := by
  obtain ⟨A, hA⟩ := hD.exists_internalMetric_le_ofReal_of_isCompact hK hKc isOpen_interior hKS
  exact ⟨A, fun u hu v hv => (internalMetric_anti D interior_subset u v).trans (hA u hu v hv)⟩

end LatticeProb.LQG
