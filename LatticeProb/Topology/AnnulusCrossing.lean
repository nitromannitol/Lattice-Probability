import LatticeProb.Topology.PeanoContinuum
import LatticeProb.Topology.CrosscutSides

/-!
# Crossing components of a Peano continuum in an annulus

Let `K ⊆ ℂ` be compact and locally connected, and `φ : ℂ → ℝ` a `1`-Lipschitz function (for instance the
sup-distance `z ↦ max |Re (z - x)| |Im (z - x)|` to a point `x`, whose sublevel sets are closed squares). For `s < t`,
only finitely many components of `K ∩ {s ≤ φ ≤ t}` meet both level sets `{φ = s}` and `{φ = t}`.

This is the uniform local connectedness (ULC) bound on annular crossings used in the proof of Torhorst's theorem
(Whyburn, *Analytic Topology*, Chapter VI): each crossing component contains a point of the middle level set
`{φ = (s + t) / 2}`, and points of distinct crossing components are uniformly separated, since two close points of `K`
lie in a small continuum of `K` that stays inside the open annulus `{s < φ < t}`.

* `finite_crossing_connectedComponentsIn`: the finiteness statement.
-/

open Set Metric
open scoped Topology

namespace LatticeProb.Topology

/-- **Finitely many annular crossings.** Let `K ⊆ ℂ` be compact and locally connected, `φ : ℂ → ℝ` be
`1`-Lipschitz and `s < t`. Only finitely many components of `K ∩ φ ⁻¹' [s, t]` meet both `{φ = s}` and `{φ = t}`. -/
theorem finite_crossing_connectedComponentsIn {K : Set ℂ} (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    {φ : ℂ → ℝ} (hφ : LipschitzWith 1 φ) {s t : ℝ} (hst : s < t) :
    {U ∈ connectedComponentsIn (K ∩ φ ⁻¹' Icc s t) | (∃ p ∈ U, φ p = s) ∧ ∃ p ∈ U, φ p = t}.Finite := by
  set A := K ∩ φ ⁻¹' Icc s t with hA
  obtain ⟨δ, hδ, hulc⟩ :=
    IsLocallyConnectedSet.uniformly_locallyConnected hK hlc (half_pos (sub_pos.2 hst))
  obtain ⟨c, -, hcf, hcov⟩ := hK.finite_cover_balls (half_pos hδ)
  -- at most one crossing component has a point of the middle level set in a given ball of radius `δ / 2`
  have hsub : ∀ y : ℂ, {U | U ∈ connectedComponentsIn A ∧
      ∃ p ∈ U, φ p = (s + t) / 2 ∧ dist p y < δ / 2}.Subsingleton := by
    rintro y U ⟨hU, p, hpU, hpm, hpy⟩ V ⟨hV, p', hpV, hpm', hpy'⟩
    have hpA := subset_of_mem_connectedComponentsIn hU hpU
    have hpA' := subset_of_mem_connectedComponentsIn hV hpV
    obtain ⟨L, hLK, hLcpt, hLc, hpL, hpL', hLd⟩ :=
      hulc p hpA.1 p' hpA'.1 (by linarith [dist_triangle_right p p' y])
    have hLA : L ⊆ A := by
      intro z hz
      refine ⟨hLK hz, ?_⟩
      have h1 : dist z p ≤ diam L := dist_le_diam_of_mem hLcpt.isBounded hz hpL
      have h2 : dist (φ z) (φ p) ≤ dist z p := by simpa using hφ.dist_le_mul z p
      rw [Real.dist_eq, abs_le] at h2
      show s ≤ φ z ∧ φ z ≤ t
      constructor <;> linarith
    have hLU : L ⊆ U :=
      subset_of_mem_connectedComponentsIn_of_nonempty_inter hU hLc.isPreconnected hLA ⟨p, hpL, hpU⟩
    have hLV : L ⊆ V :=
      subset_of_mem_connectedComponentsIn_of_nonempty_inter hV hLc.isPreconnected hLA ⟨p', hpL', hpV⟩
    exact (subset_of_mem_connectedComponentsIn_of_nonempty_inter hV
        (isConnected_of_mem_connectedComponentsIn hU).isPreconnected
        (subset_of_mem_connectedComponentsIn hU) ⟨p, hpU, hLV hpL⟩).antisymm
      (subset_of_mem_connectedComponentsIn_of_nonempty_inter hU
        (isConnected_of_mem_connectedComponentsIn hV).isPreconnected
        (subset_of_mem_connectedComponentsIn hV) ⟨p', hpV, hLU hpL'⟩)
  refine (hcf.biUnion fun y _ => (hsub y).finite).subset ?_
  rintro U ⟨hU, ⟨p₀, hp₀U, hp₀⟩, ⟨p₁, hp₁U, hp₁⟩⟩
  -- a crossing component meets the middle level set
  have hiv := (isConnected_of_mem_connectedComponentsIn hU).isPreconnected.intermediate_value hp₀U hp₁U
    hφ.continuous.continuousOn
  rw [hp₀, hp₁] at hiv
  obtain ⟨p, hpU, hpm⟩ := hiv (show (s + t) / 2 ∈ Icc s t from ⟨by linarith, by linarith⟩)
  obtain ⟨y, hy, hpy⟩ := mem_iUnion₂.1 (hcov (subset_of_mem_connectedComponentsIn hU hpU).1)
  exact mem_biUnion hy ⟨hU, p, hpU, hpm, hpy⟩

end LatticeProb.Topology
