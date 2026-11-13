/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.TopoArcInterior at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# An arc contains no disc around an interior point (EXT-CA node T4(c), CORE-3B item 2)

An arc in `ℂ` (the image of an injective continuous map on `Icc 0 1`, see `IsArcSet`) has empty
interior: it contains no disc around any of its interior points, and hence no disc at all
(`interior_arc_eq_empty`).

* `not_ball_subset_arc`: no ball around `γ c`, `0 < c < 1`, is contained in the arc `γ '' Icc 0 1`.
* `interior_arc_eq_empty`: `IsArcSet A → interior A = ∅`.

**Proof (own elementary proof; blueprint §3 T4(c): "an arc minus an interior point is
disconnected; a disk minus a point is not").** Suppose `ball (γ c) R ⊆ γ '' Icc 0 1` for an
interior parameter `c`. Choose `0 < ρ < R` also smaller than the two distances
`dist (γ 0) (γ c)`, `dist (γ 1) (γ c)` (positive by injectivity). The sphere `S := sphere (γ c) ρ`
is preconnected (`isPreconnected_sphere`, using `Module.rank ℝ ℂ = 2`) and lies in the arc. By
continuity of `γ` at `c` pick `ε > 0` with `dist (γ t) (γ c) < ρ` for `t ∈ Icc 0 1` and
`dist t c < ε`; then every point of `S` is `γ t` with `t` outside the open interval
`(c - ε, c + ε)`. So `S ⊆ K₁ ∪ K₂` for the compact (hence closed) sets
`K₁ = γ '' Icc 0 (c - ε)` and `K₂ = γ '' Icc (c + ε) 1`, which are disjoint by injectivity. But
the intermediate value theorem applied to `t ↦ dist (γ t) (γ c)` on `[0, c]` and on `[c, 1]`
(the values at `c` and at the endpoints are `0 < ρ` and `> ρ`) exhibits points of `S` in each of
`K₁`, `K₂`, contradicting the preconnectedness of `S`. For the endpoint case, a disc around
`γ 0` (or `γ 1`) contains a disc of half the radius around a nearby `γ t` with `t ∈ Ioo 0 1`,
which the previous step rules out. -/

open Complex Set Metric Real

namespace QuantumZipper.CA.Topo

/-- The radial function of a curve, `t ↦ dist (γ t) (γ c)`, is continuous wherever `γ` is
(own elementary proof). -/
private theorem continuousOn_dist_curve {γ : ℝ → ℂ} {s : Set ℝ} {c : ℝ} (hγ : ContinuousOn γ s) :
    ContinuousOn (fun t => dist (γ t) (γ c)) s := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.1 (hγ b hb) ε hε
  exact ⟨δ, hδpos, fun a ha had => lt_of_le_of_lt (dist_dist_dist_le_left _ _ _) (hδ ha had)⟩

/-- An arc contains no disc around one of its interior points (own elementary proof, blueprint
§3 T4(c), first part): if `c ∈ Ioo 0 1` and `γ` is continuous and injective on `Icc 0 1`, then
`ball (γ c) R` is not contained in the arc `γ '' Icc 0 1`. -/
theorem not_ball_subset_arc {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Set.Icc 0 1))
    (hγi : Set.InjOn γ (Set.Icc 0 1)) {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) {R : ℝ}
    (hR : 0 < R) : ¬ Metric.ball (γ c) R ⊆ γ '' Set.Icc 0 1 := by
  intro hsub
  have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_refl 1⟩
  have hd0 : 0 < dist (γ 0) (γ c) := by
    rw [dist_pos]
    exact fun h => (ne_of_lt hc.1) (hγi h0mem hc01 h)
  have hd1 : 0 < dist (γ 1) (γ c) := by
    rw [dist_pos]
    exact fun h => (ne_of_gt hc.2) (hγi h1mem hc01 h)
  set ρ : ℝ := min R (min (dist (γ 0) (γ c)) (dist (γ 1) (γ c))) / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have := lt_min hR (lt_min hd0 hd1)
    linarith
  have hρR : ρ < R := by
    rw [hρdef]
    have := min_le_left R (min (dist (γ 0) (γ c)) (dist (γ 1) (γ c)))
    linarith
  have hρ0 : ρ < dist (γ 0) (γ c) := by
    rw [hρdef]
    have h₁ := min_le_right R (min (dist (γ 0) (γ c)) (dist (γ 1) (γ c)))
    have h₂ := min_le_left (dist (γ 0) (γ c)) (dist (γ 1) (γ c))
    linarith
  have hρ1 : ρ < dist (γ 1) (γ c) := by
    rw [hρdef]
    have h₁ := min_le_right R (min (dist (γ 0) (γ c)) (dist (γ 1) (γ c)))
    have h₂ := min_le_right (dist (γ 0) (γ c)) (dist (γ 1) (γ c))
    linarith
  -- continuity at the interior parameter `c`
  obtain ⟨ε, hεpos, hε⟩ := Metric.continuousWithinAt_iff.1 (hγc c hc01) ρ hρpos
  -- the two closed pieces of the arc on either side of `c`
  set K₁ : Set ℂ := γ '' Set.Icc 0 (c - ε) with hK₁def
  set K₂ : Set ℂ := γ '' Set.Icc (c + ε) 1 with hK₂def
  have hK₁cl : IsClosed K₁ :=
    (isCompact_Icc.image_of_continuousOn
      (hγc.mono (Icc_subset_Icc le_rfl (by linarith [hc.2])))).isClosed
  have hK₂cl : IsClosed K₂ :=
    (isCompact_Icc.image_of_continuousOn
      (hγc.mono (Icc_subset_Icc (by linarith [hc.1]) le_rfl))).isClosed
  have hKdisj : K₁ ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨t₁, ht₁, ht₁x⟩, ⟨t₂, ht₂, ht₂x⟩⟩
    have h₁ : t₁ ≤ 1 := by linarith [ht₁.2, hc.2]
    have h₂ : 0 ≤ t₂ := by linarith [ht₂.1, hc.1]
    have heq : t₁ = t₂ := hγi ⟨ht₁.1, h₁⟩ ⟨h₂, ht₂.2⟩ (ht₁x.trans ht₂x.symm)
    linarith [ht₁.2, ht₂.1, heq, hεpos]
  -- every point of the sphere is in one of the two pieces
  have hSsub12 : sphere (γ c) ρ ⊆ K₁ ∪ K₂ := by
    intro x hxS
    have hxρ : dist x (γ c) = ρ := mem_sphere.1 hxS
    have hxball : x ∈ ball (γ c) R := by
      rw [mem_ball, hxρ]
      exact hρR
    obtain ⟨t, ht, htx⟩ := hsub hxball
    have htnot : ¬ (c - ε < t ∧ t < c + ε) := by
      rintro ⟨h₁, h₂⟩
      have hdt : dist t c < ε := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith⟩
      have hclose := hε ht hdt
      have heq : dist (γ t) (γ c) = ρ := by
        rw [htx]
        exact hxρ
      linarith
    have ht' : t ≤ c - ε ∨ c + ε ≤ t := by
      by_contra h
      push Not at h
      exact htnot h
    rcases ht' with h | h
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, htx⟩
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, htx⟩
  -- points of the sphere on each side, by the intermediate value theorem
  have hf₁ : ContinuousOn (fun t : ℝ => dist (γ t) (γ c)) (Set.Icc 0 c) :=
    continuousOn_dist_curve (hγc.mono (Icc_subset_Icc le_rfl hc.2.le))
  have hf₂ : ContinuousOn (fun t : ℝ => dist (γ t) (γ c)) (Set.Icc c 1) :=
    continuousOn_dist_curve (hγc.mono (Icc_subset_Icc hc.1.le le_rfl))
  have hmem₁ : ρ ∈ Set.Icc (dist (γ c) (γ c)) (dist (γ 0) (γ c)) := by
    rw [dist_self]
    exact ⟨hρpos.le, hρ0.le⟩
  obtain ⟨t₁, ht₁, ht₁ρ⟩ := intermediate_value_Icc' hc.1.le hf₁ hmem₁
  have hmem₂ : ρ ∈ Set.Icc (dist (γ c) (γ c)) (dist (γ 1) (γ c)) := by
    rw [dist_self]
    exact ⟨hρpos.le, hρ1.le⟩
  obtain ⟨t₂, ht₂, ht₂ρ⟩ := intermediate_value_Icc hc.2.le hf₂ hmem₂
  have ht₁le : t₁ ≤ c - ε := by
    by_contra h
    push Not at h
    have hdt : dist t₁ c < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith [ht₁.2, hεpos]⟩
    have hlt := hε ⟨ht₁.1, by linarith [ht₁.2, hc.2]⟩ hdt
    rw [show dist (γ t₁) (γ c) = ρ from ht₁ρ] at hlt
    exact (lt_irrefl ρ) hlt
  have ht₂ge : c + ε ≤ t₂ := by
    by_contra h
    push Not at h
    have hdt : dist t₂ c < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht₂.1, hεpos], by linarith⟩
    have hlt := hε ⟨by linarith [ht₂.1, hc.1], ht₂.2⟩ hdt
    rw [show dist (γ t₂) (γ c) = ρ from ht₂ρ] at hlt
    exact (lt_irrefl ρ) hlt
  -- contradiction with the preconnectedness of the sphere
  have hx₁S : γ t₁ ∈ sphere (γ c) ρ := mem_sphere.2 ht₁ρ
  have hx₁K₁ : γ t₁ ∈ K₁ := ⟨t₁, ⟨ht₁.1, ht₁le⟩, rfl⟩
  have hx₂S : γ t₂ ∈ sphere (γ c) ρ := mem_sphere.2 ht₂ρ
  have hx₂K₂ : γ t₂ ∈ K₂ := ⟨t₂, ⟨ht₂ge, ht₂.2⟩, rfl⟩
  have hSpre : IsPreconnected (sphere (γ c) ρ) :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (γ c) ρ
  have hSdisj : sphere (γ c) ρ ∩ (K₁ ∩ K₂) = ∅ := by rw [hKdisj, Set.inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hSpre K₁ K₂ hK₁cl hK₂cl hSsub12 hSdisj
    with h | h
  · have hmem : γ t₂ ∈ K₁ ∩ K₂ := ⟨h hx₂S, hx₂K₂⟩
    rw [hKdisj] at hmem
    exact hmem
  · have hmem : γ t₁ ∈ K₁ ∩ K₂ := ⟨hx₁K₁, h hx₁S⟩
    rw [hKdisj] at hmem
    exact hmem

/-- If a disc around an endpoint of an arc is contained in the arc, so is a disc around a nearby
interior point (own elementary proof, used for the endpoint case of `interior_arc_eq_empty`). -/
private theorem exists_ball_subset_of_endpoint {γ : ℝ → ℂ}
    (hγc : ContinuousOn γ (Set.Icc 0 1)) {c : ℝ} (hc : c = 0 ∨ c = 1) {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball (γ c) R ⊆ γ '' Set.Icc 0 1) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, Metric.ball (γ t) (R / 2) ⊆ γ '' Set.Icc 0 1 := by
  have hR2 : 0 < R / 2 := by linarith
  rcases hc with rfl | rfl
  · obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousWithinAt_iff.1 (hγc 0 ⟨le_refl 0, zero_le_one⟩) (R / 2) hR2
    set s : ℝ := (min δ 1) / 2 with hsdef
    have hspos : 0 < s := by
      rw [hsdef]
      have := lt_min hδpos one_pos
      linarith
    have hslt1 : s < 1 := by
      rw [hsdef]
      have := min_le_right δ 1
      linarith
    have hsltδ : s < δ := by
      rw [hsdef]
      have := min_le_left δ 1
      linarith
    refine ⟨s, ⟨hspos, hslt1⟩, ?_⟩
    have hclose : dist (γ s) (γ 0) < R / 2 := by
      refine hδ ⟨hspos.le, hslt1.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos hspos]
      exact hsltδ
    intro w hw
    refine hball ?_
    rw [mem_ball] at hw ⊢
    calc dist w (γ 0) ≤ dist w (γ s) + dist (γ s) (γ 0) := dist_triangle _ _ _
      _ < R / 2 + R / 2 := by linarith
      _ = R := by ring
  · obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousWithinAt_iff.1 (hγc 1 ⟨zero_le_one, le_refl 1⟩) (R / 2) hR2
    set s : ℝ := (min δ 1) / 2 with hsdef
    have hspos : 0 < s := by
      rw [hsdef]
      have := lt_min hδpos one_pos
      linarith
    have hslt1 : s < 1 := by
      rw [hsdef]
      have := min_le_right δ 1
      linarith
    have hsltδ : s < δ := by
      rw [hsdef]
      have := min_le_left δ 1
      linarith
    refine ⟨1 - s, ⟨by linarith, by linarith⟩, ?_⟩
    have hclose : dist (γ (1 - s)) (γ 1) < R / 2 := by
      refine hδ ⟨by linarith, by linarith⟩ ?_
      have h1s : (1 - s) - 1 = -s := by ring
      rw [Real.dist_eq, h1s, abs_neg, abs_of_pos hspos]
      exact hsltδ
    intro w hw
    refine hball ?_
    rw [mem_ball] at hw ⊢
    calc dist w (γ 1) ≤ dist w (γ (1 - s)) + dist (γ (1 - s)) (γ 1) := dist_triangle _ _ _
      _ < R / 2 + R / 2 := by linarith
      _ = R := by ring

/-- **EXT-CA T4(c), CORE-3B item 2**: an arc in `ℂ` has empty interior (own elementary proof,
blueprint §3 T4(c)). -/
theorem interior_arc_eq_empty {A : Set ℂ} (hA : IsArcSet A) : interior A = ∅ := by
  obtain ⟨γ, hγc, hγi, rfl⟩ := hA
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  obtain ⟨c, hc01, rfl⟩ := hball (mem_ball_self hR)
  by_cases hci : c ∈ Set.Ioo (0 : ℝ) 1
  · exact not_ball_subset_arc hγc hγi hci hR hball
  · have hend : c = 0 ∨ c = 1 := by
      have h : c ≤ 0 ∨ 1 ≤ c := by
        by_contra h
        push Not at h
        exact hci ⟨h.1, h.2⟩
      rcases h with h | h
      · exact Or.inl (le_antisymm h hc01.1)
      · exact Or.inr (le_antisymm hc01.2 h)
    obtain ⟨t, htIoo, htball⟩ := exists_ball_subset_of_endpoint hγc hend hR hball
    exact not_ball_subset_arc hγc hγi htIoo (by linarith : 0 < R / 2) htball

end QuantumZipper.CA.Topo
