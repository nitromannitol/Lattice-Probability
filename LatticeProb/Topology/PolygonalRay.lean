import Mathlib
import LatticeProb.Topology.PathGluing

/-!
# Polygonal rays

A *polygonal ray* towards a point `x` runs through vertices `v 0, v 1, v 2, …` with `v n → x`: on the time interval
`[1 - 2⁻¹ ^ n, 1 - 2⁻¹ ^ (n + 1)]` it moves affinely along the segment `[v n, v (n + 1)]`, and it reaches `x` at
time `1`. Such rays are the access arcs to boundary points of plane domains in the proof of Torhorst's theorem.

* `IsPolygonalRayParam v x β`: `β` is the parametrisation just described.
* `exists_polygonalRay_param`: it exists and is continuous on `[0, 1]` when `v n → x`.
* `IsPolygonalRayParam.apply_grid`, `IsPolygonalRayParam.image_Icc_grid`, `IsPolygonalRayParam.exists_mem_segment`:
  it passes through `v n` at time `1 - 2⁻¹ ^ n`, traces `[v n, v (n + 1)]` on the `n`-th interval, and lies on the
  segments before time `1`.
* `IsPolygonalRayParam.injOn`: it is injective on `[0, 1]` when consecutive vertices are distinct, consecutive
  segments meet only in their common vertex, non-consecutive segments are disjoint and `x` lies on no segment.
-/

open Set Filter Metric
open scoped Topology

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `β` runs the polygonal ray through `v 0, v 1, …` towards `x`: affinely along `[v n, v (n + 1)]` on
`[1 - 2⁻¹ ^ n, 1 - 2⁻¹ ^ (n + 1)]`, and `β 1 = x`. -/
def IsPolygonalRayParam (v : ℕ → E) (x : E) (β : ℝ → E) : Prop :=
  β 1 = x ∧ ∀ n : ℕ, ∀ t ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)),
    β t = AffineMap.lineMap (v n) (v (n + 1)) ((t - (1 - 2⁻¹ ^ n)) / 2⁻¹ ^ (n + 1))

theorem two_inv_pow_eq_two_mul (n : ℕ) : (2⁻¹ : ℝ) ^ n = 2 * 2⁻¹ ^ (n + 1) := by
  rw [pow_succ]
  ring

/-- The local time on the `n`-th interval of the dyadic grid lies in `[0, 1]`. -/
theorem div_mem_Icc_of_mem_grid {n : ℕ} {t : ℝ} (ht : t ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1))) :
    (t - (1 - 2⁻¹ ^ n)) / 2⁻¹ ^ (n + 1) ∈ Icc (0 : ℝ) 1 := by
  have hw : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
  have h2 := two_inv_pow_eq_two_mul n
  refine ⟨div_nonneg (by linarith [ht.1]) hw.le, ?_⟩
  rw [div_le_one hw]
  linarith [ht.2]

/-- Every time in `[0, 1)` lies in some interval `[1 - 2⁻¹ ^ n, 1 - 2⁻¹ ^ (n + 1)]` of the dyadic grid. -/
theorem exists_mem_grid {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ n : ℕ, t ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) := by
  classical
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
  have hex : ∃ m : ℕ, t ≤ 1 - 2⁻¹ ^ (m + 1) := by
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds (sub_pos.2 ht1))).exists
    refine ⟨m, ?_⟩
    have h2 := two_inv_pow_eq_two_mul m
    have hpos : (0 : ℝ) < 2⁻¹ ^ (m + 1) := by positivity
    linarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases hk : Nat.find hex with _ | k
  · simpa using ht0
  · have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [not_le] at hmin
    exact hmin.le

/-- **Polygonal ray parametrisation.** If `v n → x`, the polygonal ray through the `v n` towards `x` has a
parametrisation that is continuous on `[0, 1]`. -/
theorem exists_polygonalRay_param {v : ℕ → E} {x : E} (hv : Tendsto v atTop (𝓝 x)) :
    ∃ β : ℝ → E, ContinuousOn β (Icc 0 1) ∧ IsPolygonalRayParam v x β := by
  set ρ : ℕ → ℝ := fun n => max (dist (v n) x) (dist (v (n + 1)) x) + 2⁻¹ ^ n with hρ_def
  have hd : Tendsto (fun n => dist (v n) x) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hv
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    have h1 := hd.max (hd.comp (tendsto_add_atTop_nat 1))
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
    have h3 := h1.add h2
    rw [max_self, add_zero] at h3
    exact h3
  have hγρ : ∀ n, ∀ s, dist (Path.segment (v n) (v (n + 1)) s) x < ρ n := by
    intro n s
    have hmem : Path.segment (v n) (v (n + 1)) s ∈ segment ℝ (v n) (v (n + 1)) := by
      rw [← Path.range_segment]
      exact mem_range_self _
    have hsub : segment ℝ (v n) (v (n + 1)) ⊆ closedBall x (max (dist (v n) x) (dist (v (n + 1)) x)) :=
      (convex_closedBall _ _).segment_subset (mem_closedBall.2 (le_max_left _ _))
        (mem_closedBall.2 (le_max_right _ _))
    have hle := mem_closedBall.1 (hsub hmem)
    have hpos : (0 : ℝ) < 2⁻¹ ^ n := by positivity
    simp only [hρ_def]
    linarith
  obtain ⟨β, hc, h1, -, hgrid⟩ :=
    exists_continuousOn_Icc_of_tendsto_paths_grid (fun n => Path.segment (v n) (v (n + 1))) hρ hγρ
  refine ⟨β, hc, h1, fun n t ht => ?_⟩
  rw [hgrid n t ht, Path.extend_apply _ (div_mem_Icc_of_mem_grid ht)]
  rfl

namespace IsPolygonalRayParam

variable {v : ℕ → E} {x : E} {β : ℝ → E}

/-- The ray passes through `v n` at time `1 - 2⁻¹ ^ n`. -/
theorem apply_grid (hβ : IsPolygonalRayParam v x β) (n : ℕ) : β (1 - 2⁻¹ ^ n) = v n := by
  have h2 := two_inv_pow_eq_two_mul n
  have hpos : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
  rw [hβ.2 n _ ⟨le_rfl, by linarith⟩, sub_self, zero_div, AffineMap.lineMap_apply_zero]

/-- On the `n`-th interval of the grid the ray lies on `[v n, v (n + 1)]`. -/
theorem mem_segment (hβ : IsPolygonalRayParam v x β) {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1))) : β t ∈ segment ℝ (v n) (v (n + 1)) := by
  rw [hβ.2 n t ht]
  exact lineMap_mem_segment ℝ _ _ (div_mem_Icc_of_mem_grid ht)

/-- On the `n`-th interval of the grid the ray traces exactly `[v n, v (n + 1)]`. -/
theorem image_Icc_grid (hβ : IsPolygonalRayParam v x β) (n : ℕ) :
    β '' Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) = segment ℝ (v n) (v (n + 1)) := by
  refine Subset.antisymm (image_subset_iff.2 fun t ht => hβ.mem_segment ht) ?_
  rw [segment_eq_image_lineMap]
  rintro _ ⟨s, hs, rfl⟩
  have h2 := two_inv_pow_eq_two_mul n
  have hpos : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
  refine ⟨1 - 2⁻¹ ^ n + s * 2⁻¹ ^ (n + 1), ⟨?_, ?_⟩, ?_⟩
  · nlinarith [hs.1]
  · nlinarith [hs.2]
  · rw [hβ.2 n _ ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩]
    congr 1
    field_simp
    ring

/-- Before time `1` the ray lies on one of the segments. -/
theorem exists_mem_segment (hβ : IsPolygonalRayParam v x β) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ∃ n, β t ∈ segment ℝ (v n) (v (n + 1)) := by
  obtain ⟨n, hn⟩ := exists_mem_grid ht.1 ht.2
  exact ⟨n, hβ.mem_segment hn⟩

/-- **Injectivity of a simple polygonal ray.** If consecutive vertices are distinct, consecutive segments meet
only in their common vertex, non-consecutive segments are disjoint and `x` lies on no segment, then the polygonal
ray parametrisation is injective on `[0, 1]`. -/
theorem injOn (hβ : IsPolygonalRayParam v x β) (hne : ∀ n, v n ≠ v (n + 1))
    (hadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hfar : ∀ n m, n + 2 ≤ m → Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    (hx : ∀ n, x ∉ segment ℝ (v n) (v (n + 1))) : InjOn β (Icc 0 1) := by
  -- the local time determines the point on one segment
  have hloc : ∀ n t₁ t₂, t₁ ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) →
      t₂ ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) → β t₁ = β t₂ → t₁ = t₂ := by
    intro n t₁ t₂ ht₁ ht₂ h
    rw [hβ.2 n t₁ ht₁, hβ.2 n t₂ ht₂] at h
    have hpos : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
    have h' := (div_left_inj' hpos.ne').1 (AffineMap.lineMap_injective ℝ (hne n) h)
    linarith
  -- a point of `[v n, v (n + 1)]` equal to `v (n + 1)` is reached at the end of the interval
  have hend : ∀ n t, t ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) → β t = v (n + 1) →
      t = 1 - 2⁻¹ ^ (n + 1) := by
    intro n t ht h
    rw [hβ.2 n t ht, AffineMap.lineMap_eq_right_iff] at h
    have hpos : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
    have h1 := (div_eq_one_iff_eq hpos.ne').1 (h.resolve_left (hne n))
    have h2 := two_inv_pow_eq_two_mul n
    linarith
  have hstart : ∀ n t, t ∈ Icc (1 - 2⁻¹ ^ n : ℝ) (1 - 2⁻¹ ^ (n + 1)) → β t = v n → t = 1 - 2⁻¹ ^ n := by
    intro n t ht h
    rw [hβ.2 n t ht, AffineMap.lineMap_eq_left_iff] at h
    have hpos : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
    rcases div_eq_zero_iff.1 (h.resolve_left (hne n)) with h1 | h1
    · linarith
    · exact absurd h1 hpos.ne'
  have key : ∀ n₁ n₂ t₁ t₂, n₁ ≤ n₂ → t₁ ∈ Icc (1 - 2⁻¹ ^ n₁ : ℝ) (1 - 2⁻¹ ^ (n₁ + 1)) →
      t₂ ∈ Icc (1 - 2⁻¹ ^ n₂ : ℝ) (1 - 2⁻¹ ^ (n₂ + 1)) → β t₁ = β t₂ → t₁ = t₂ := by
    intro n₁ n₂ t₁ t₂ hn ht₁ ht₂ h
    rcases (show n₁ = n₂ ∨ n₂ = n₁ + 1 ∨ n₁ + 2 ≤ n₂ by omega) with rfl | rfl | hfar'
    · exact hloc n₁ t₁ t₂ ht₁ ht₂ h
    · have hp : β t₁ = v (n₁ + 1) :=
        hadj n₁ ⟨hβ.mem_segment ht₁, by rw [h]; exact hβ.mem_segment ht₂⟩
      rw [hend n₁ t₁ ht₁ hp, hstart (n₁ + 1) t₂ ht₂ (h.symm.trans hp)]
    · exact (Set.disjoint_left.1 (hfar n₁ n₂ hfar') (hβ.mem_segment ht₁)
        (by rw [h]; exact hβ.mem_segment ht₂)).elim
  intro t₁ ht₁ t₂ ht₂ h
  rcases ht₁.2.lt_or_eq with ht₁1 | rfl <;> rcases ht₂.2.lt_or_eq with ht₂1 | rfl
  · obtain ⟨n₁, hn₁⟩ := exists_mem_grid ht₁.1 ht₁1
    obtain ⟨n₂, hn₂⟩ := exists_mem_grid ht₂.1 ht₂1
    rcases le_total n₁ n₂ with hn | hn
    · exact key n₁ n₂ t₁ t₂ hn hn₁ hn₂ h
    · exact (key n₂ n₁ t₂ t₁ hn hn₂ hn₁ h.symm).symm
  · obtain ⟨n₁, hn₁⟩ := exists_mem_grid ht₁.1 ht₁1
    exact absurd (by rw [← hβ.1, ← h]; exact hβ.mem_segment hn₁) (hx n₁)
  · obtain ⟨n₂, hn₂⟩ := exists_mem_grid ht₂.1 ht₂1
    exact absurd (by rw [← hβ.1, h]; exact hβ.mem_segment hn₂) (hx n₂)
  · rfl

end IsPolygonalRayParam

end LatticeProb.Topology
