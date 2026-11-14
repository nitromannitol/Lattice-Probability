import LatticeProb.Euclidean.PolarTemplateArcDiam
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RItinerary

/-!
# Template itineraries from a uniform approximation of the moved polar template

Let `f : ℝ → ℂ` be a path and let `q m` be a point of the cell of the vertex `v m`. Suppose that on
the half-step window `|t - m| ≤ 1/2` the path stays within distance `d` of `q m` (this holds for the
linear interpolation of `m ↦ q m` when consecutive cells intersect and have diameter at most `d`),
and that on a time interval `[a, b]` the path follows the moved polar template
`movedTemplate z r ϑ ∘ φ` within distance `κ`, for a continuous monotone `φ` with `φ a = 0` and
`φ b = 1`. Then the vertices `v m₀, …, v (m₀ + n)` whose half-step windows cover `[a, b]` form a
template walk (`MatedCRTHarmonic.RouteM.IsTemplateWalk`), with template intervals
`[α j, β j] = φ([m₀ + j - 1/2, m₀ + j + 1/2] ∩ [a, b])`, the window clamped to `[a, b]`
(`itinStart`, `itinEnd`).

Nearness of the cells to the template follows from the triangle inequality. The length bound
`β j - α j ≤ 1/50` follows from the arc-diameter lemma `sub_lt_of_diam_movedTemplate_image_Icc_lt`,
since the template arc over `[α j, β j]` stays within `κ` of the path on one half-step window.

## Main statements
* `isTemplateWalk_of_uniform_approx`: the itinerary for an admissible index range `m₀, n`;
* `exists_itinerary_indices`: an admissible index range exists when `0 ≤ a ≤ b`
  (`m₀ = ⌊a + 1/2⌋₊`, and `m₀ + n = ⌈b - 1/2⌉₊` unless `[a, b]` lies in one window).
-/

set_option autoImplicit false

noncomputable section

open Set Real
open MatedCRTHarmonic MatedCRTHarmonic.Topology MatedCRTHarmonic.RouteM MatedCRTHarmonic.CellularEmbedding

namespace LatticeProb.PolarTemplate

/-- Left end of the template interval of the `j`-th vertex of the itinerary: `φ` at the left end
`m₀ + j - 1/2` of its half-step window, clamped to `[a, b]`. -/
def itinStart (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (m₀ j : ℕ) : ℝ :=
  φ (projIcc a b hab ((m₀ : ℝ) + j - 1 / 2))

/-- Right end of the template interval of the `j`-th vertex of the itinerary: `φ` at the right end
`m₀ + j + 1/2` of its half-step window, clamped to `[a, b]`. -/
def itinEnd (φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (m₀ j : ℕ) : ℝ :=
  φ (projIcc a b hab ((m₀ : ℝ) + j + 1 / 2))

/-- **Template itinerary.** A path that follows the moved polar template within `κ` on `[a, b]`
(after a continuous monotone reparametrization `φ` of `[a, b]` onto `[0, 1]`), and stays within `d`
of the points `q m` of the cells of the walk `v` on the half-step windows, makes the walk
`v m₀, …, v (m₀ + n)` a template walk with template intervals `[itinStart j, itinEnd j]`, provided
the half-step windows of `m₀, …, m₀ + n` cover `[a, b]`, the cells have diameter at most `d`, and
`2d + κ ≤ r/60`, `2κ + 2d < r/250`. -/
theorem isTemplateWalk_of_uniform_approx {V E : Type*} {G : LFMultigraph V E} {o : V}
    (H : CellularEmbedding G o) (z : ℂ) {r ϑ κ d a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφm : MonotoneOn φ (Icc a b)) (hφc : ContinuousOn φ (Icc a b)) (hφa : φ a = 0)
    (hφb : φ b = 1) {f : ℝ → ℂ}
    (htube : ∀ t ∈ Icc a b, ‖f t - movedTemplate z r ϑ (φ t)‖ < κ)
    {v : ℕ → V} {q : ℕ → ℂ} {m₀ n : ℕ}
    (ha₁ : (m₀ : ℝ) - 1 / 2 ≤ a) (ha₂ : a ≤ (m₀ : ℝ) + 1 / 2)
    (hb₁ : (m₀ : ℝ) + n - 1 / 2 ≤ b) (hb₂ : b ≤ (m₀ : ℝ) + n + 1 / 2)
    (hadj : ∀ j < n, G.adj.Adj (v (m₀ + j)) (v (m₀ + j + 1)))
    (hq : ∀ j ≤ n, q (m₀ + j) ∈ H.cell (v (m₀ + j)))
    (hdiam : ∀ j ≤ n, Metric.diam (H.cell (v (m₀ + j))) ≤ d)
    (hfq : ∀ j ≤ n, ∀ t ∈ Icc a b, |t - ((m₀ : ℝ) + j)| ≤ 1 / 2 → ‖f t - q (m₀ + j)‖ ≤ d)
    (h60 : 2 * d + κ ≤ r / 60) (h250 : 2 * κ + 2 * d < r / 250) :
    IsTemplateWalk H z r ϑ n (fun j => v (m₀ + j)) (itinStart φ hab m₀) (itinEnd φ hab m₀) := by
  have hmem : ∀ u : ℝ, (projIcc a b hab u : ℝ) ∈ Icc a b := fun u => (projIcc a b hab u).2
  have hd0 : 0 ≤ d := (Metric.diam_nonneg).trans (hdiam 0 (Nat.zero_le n))
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (htube a (left_mem_Icc.2 hab)).le
  -- the clamped window of the `j`-th vertex lies in `[a, b]` and in its half-step window
  have hwin : ∀ j ≤ n, ∀ t ∈ Icc (projIcc a b hab ((m₀ : ℝ) + j - 1 / 2) : ℝ)
      (projIcc a b hab ((m₀ : ℝ) + j + 1 / 2)),
      t ∈ Icc a b ∧ |t - ((m₀ : ℝ) + j)| ≤ 1 / 2 := by
    intro j hj t ht
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : (m₀ : ℝ) + j - 1 / 2 ≤ (projIcc a b hab ((m₀ : ℝ) + j - 1 / 2) : ℝ) := by
      rw [coe_projIcc]
      exact le_max_of_le_right (le_min (by linarith) le_rfl)
    have h2 : (projIcc a b hab ((m₀ : ℝ) + j + 1 / 2) : ℝ) ≤ (m₀ : ℝ) + j + 1 / 2 := by
      rw [coe_projIcc]
      exact max_le (by linarith) (min_le_right _ _)
    exact ⟨⟨(hmem _).1.trans ht.1, ht.2.trans (hmem _).2⟩,
      abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hxy : ∀ j : ℕ, (projIcc a b hab ((m₀ : ℝ) + j - 1 / 2) : ℝ) ≤
      (projIcc a b hab ((m₀ : ℝ) + j + 1 / 2) : ℝ) := fun j =>
    Subtype.coe_le_coe.2 (monotone_projIcc hab (by linarith))
  -- every template time of the interval of the `j`-th vertex is `φ t` for a time `t` of its window
  have himage : ∀ j : ℕ, ∀ s ∈ Icc (itinStart φ hab m₀ j) (itinEnd φ hab m₀ j),
      ∃ t ∈ Icc (projIcc a b hab ((m₀ : ℝ) + j - 1 / 2) : ℝ)
        (projIcc a b hab ((m₀ : ℝ) + j + 1 / 2)), φ t = s := fun j s hs =>
    intermediate_value_Icc (hxy j)
      (hφc.mono (Icc_subset_Icc (hmem _).1 (hmem _).2)) hs
  refine
    { adj := hadj
      α_zero := ?_
      β_last := ?_
      monotone_α := ?_
      monotone_β := ?_
      overlap := ?_
      bounds := ?_
      near := ?_ }
  · show φ (projIcc a b hab ((m₀ : ℝ) + ((0 : ℕ) : ℝ) - 1 / 2) : ℝ) = 0
    rw [Nat.cast_zero, add_zero, projIcc_of_le_left hab ha₁]
    exact hφa
  · show φ (projIcc a b hab ((m₀ : ℝ) + (n : ℝ) + 1 / 2) : ℝ) = 1
    rw [projIcc_of_right_le hab hb₂]
    exact hφb
  · intro j k hjk
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    exact hφm (hmem _) (hmem _) (Subtype.coe_le_coe.2 (monotone_projIcc hab (by linarith)))
  · intro j k hjk
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    exact hφm (hmem _) (hmem _) (Subtype.coe_le_coe.2 (monotone_projIcc hab (by linarith)))
  · intro j _
    refine le_of_eq ?_
    show φ (projIcc a b hab ((m₀ : ℝ) + ((j + 1 : ℕ) : ℝ) - 1 / 2) : ℝ) =
      φ (projIcc a b hab ((m₀ : ℝ) + (j : ℝ) + 1 / 2) : ℝ)
    congr 3
    push_cast
    ring
  · intro j hj
    have hα0 : 0 ≤ itinStart φ hab m₀ j := hφa ▸ hφm (left_mem_Icc.2 hab) (hmem _) (hmem _).1
    have hβ1 : itinEnd φ hab m₀ j ≤ 1 := hφb ▸ hφm (hmem _) (right_mem_Icc.2 hab) (hmem _).2
    refine ⟨hα0, hφm (hmem _) (hmem _) (hxy j), hβ1, ?_⟩
    refine (sub_lt_of_diam_movedTemplate_image_Icc_lt z (r := r) (ϑ := ϑ) hα0 hβ1 ?_).le
    refine lt_of_le_of_lt ?_ h250
    refine Metric.diam_le_of_forall_dist_le (by linarith) ?_
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    obtain ⟨t, ht, rfl⟩ := himage j s hs
    obtain ⟨t', ht', rfl⟩ := himage j s' hs'
    have hW := hwin j hj t ht
    have hW' := hwin j hj t' ht'
    have h1 := htube t hW.1
    have h2 := htube t' hW'.1
    have h3 := hfq j hj t hW.1 hW.2
    have h4 := hfq j hj t' hW'.1 hW'.2
    rw [dist_eq_norm]
    calc ‖movedTemplate z r ϑ (φ t) - movedTemplate z r ϑ (φ t')‖
        = ‖(movedTemplate z r ϑ (φ t) - f t) + (f t - q (m₀ + j)) + (q (m₀ + j) - f t') +
            (f t' - movedTemplate z r ϑ (φ t'))‖ := by congr 1; abel
      _ ≤ ‖movedTemplate z r ϑ (φ t) - f t‖ + ‖f t - q (m₀ + j)‖ + ‖q (m₀ + j) - f t'‖ +
            ‖f t' - movedTemplate z r ϑ (φ t')‖ := norm_add₄_le
      _ ≤ 2 * κ + 2 * d := by
        rw [norm_sub_rev (movedTemplate z r ϑ (φ t)) (f t), norm_sub_rev (q (m₀ + j)) (f t')]
        linarith
  · intro j hj s hs w hw
    obtain ⟨t, ht, rfl⟩ := himage j s hs
    have hW := hwin j hj t ht
    have h1 := htube t hW.1
    have h2 := hfq j hj t hW.1 hW.2
    have h3 : ‖w - q (m₀ + j)‖ ≤ d := by
      rw [← dist_eq_norm]
      exact (Metric.dist_le_diam_of_mem (H.isCompact_cell _).isBounded hw (hq j hj)).trans
        (hdiam j hj)
    calc ‖w - movedTemplate z r ϑ (φ t)‖
        = ‖(w - q (m₀ + j)) + (q (m₀ + j) - f t) + (f t - movedTemplate z r ϑ (φ t))‖ := by
          congr 1; abel
      _ ≤ ‖w - q (m₀ + j)‖ + ‖q (m₀ + j) - f t‖ + ‖f t - movedTemplate z r ϑ (φ t)‖ :=
          norm_add₃_le
      _ < 2 * d + κ := by
        rw [norm_sub_rev (q (m₀ + j)) (f t)]
        linarith
      _ ≤ r / 60 := h60

/-- **Admissible index range.** For `0 ≤ a ≤ b` there are `m₀, n` whose half-step windows
`[m - 1/2, m + 1/2]`, `m₀ ≤ m ≤ m₀ + n`, cover `[a, b]` in the sense required by
`isTemplateWalk_of_uniform_approx`: `m₀ = ⌊a + 1/2⌋₊`, and `m₀ + n = ⌈b - 1/2⌉₊` unless this is
smaller than `m₀` (then `n = 0`). -/
theorem exists_itinerary_indices {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ m₀ n : ℕ, (m₀ : ℝ) - 1 / 2 ≤ a ∧ a ≤ (m₀ : ℝ) + 1 / 2 ∧
      (m₀ : ℝ) + n - 1 / 2 ≤ b ∧ b ≤ (m₀ : ℝ) + n + 1 / 2 := by
  have hf1 : (⌊a + 1 / 2⌋₊ : ℝ) ≤ a + 1 / 2 := Nat.floor_le (by linarith)
  have hf2 : a + 1 / 2 < ⌊a + 1 / 2⌋₊ + 1 := Nat.lt_floor_add_one _
  have hc1 : b - 1 / 2 ≤ ⌈b - 1 / 2⌉₊ := Nat.le_ceil _
  have hc2 : (⌈b - 1 / 2⌉₊ : ℝ) - 1 / 2 ≤ b := by
    rcases le_or_gt 0 (b - 1 / 2) with hb | hb
    · linarith [Nat.ceil_lt_add_one hb]
    · rw [Nat.ceil_eq_zero.2 hb.le, Nat.cast_zero]
      linarith
  rcases le_total ⌊a + 1 / 2⌋₊ ⌈b - 1 / 2⌉₊ with h | h
  · refine ⟨⌊a + 1 / 2⌋₊, ⌈b - 1 / 2⌉₊ - ⌊a + 1 / 2⌋₊, by linarith, by linarith, ?_, ?_⟩
    · rw [Nat.cast_sub h]
      linarith
    · rw [Nat.cast_sub h]
      linarith
  · have h' : (⌈b - 1 / 2⌉₊ : ℝ) ≤ ⌊a + 1 / 2⌋₊ := by exact_mod_cast h
    refine ⟨⌊a + 1 / 2⌋₊, 0, by linarith, by linarith, ?_, ?_⟩
    · rw [Nat.cast_zero, add_zero]
      linarith
    · rw [Nat.cast_zero, add_zero]
      linarith

end LatticeProb.PolarTemplate
