/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Cells at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Energy
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting

/-!
# Cells of a cellular embedding and the density `u^ε` of GMS [18] (2.12)

Source: GMS [18] : the cells `H_x` and the vertex sets
`V(D) = {x : H_x ∩ D ≠ ∅}` of (1.3)–(1.5), and the density (2.12)
`u^ε(z) = diam(H_{x_z})² deg(x_z) / area(H_{x_z})`, where `H_{x_z}` is "the (a.s. unique) cell containing
`z`". The cells are those of the frozen `CellularEmbedding` (the cellular embedding definition: compact,
connected, nonempty interior, locally finite, covering `ℂ`, Lebesgue-null pairwise intersections, adjacent
cells intersect); the mated-CRT cells `η([x − ε, x])` are an instance, as encoded by
`MatedCRT.IsCellCoupling`.

* `vFin H D`: `V(D)` as a `Finset` (finite for bounded `D`, `finite_verticesMeeting`; `mem_vFin`).
* `cellDiam H x = diam(H_x)`, `uCoef H x = diam(H_x)² deg(x) / area(H_x)` and
  `uDens H z = ∑_{x : z ∈ H_x} uCoef H x`: the density (2.12) without a selection of `x_z`; it agrees almost
  everywhere with the selection form (`uDens_ae_eq`), since almost every point lies in exactly one cell.
* `setLIntegral_cell_uDens`: `∫_{H_x} u = diam(H_x)² deg(x)` (the identity behind [18] (3.5));
  `setLIntegral_biUnion_cell`: integrals over unions of cells are sums over the cells.
* `cell_subset_of_inter_frontier_eq_empty`: a cell meeting the open set `D` but not `∂D` lies in `D`
  ([18] "interior cells"); `mem_vFin_of_adj_of_subset`: its neighbours then lie in `V(D)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-! ### Basic properties of the cells -/

theorem measurableSet_cell (x : V) : MeasurableSet (H.cell x) :=
  (H.isCompact_cell x).isClosed.measurableSet

theorem volume_cell_ne_top (x : V) : volume (H.cell x) ≠ ⊤ :=
  (H.isCompact_cell x).measure_lt_top.ne

theorem volume_cell_pos (x : V) : 0 < volume (H.cell x) :=
  Measure.measure_pos_of_nonempty_interior _ (H.interior_cell_nonempty x)

theorem cell_nonempty (x : V) : (H.cell x).Nonempty :=
  (H.interior_cell_nonempty x).mono interior_subset

include H in
/-- A cellular embedding has countably many vertices (locally finite nonempty cells in `ℂ`). -/
theorem countable_vertex : Countable V :=
  Set.countable_univ_iff.mp (H.locallyFinite_cell.countable_univ (cell_nonempty H))

/-- `V(D)` is finite for bounded `D`. -/
theorem finite_verticesMeeting {D : Set ℂ} (hD : Bornology.IsBounded D) :
    (verticesMeeting H.cell D).Finite := by
  refine (H.locallyFinite_cell.finite_nonempty_inter_compact hD.isCompact_closure).subset ?_
  intro x hx
  obtain ⟨z, hz1, hz2⟩ := hx
  exact ⟨z, hz1, subset_closure hz2⟩

/-- `V(D) = {x : H_x ∩ D ≠ ∅}` as a `Finset` (empty if `V(D)` is infinite, which never happens for
bounded `D`). -/
def vFin (D : Set ℂ) : Finset V :=
  if h : (verticesMeeting H.cell D).Finite then h.toFinset else ∅

theorem mem_vFin {D : Set ℂ} (hD : Bornology.IsBounded D) {x : V} :
    x ∈ vFin H D ↔ (H.cell x ∩ D).Nonempty := by
  unfold vFin
  rw [dite_eq_left (finite_verticesMeeting H hD), Set.Finite.mem_toFinset]
  rfl

theorem vFin_mono {D D' : Set ℂ} (hD' : Bornology.IsBounded D') (h : D ⊆ D') :
    vFin H D ⊆ vFin H D' := by
  intro x hx
  have hD : Bornology.IsBounded D := hD'.subset h
  rw [mem_vFin H hD] at hx
  rw [mem_vFin H hD']
  exact hx.mono (Set.inter_subset_inter_right _ h)

/-- `diam(H_x)`. -/
def cellDiam (x : V) : ℝ := diam (H.cell x)

theorem cellDiam_nonneg (x : V) : 0 ≤ cellDiam H x := diam_nonneg

theorem dist_le_cellDiam {x : V} {z w : ℂ} (hz : z ∈ H.cell x) (hw : w ∈ H.cell x) :
    dist z w ≤ cellDiam H x :=
  dist_le_diam_of_mem (H.isCompact_cell x).isBounded hz hw

/-- Points of adjacent cells are at distance at most the sum of the diameters. -/
theorem dist_le_cellDiam_add_of_adj {x y : V} (hadj : G.adj.Adj x y) {z w : ℂ}
    (hz : z ∈ H.cell x) (hw : w ∈ H.cell y) : dist z w ≤ cellDiam H x + cellDiam H y := by
  obtain ⟨c, hcx, hcy⟩ := H.inter_of_adj x y hadj
  calc dist z w ≤ dist z c + dist c w := dist_triangle _ _ _
    _ ≤ cellDiam H x + cellDiam H y := add_le_add (dist_le_cellDiam H hz hcx)
        (dist_le_cellDiam H hcy hw)

/-- A cell meeting the open set `D` but not its frontier lies in `D`. -/
theorem cell_subset_of_inter_frontier_eq_empty {D : Set ℂ} (hD : IsOpen D) {x : V}
    (hmeet : (H.cell x ∩ D).Nonempty) (hfr : H.cell x ∩ frontier D = ∅) : H.cell x ⊆ D := by
  have hcover : H.cell x ⊆ D ∪ (closure D)ᶜ := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · refine Or.inr fun hzc => ?_
      have : z ∈ frontier D := by
        rw [frontier, hD.interior_eq]
        exact ⟨hzc, hzD⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hfr) z ⟨hz, this⟩
  rcases (H.isConnected_cell x).isPreconnected.subset_or_subset hD isClosed_closure.isOpen_compl
    (Disjoint.mono_left subset_closure disjoint_compl_right) hcover with h | h
  · exact h
  · obtain ⟨z, hz1, hz2⟩ := hmeet
    exact absurd (subset_closure hz2) (h hz1)

/-- The neighbours of a vertex whose cell lies in `D` lie in `V(D)`. -/
theorem mem_vFin_of_adj_of_subset {D : Set ℂ} (hD : Bornology.IsBounded D) {x y : V}
    (hsub : H.cell x ⊆ D) (hadj : G.adj.Adj x y) : y ∈ vFin H D := by
  rw [mem_vFin H hD]
  obtain ⟨c, hcx, hcy⟩ := H.inter_of_adj x y hadj
  exact ⟨c, hcy, hsub hcx⟩

/-- The heads of the darts at a vertex whose cell lies in `D` lie in `V(D)` (loops included). -/
theorem dtgt_mem_vFin_of_subset {D : Set ℂ} (hD : Bornology.IsBounded D) {x : V}
    (hsub : H.cell x ⊆ D) (hx : x ∈ vFin H D) {d : G.Dart} (hd : d ∈ G.outDarts x) :
    G.dtgt d ∈ vFin H D := by
  by_cases hloop : G.dtgt d = x
  · rw [hloop]; exact hx
  · have hsrc := (mem_outDarts G).mp hd
    have hadj : G.adj.Adj x (G.dtgt d) := by
      rcases d with ⟨e, b⟩
      cases b
      · rw [← hsrc]; exact adj_of_edge G (by rw [← hsrc] at hloop; exact fun h => hloop h.symm)
      · rw [← hsrc]
        exact (adj_of_edge G (by rw [← hsrc] at hloop; exact hloop)).symm
    exact mem_vFin_of_adj_of_subset H hD hsub hadj

/-! ### The density `u^ε` -/

/-- `diam(H_x)² deg(x) / area(H_x)`, the value of `u^ε` on the cell `H_x` ([18] (2.12)). -/
def uCoef (x : V) : ℝ≥0∞ := ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) / volume (H.cell x)

/-- The density `u^ε` of [18] (2.12), selection-free: `∑_{x : z ∈ H_x} diam(H_x)² deg(x)/area(H_x)`.
It agrees a.e. with the selection form (`uDens_ae_eq`). -/
def uDens (z : ℂ) : ℝ≥0∞ := ∑' x, (H.cell x).indicator (fun _ => uCoef H x) z

theorem measurable_uDens : Measurable (uDens H) := by
  have := countable_vertex H
  exact Measurable.tsum fun x =>
    (measurable_const.indicator (measurableSet_cell H x))

theorem uCoef_mul_volume (x : V) :
    uCoef H x * volume (H.cell x) = ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) :=
  ENNReal.div_mul_cancel (volume_cell_pos H x).ne' (volume_cell_ne_top H x)

/-- `uCoef` in the real form of [18] (2.12). -/
theorem uCoef_eq_ofReal (x : V) :
    uCoef H x = ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x / (volume (H.cell x)).toReal) := by
  unfold uCoef
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (volume_cell_pos H x).ne'
    (volume_cell_ne_top H x)), ENNReal.ofReal_toReal (volume_cell_ne_top H x)]

/-- **`∫_{H_x} u^ε = diam(H_x)² deg(x)`** ([18] (3.5)). -/
theorem setLIntegral_cell_uDens (x : V) :
    ∫⁻ z in H.cell x, uDens H z = ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) := by
  have := countable_vertex H
  unfold uDens
  rw [lintegral_tsum fun y => (measurable_const.indicator (measurableSet_cell H y)).aemeasurable]
  have hterm (y : V) : ∫⁻ z in H.cell x, (H.cell y).indicator (fun _ => uCoef H y) z =
      uCoef H y * volume (H.cell y ∩ H.cell x) := by
    rw [lintegral_indicator_const (measurableSet_cell H y), Measure.restrict_apply
      (measurableSet_cell H y)]
  simp_rw [hterm]
  rw [tsum_eq_single x fun y hy => by rw [H.volume_inter_cell y x hy, mul_zero],
    Set.inter_self, uCoef_mul_volume]

/-- Integrals over a finite union of cells are sums over the cells (the cells overlap in null sets). -/
theorem setLIntegral_biUnion_cell (S : Finset V) (F : ℂ → ℝ≥0∞) :
    ∫⁻ z in ⋃ x ∈ S, H.cell x, F z = ∑ x ∈ S, ∫⁻ z in H.cell x, F z := by
  refine lintegral_biUnion_finset₀ ?_ (fun x _ => (measurableSet_cell H x).nullMeasurableSet) F
  intro x _ y _ hxy
  exact H.volume_inter_cell x y hxy

/-- **`u^ε` is the density (2.12) a.e.**: for any selection `c` of a cell containing each point,
`uDens H = uCoef H ∘ c` almost everywhere. -/
theorem uDens_ae_eq (c : ℂ → V) (hc : ∀ z, z ∈ H.cell (c z)) :
    uDens H =ᵐ[volume] fun z => uCoef H (c z) := by
  have := countable_vertex H
  have hnull : volume (⋃ p : {p : V × V // p.1 ≠ p.2}, H.cell p.1.1 ∩ H.cell p.1.2) = 0 :=
    measure_iUnion_null fun p => H.volume_inter_cell _ _ p.2
  refine measure_mono_null (fun z hz => ?_) hnull
  by_contra hz'
  simp only [Set.mem_iUnion, Set.mem_inter_iff, not_exists, not_and] at hz'
  apply hz
  show uDens H z = uCoef H (c z)
  unfold uDens
  rw [tsum_eq_single (c z) fun y hy => Set.indicator_of_notMem
      (fun hzy => hz' ⟨(y, c z), hy⟩ hzy (hc z)) _,
    Set.indicator_of_mem (hc z)]

end MatedCRTHarmonic.GMS3
