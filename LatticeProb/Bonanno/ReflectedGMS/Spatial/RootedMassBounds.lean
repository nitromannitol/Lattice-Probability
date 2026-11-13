/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.RootedMassBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots

/-!
# Rooted cell selection and the neighbourhood mass transport

This file supplies the upstream input for the local geometric mass
`W(R) = ∑_{H hits a bounded patch} d_H ^ 2 (π_H + π*_H)`: the *scale invariant*
neighbourhood transport of the reflected-GMS manuscript, together with the
boundary-masked (`RootDensities.rootAt`) densities it produces.

The transport is
`T(𝓗, w, z) = ∑_H 1_{w ∈ int H} 1_{z ∈ N(H)} / a_H`,
where `N(H) = {z | infDist z H ≤ diam H}` is the neighbourhood of `H` at `H`'s
own scale.  Both `infDist` and `diam` scale by the *same* factor `s` under the
manuscript similarity `S(s,u) z = s • (z - u)`, so `N(·)` is exactly covariant,
`a_H` scales by `s ^ 2`, and the transport is `(s ^ 2)⁻¹`-covariant: it really is
an `EnvironmentLaws.MassTransportKernel`.  Nothing here assumes stationarity, a
mass-transport identity for this kernel, or any canonical similarity action: the
covariance consumes an `EnvironmentLaws.IsSimilarity` witness directly, and the
existing law `EnvironmentLaws.MassTransport` is then invoked.

The two integrals are computed exactly:

* outgoing from the origin, off the boundary mask, is the rooted density
  `volume (N (H_0)) / a_{H_0}`, because the interior root is unique;
* incoming at the origin is the *count* `∑_H 1_{0 ∈ N(H)}` of cells that are
  near the origin at their own scale, because `volume (interior H) = a_H` for a
  null-boundary cell.

Mass transport therefore turns the expected near-origin cell count into the
rooted diameter moment `E[d_{H_0} ^ 2 / a_{H_0}]` (Lebesgue area of a ball
bounds `volume (N H)` by `4 d_H ^ 2`).  This is the large-cell control needed by
the local geometric mass.

Remaining step exposed to the consumer (deliberately not proved here): the
manuscript's finite-energy moment is
`E[rootedFiniteEnergyDensity] = E[(d² / a)(H_0) * (π + π*)(H_0)]`, so bounding
`∫⁻ rootedDiamSqAreaDensity` by it needs exactly the pointwise inequality
`1 ≤ ENNReal.ofReal (π (H_0) + π* (H_0))`, i.e. the AM–GM bound
`π_H + π*_H = ∑_{H' ~ H} (c + c⁻¹) ≥ 2 deg(H) ≥ 1` for a vertex of positive
degree. `rootedDiamSqAreaDensity_eq_ofReal_cellArea` below already rewrites the
density in the exact `ENNReal.ofReal (cellArea ·)` denominator used by
`RootDensities.finiteEnergyDensity`, so only that conductance factor is missing.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Pointwise

namespace ReflectedGMS.Spatial

open Code EnvironmentLaws

variable {V : Type*}

/-! ### The cell diameter is continuous for the Hausdorff Borel structure -/

/-- Moving a nonempty compact cell by Hausdorff distance `t` changes its
diameter by at most `2 t`. -/
theorem cellDiam_le_add_two_dist (K L : CompactCell) :
    Metric.diam (K : Set Plane) ≤ Metric.diam (L : Set Plane) + 2 * dist K L := by
  have hdiamL : (0 : ℝ) ≤ Metric.diam (L : Set Plane) := Metric.diam_nonneg
  have hdistKL : (0 : ℝ) ≤ dist K L := dist_nonneg
  refine Metric.diam_le_of_forall_dist_le (by linarith) ?_
  intro x hx y hy
  refine _root_.le_of_forall_pos_le_add ?_
  intro ε hε
  have hfin : Metric.hausdorffEDist (K : Set Plane) (L : Set Plane) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty L.nonempty
      K.isCompact.isBounded L.isCompact.isBounded
  have hdist : dist K L = Metric.hausdorffDist (K : Set Plane) (L : Set Plane) :=
    NonemptyCompacts.dist_eq
  have hlt : Metric.hausdorffDist (K : Set Plane) (L : Set Plane) < dist K L + ε / 2 := by
    rw [hdist]
    linarith
  obtain ⟨x', hx', hxx'⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx hlt hfin
  obtain ⟨y', hy', hyy'⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hy hlt hfin
  have hxy' : dist x' y' ≤ Metric.diam (L : Set Plane) :=
    Metric.dist_le_diam_of_mem L.isCompact.isBounded hx' hy'
  have htri : dist x y ≤ dist x x' + dist x' y' + dist y' y := dist_triangle4 x x' y' y
  have hsymm : dist y' y = dist y y' := dist_comm y' y
  linarith

theorem lipschitzWith_cellDiam :
    LipschitzWith 2 fun K : CompactCell => Metric.diam (K : Set Plane) :=
  LipschitzWith.of_le_add_mul 2 fun K L => by
    have h := cellDiam_le_add_two_dist K L
    simpa using h

theorem continuous_cellDiam :
    Continuous fun K : CompactCell => Metric.diam (K : Set Plane) :=
  lipschitzWith_cellDiam.continuous

theorem measurable_cellDiam :
    Measurable fun K : CompactCell => Metric.diam (K : Set Plane) :=
  continuous_cellDiam.measurable

/-! ### The scale-covariant neighbourhood of a cell -/

/-! ### Exact scaling of `infDist` and `diam` under the manuscript similarity -/

theorem isometry_translation (c : Plane) : Isometry fun y : Plane => c + y :=
  Isometry.of_dist_eq fun x y => by
    simp [dist_eq_norm, add_sub_add_left_eq_sub]

theorem positiveSimilarity_eq_comp (s : ℝ) (u : Plane) :
    positiveSimilarity s u
      = (fun y : Plane => -(s • u) + y) ∘ fun z : Plane => s • z := by
  funext z
  show s • (z - u) = -(s • u) + s • z
  rw [smul_sub, sub_eq_neg_add]

theorem diam_image_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (A : Set Plane) :
    Metric.diam (positiveSimilarity s u '' A) = s * Metric.diam A := by
  rw [positiveSimilarity_eq_comp, Set.image_comp,
    (isometry_translation (-(s • u))).diam_image, Set.image_smul, diam_smul₀,
    Real.norm_eq_abs, abs_of_pos hs]

theorem infDist_image_positiveSimilarity (s : ℝ) (u : Plane) (hs : 0 < s)
    (A : Set Plane) (z : Plane) :
    Metric.infDist (positiveSimilarity s u z) (positiveSimilarity s u '' A)
      = s * Metric.infDist z A := by
  have himg : positiveSimilarity s u '' A = (fun y : Plane => -(s • u) + y) '' (s • A) := by
    rw [positiveSimilarity_eq_comp, Set.image_comp, Set.image_smul]
  have hpt : positiveSimilarity s u z = (fun y : Plane => -(s • u) + y) (s • z) := by
    show s • (z - u) = -(s • u) + s • z
    rw [smul_sub, sub_eq_neg_add]
  have h1 : Metric.infDist ((fun y : Plane => -(s • u) + y) (s • z))
      ((fun y : Plane => -(s • u) + y) '' (s • A)) = Metric.infDist (s • z) (s • A) :=
    Metric.infDist_image (isometry_translation (-(s • u)))
  have h2 : Metric.infDist (s • z) (s • A) = ‖s‖ * Metric.infDist z A :=
    infDist_smul₀ (ne_of_gt hs) A z
  rw [himg, hpt, h1, h2, Real.norm_eq_abs, abs_of_pos hs]

/-- Interior membership is covariant as well. -/
theorem mem_interior_transformCell_iff (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : CompactCell) (w : Plane) :
    positiveSimilarity s u w ∈ interior ((transformCell s u hs K : CompactCell) : Set Plane)
      ↔ w ∈ interior (K : Set Plane) := by
  have hhom : ⇑(positiveSimilarityHomeomorph s u hs) = positiveSimilarity s u := rfl
  have hinj : Function.Injective (positiveSimilarity s u) := by
    rw [← hhom]
    exact (positiveSimilarityHomeomorph s u hs).injective
  have hint : interior ((transformCell s u hs K : CompactCell) : Set Plane)
      = positiveSimilarity s u '' interior (K : Set Plane) := by
    have himg := (positiveSimilarityHomeomorph s u hs).image_interior (K : Set Plane)
    rw [coe_transformCell]
    exact himg.symm
  rw [hint]
  exact hinj.mem_set_image

/-- Indicators of corresponding sets agree once the membership conditions do. -/
theorem indicator_one_congr_of_iff {A B : Set Plane} {x y : Plane} (h : y ∈ B ↔ x ∈ A) :
    Set.indicator B (fun _ => (1 : ℝ≥0∞)) y = Set.indicator A (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem (h.mpr hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem fun hy => hx (h.mp hy), Set.indicator_of_notMem hx]

/-! ### The neighbourhood transport of a single cell -/

/-! ### Slot and environment level transport -/

/-! ### Outgoing and incoming integrals -/

/-- For a cell with null frontier the interior carries the full area. -/
theorem volume_interior_eq_of_frontier_null {K : CompactCell}
    (hfront : volume (frontier (K : Set Plane)) = 0) :
    volume (interior (K : Set Plane)) = volume (K : Set Plane) := by
  refine le_antisymm (measure_mono interior_subset) ?_
  have hsub : (K : Set Plane) ⊆ interior (K : Set Plane) ∪ frontier (K : Set Plane) := by
    intro x hx
    by_cases hint : x ∈ interior (K : Set Plane)
    · exact Or.inl hint
    · refine Or.inr ?_
      rw [K.isCompact.isClosed.frontier_eq]
      exact ⟨hx, hint⟩
  calc volume (K : Set Plane)
      ≤ volume (interior (K : Set Plane) ∪ frontier (K : Set Plane)) := measure_mono hsub
    _ ≤ volume (interior (K : Set Plane)) + volume (frontier (K : Set Plane)) :=
        measure_union_le _ _
    _ = volume (interior (K : Set Plane)) := by rw [hfront, add_zero]

/-! ### Rooted densities and the near-cell count -/

/-- The boundary-masked diameter density `d_H ^ 2 / a_H` of the rooted cell:
exactly the geometric factor of `RootDensities.finiteEnergyDensity`. -/
noncomputable def rootedDiamSqAreaDensity (F : IndexedCells V) (z : Plane) : ℝ≥0∞ :=
  (RootDensities.rootAt F z).elim 0 fun v =>
    ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) / volume (F.cell v : Set Plane)

/-- The rooted diameter density in the exact `cellArea` denominator used by
`RootDensities.finiteEnergyDensity`. -/
theorem rootedDiamSqAreaDensity_eq_ofReal_cellArea [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (z : Plane) :
    rootedDiamSqAreaDensity F z
      = (RootDensities.rootAt F z).elim 0 fun v =>
          ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
            ENNReal.ofReal (StatementIngredients.cellArea F v) := by
  cases hroot : RootDensities.rootAt F z with
  | none => simp [rootedDiamSqAreaDensity, hroot]
  | some v =>
      have harea : ENNReal.ofReal (StatementIngredients.cellArea F v)
          = volume (F.cell v : Set Plane) := by
        rw [StatementIngredients.cellArea,
          ENNReal.ofReal_toReal (cellVolume_pos_lt_top F hF v).2.ne]
      simp [rootedDiamSqAreaDensity, hroot, harea]

/-! ### Mass transport: the near-origin cell count and the diameter moment -/

end ReflectedGMS.Spatial
