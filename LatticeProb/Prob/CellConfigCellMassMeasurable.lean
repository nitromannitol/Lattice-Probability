import LatticeProb.Prob.DyadicCellConfig
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots

/-!
# Measurability of the cell mass of a cell configuration

The cell mass of a set `S` for a cell configuration `H` (Gwynne, Miller and Sheffield, *An
invariance principle for ergodic scale-free random environments*, arXiv 1807.07515, (2.1)) is the
sum over the cells `K` of `H` of the fraction `|K ∩ S| / |K|` of their area lying in `S`. Every cell
of a cell configuration carries a unique least rational interior label, so the sum over the cells
is the sum over the label slots of the configuration. Each slot is a measurable function of the
configuration on the space `GMSSpace` of cell configurations (with the Borel structure of its
Hausdorff topology), and the area fraction is a measurable function of the cell by Tonelli's
theorem. Hence the cell mass of a fixed measurable set is a measurable function of the
configuration.

## Main statements

* `LatticeProb.CellConfigCappedSquare.measurable_volume_inter`: `K ↦ |K ∩ S|` is measurable on
  nonempty compact sets, for measurable `S`.
* `LatticeProb.CellConfigCappedSquare.cellMass_planeCells_eq_tsum_slotMass`: the cell mass is the
  sum over the label slots.
* `LatticeProb.CellConfigCappedSquare.measurable_cellMass_planeCells` and
  `measurable_cellMass_complexCells`: the cell mass of a fixed measurable set is a measurable
  function of the configuration.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass

/-- The area of the part of a cell lying in a measurable set is a measurable function of the
cell (Tonelli's theorem on the closed set `{(K, z) | z ∈ K}`). -/
theorem measurable_volume_inter {S : Set Plane} (hS : MeasurableSet S) :
    Measurable fun K : Code.CompactCell => volume ((K : Set Plane) ∩ S) := by
  have hE : MeasurableSet {p : Code.CompactCell × Plane | p.2 ∈ (p.1 : Set Plane) ∩ S} :=
    Spatial.measurableSet_cellMem.inter (measurable_snd hS)
  have h : (fun K : Code.CompactCell => volume ((K : Set Plane) ∩ S)) = fun K =>
      ∫⁻ z, {p : Code.CompactCell × Plane | p.2 ∈ (p.1 : Set Plane) ∩ S}.indicator
        (fun _ => (1 : ℝ≥0∞)) (K, z) := by
    funext K
    rw [← lintegral_indicator_one (K.isCompact.isClosed.measurableSet.inter hS)]
    rfl
  rw [h]
  exact (measurable_const.indicator hE).lintegral_prod_right' (ν := (volume : Measure Plane))

/-- The fraction `|K ∩ S| / |K|` of the area of the cell `K` lying in `S`. -/
noncomputable def cellFraction (S : Set Plane) (K : Code.CompactCell) : ℝ≥0∞ :=
  volume ((K : Set Plane) ∩ S) / volume (K : Set Plane)

theorem measurable_cellFraction {S : Set Plane} (hS : MeasurableSet S) :
    Measurable (cellFraction S) :=
  (measurable_volume_inter hS).div Spatial.measurable_cellVolume

/-- The contribution of the label slot `n` of a cell configuration to the cell mass of `S`. -/
noncomputable def slotMass (S : Set Plane) (H : CellConfig) (n : ℕ) : ℝ≥0∞ :=
  (H.slot n).elim 0 (cellFraction S)

theorem leastInteriorLabel_unique {K : Code.CompactCell} {a b : ℕ}
    (ha : Code.LeastInteriorLabel K a) (hb : Code.LeastInteriorLabel K b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd ha.1 (hb.2 a h)
  · exact h
  · exact absurd hb.1 (ha.2 b h)

/-- **The cell mass is the sum over the label slots.** -/
theorem cellMass_planeCells_eq_tsum_slotMass {H : CellConfig} (hH : H.IsCellConfiguration)
    (S : Set Plane) : cellMass volume (planeCells H) S = ∑' n, slotMass S H n := by
  have hinj : Function.Injective (CellConfig.label hH) := by
    intro K K' h
    have h1 := CellConfig.slot_label hH K
    have h2 := CellConfig.slot_label hH K'
    rw [h] at h1
    exact Subtype.ext (Option.some_inj.mp (h1.symm.trans h2))
  have hsupp : Function.support (slotMass S H) ⊆ Set.range (CellConfig.label hH) := by
    intro n hn
    cases hs : H.slot n with
    | none =>
      exact absurd (by simp only [slotMass, hs, Option.elim]) hn
    | some K =>
      obtain ⟨hK, hl⟩ := (CellConfig.slot_eq_some_iff hH).1 hs
      exact ⟨⟨K, hK⟩, leastInteriorLabel_unique (CellConfig.leastInteriorLabel_label hH ⟨K, hK⟩) hl⟩
  rw [← hinj.tsum_eq hsupp]
  unfold cellMass
  congr 1
  funext K
  simp only [slotMass, CellConfig.slot_label hH K, Option.elim, cellFraction, planeCells]

theorem slotMass_eq_indicator (S : Set Plane) (H : GMSSpace) (n : ℕ) :
    slotMass S H.1 n =
      (labelSet n).indicator (fun H => cellFraction S (interiorCell (Code.rationalPoint n) H)) H := by
  by_cases h : H ∈ labelSet n
  · rw [slotMass, slot_eq, Set.indicator_of_mem h]
    simp only [h, ↓reduceIte, Option.elim]
  · rw [slotMass, slot_eq, Set.indicator_of_notMem h]
    simp only [h, ↓reduceIte, Option.elim]

theorem measurable_slotMass {S : Set Plane} (hS : MeasurableSet S) (n : ℕ) :
    Measurable fun H : GMSSpace => slotMass S H.1 n := by
  have h : (fun H : GMSSpace => slotMass S H.1 n) =
      (labelSet n).indicator (fun H => cellFraction S (interiorCell (Code.rationalPoint n) H)) :=
    funext fun H => slotMass_eq_indicator S H n
  rw [h]
  exact ((measurable_cellFraction hS).comp (measurable_interiorCell _)).indicator
    (measurableSet_labelSet n)

/-- **The cell mass of a fixed measurable set is a measurable function of the configuration.** -/
theorem measurable_cellMass_planeCells {S : Set Plane} (hS : MeasurableSet S) :
    Measurable fun H : GMSSpace => cellMass volume (planeCells H.1) S := by
  have h : (fun H : GMSSpace => cellMass volume (planeCells H.1) S) =
      fun H => ∑' n, slotMass S H.1 n :=
    funext fun H => cellMass_planeCells_eq_tsum_slotMass H.2 S
  rw [h]
  exact Measurable.tsum fun n => measurable_slotMass hS n

/-- The cell mass of a fixed measurable subset of `ℂ` for the cells pulled back to `ℂ` is a
measurable function of the configuration. -/
theorem measurable_cellMass_complexCells {S : Set ℂ} (hS : MeasurableSet S) :
    Measurable fun H : GMSSpace => cellMass volume (complexCells H.1) S := by
  have h : (fun H : GMSSpace => cellMass volume (complexCells H.1) S) =
      fun H => cellMass volume (planeCells H.1) (planeCoord '' S) :=
    funext fun H => cellMass_complexCells S
  rw [h]
  exact measurable_cellMass_planeCells (planeCoordMeas.measurableSet_image.2 hS)

end LatticeProb.CellConfigCappedSquare
