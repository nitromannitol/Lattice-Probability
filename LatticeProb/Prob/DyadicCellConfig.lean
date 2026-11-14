import LatticeProb.Prob.DyadicExhaustion
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-!
# Capped squares of a cell configuration

A cell configuration in the sense of Gwynne, Miller and Sheffield (*Harmonic functions on mated-CRT
maps*, arXiv 1807.07511, Definition 1.15; `ReflectedGMS.GMS.CellConfig.IsCellConfiguration`) lives
in `Plane = EuclideanSpace ℝ (Fin 2)`. We pull its cells back to `ℂ` by the coordinates
`z ↦ (Re z, Im z)` (the orthonormal basis `1, i`) and check the hypotheses of the existence of the
capped squares `S_m^w` of Gwynne, Miller and Sheffield (*An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515, (2.1) and Lemma 2.2): the pulled-back cells
form a countable, locally finite cover of `ℂ` by compact sets of positive area. Their cell mass is
the cell mass of the configuration, computed in `Plane`.

## Main statements

* `LatticeProb.CellConfigCappedSquare.countable_cells`: the cells of a cell configuration form a
  countable set.
* `LatticeProb.CellConfigCappedSquare.cellMass_complexCells`: the cell mass of the pulled-back
  cells is the cell mass of the configuration.
* `LatticeProb.CellConfigCappedSquare.ae_exists_isCappedSquare_squareAt`: for every cell
  configuration and every point `w`, almost surely in the uniform dyadic system, the capped square
  of every mass `m ∈ (0, ∞)` around `w` exists and is a square of the chain at `w`.
-/

open MeasureTheory Set Topology
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- The coordinates `z ↦ (Re z, Im z)` of `ℂ` in the orthonormal basis `1, i`, as a linear
isometry onto `Plane`. -/
noncomputable abbrev planeCoord : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

/-- The coordinates as a measurable equivalence. -/
noncomputable abbrev planeCoordMeas : ℂ ≃ᵐ Plane := planeCoord.toHomeomorph.toMeasurableEquiv

theorem measurePreserving_planeCoordMeas :
    MeasurePreserving planeCoordMeas (volume : Measure ℂ) (volume : Measure Plane) :=
  planeCoord.measurePreserving

/-- The cells of a cell configuration, pulled back to `ℂ`. -/
def complexCells (H : CellConfig) : H.cells → Set ℂ :=
  fun K => planeCoord ⁻¹' (K.1 : Set Plane)

/-- The cells of a cell configuration, as an indexed family in `Plane`. -/
def planeCells (H : CellConfig) : H.cells → Set Plane :=
  fun K => (K.1 : Set Plane)

variable {H : CellConfig}

theorem complexCells_nonempty (K : H.cells) : (complexCells H K).Nonempty := by
  obtain ⟨p, hp⟩ := K.1.nonempty
  refine ⟨planeCoord.symm p, ?_⟩
  show planeCoord (planeCoord.symm p) ∈ (K.1 : Set Plane)
  rwa [LinearIsometryEquiv.apply_symm_apply]

theorem isCompact_complexCells (K : H.cells) : IsCompact (complexCells H K) :=
  (planeCoord.toHomeomorph.isCompact_preimage).2 K.1.isCompact

theorem volume_complexCells (K : H.cells) :
    volume (complexCells H K) = volume (K.1 : Set Plane) :=
  measurePreserving_planeCoordMeas.measure_preimage_equiv _

/-- The cell mass of the pulled-back cells is the cell mass of the configuration in `Plane`. -/
theorem cellMass_complexCells (S : Set ℂ) :
    cellMass volume (complexCells H) S = cellMass volume (planeCells H) (planeCoord '' S) := by
  unfold cellMass
  congr 1
  funext K
  have hS : planeCoord ⁻¹' (planeCoord '' S) = S :=
    planeCoord.toEquiv.injective.preimage_image S
  have h : complexCells H K ∩ S = planeCoordMeas ⁻¹' ((K.1 : Set Plane) ∩ planeCoord '' S) := by
    rw [preimage_inter]
    exact congrArg _ hS.symm
  rw [h, measurePreserving_planeCoordMeas.measure_preimage_equiv, volume_complexCells]
  rfl

variable (hH : H.IsCellConfiguration)
include hH

theorem locallyFinite_complexCells : LocallyFinite (complexCells H) := by
  intro z
  obtain ⟨U, hU, hfin⟩ := hH.locallyFinite (planeCoord z)
  refine ⟨planeCoord ⁻¹' U, planeCoord.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro K ⟨x, hxK, hxU⟩
  exact ⟨K.2, planeCoord x, hxK, hxU⟩

/-- The cells of a cell configuration form a countable set. -/
theorem countable_cells : Countable H.cells :=
  Set.countable_univ_iff.mp
    ((locallyFinite_complexCells hH).countable_univ complexCells_nonempty)

theorem iUnion_complexCells : ⋃ K, complexCells H K = univ := by
  refine eq_univ_of_forall fun z => ?_
  have h := hH.iUnion_eq_univ
  rw [eq_univ_iff_forall] at h
  obtain ⟨K, hK, hz⟩ := mem_iUnion₂.mp (h (planeCoord z))
  exact mem_iUnion.mpr ⟨⟨K, hK⟩, hz⟩

theorem volume_complexCells_ne_zero (K : H.cells) : volume (complexCells H K) ≠ 0 := by
  rw [volume_complexCells]
  exact (Measure.measure_pos_of_nonempty_interior _ (hH.interior_nonempty K.1 K.2)).ne'

/-- **Existence of `S_m^w` for a cell configuration** (Gwynne, Miller and Sheffield,
arXiv 1807.07515, (2.1) and Lemma 2.2): for a cell configuration `H` and a point `w`, almost surely
in the uniform dyadic system, for every mass `m ∈ (0, ∞)` the square `squareAt j w` with `m`
between the cell masses of generations `j` and `j + 1` is the capped square of mass `m` around `w`
for the cells of `H`. -/
theorem ae_exists_isCappedSquare_squareAt (w : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ j, cellMass volume (complexCells H) (squareAt q.1 q.2.1 q.2.2 j w) ≤ m ∧
        m < cellMass volume (complexCells H) (squareAt q.1 q.2.1 q.2.2 (j + 1) w) ∧
        IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (cellMass volume (complexCells H)) m w
          (squareAt q.1 q.2.1 q.2.2 j w) := by
  have := countable_cells hH
  exact ae_exists_isCappedSquare_squareAt_cellMass w (locallyFinite_complexCells hH)
    (iUnion_complexCells hH) isCompact_complexCells (volume_complexCells_ne_zero hH)

end LatticeProb.CellConfigCappedSquare
