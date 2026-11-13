/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Canon.Density at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Local
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableWalk
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.Prop210DensityComparison

/-!
# The nonlocalized density `u^ε` of [18] (2.12)

The countable Brownian dart code supplies a Borel degree on every path. On the
locally finite event it equals the degree of the actual mated-CRT multigraph.
This gives the source density without a graph-witness choice on null samples.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- `diam(H_x)^2 deg(x)/area(H_x)` with the countable Brownian degree. -/
def rawCellCoef (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2) (x : ℤ) : ℝ≥0∞ :=
  GMS4b.segRatio c (ε * ((x : ℝ) - 1)) (ε * x) *
    CellScaling.meshGridRawDegree ε w x

/-- On the locally finite event, the Brownian degree is the multigraph degree. -/
theorem rawCellCoef_eq_graph
    (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w) (x : ℤ) :
    rawCellCoef ε c w x =
      GMS4b.segRatio c (ε * ((x : ℝ) - 1)) (ε * x) *
        (((structureGraph ε w hlf).deg x : ℕ) : ℝ≥0∞) := by
  rw [rawCellCoef, CellScaling.meshGridRawDegree_eq_graph_deg]
  rfl

/-- The raw coefficient is the GMS3 coefficient of the actual cellular
embedding whenever its cells are the SLE interval images. -/
theorem rawCellCoef_eq_uCoef
    (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w)
    (H : CellularEmbedding (structureGraph ε w hlf) 0)
    (x : ℤ) (hcell : H.cell x = cell ε c x) :
    rawCellCoef ε c w x = GMS3.uCoef H x := by
  rw [rawCellCoef_eq_graph ε c w hlf x,
    GMS4F.uCoef_eq_cellRatio_mul_degree]
  simp only [GMS4b.segRatio, GMS3.cellDiam, hcell, cell, GMS4b.cellOf]

/-- The selected cell is one of the segments in `DA^ε(z)`; this is the
area-ratio half of [18] (4.3). -/
theorem selectedCell_ratio_le_DA
    {ε : ℝ} (hε : 0 < ε) (c : C(ℝ, ℂ)) (z : ℂ) :
    GMS4b.segRatio c
      (ε * ((selectedIndex ε c z : ℝ) - 1))
      (ε * (selectedIndex ε c z : ℝ)) ≤
        GMS4b.areaRatio ε c z := by
  have ht := firstHit_mem_selectedCellTime hε c z
  have hlo : ε * (selectedIndex ε c z : ℝ) - ε ≤ GMS4b.hitTime c z := by
    calc
      ε * (selectedIndex ε c z : ℝ) - ε =
          ε * ((selectedIndex ε c z : ℝ) - 1) := by ring
      _ ≤ GMS4b.hitTime c z := ht.1.le
  have h := GMS4b.segRatio_le_locDA (ε := ε) (c := c)
    (t₀ := GMS4b.hitTime c z) (s := ε * (selectedIndex ε c z : ℝ)) hlo ht.2
  simpa only [GMS4b.areaRatio, show
    ε * (selectedIndex ε c z : ℝ) - ε =
      ε * ((selectedIndex ε c z : ℝ) - 1) by ring] using h

/-- The selected coefficient is bounded by twice the canonical localized
density when the graph-degree half of (4.3) holds. -/
theorem selectedCell_rawCoef_le_two_uStar
    {ε : ℝ} (hε : 0 < ε) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w) (z : ℂ)
    (hdegree : ((structureGraph ε w hlf).deg (selectedIndex ε c z) : ℕ∞) ≤
      2 * (GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z)) :
    rawCellCoef ε c w (selectedIndex ε c z) ≤ 2 * GMS4b.uStar ε c z := by
  have hratio := selectedCell_ratio_le_DA hε c z
  have hdegE : (((structureGraph ε w hlf).deg (selectedIndex ε c z) : ℕ) : ℝ≥0∞) ≤
      2 * (((GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z : ℕ∞)) : ℝ≥0∞) := by
    exact_mod_cast hdegree
  rw [rawCellCoef_eq_graph ε c w hlf (selectedIndex ε c z)]
  calc
    _ ≤ GMS4b.areaRatio ε c z *
        (2 * (((GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z : ℕ∞)) : ℝ≥0∞)) :=
      mul_le_mul' hratio hdegE
    _ = 2 * GMS4b.uStar ε c z := by simp only [GMS4b.uStar, GMS4b.locUStar,
      GMS4b.areaRatio, GMS4b.degreeIn, GMS4b.degreeOut]; ac_rfl

/-- The coefficient bound holds at every dyadic mesh and every spatial point
on the same full-measure event as G4FS's (4.7). -/
theorem ae_cone_selectedCell_rawCoef_le_two_uStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (z : ℂ),
      rawCellCoef (CellFamily.mesh k) (η ω) (bm ω)
        (selectedIndex (CellFamily.mesh k) (η ω) z) ≤
          2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z := by
  filter_upwards [GMS4F.ae_matedCRT_degree_le_two_local_degrees D] with ω hω k z
  obtain ⟨hlf, hdeg⟩ := hω k (GMS4b.hitTime (η ω) z)
  have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
  exact selectedCell_rawCoef_le_two_uStar hε (η ω) (bm ω) hlf z hdeg

end MatedCRTHarmonic.Canon
