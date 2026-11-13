/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.CellCoupling at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness

/-!
# Unit-mesh cellular embedding and frozen coupling from the mating-of-trees bundle
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, the area-parametrized curve cells form a unit-mesh cellular embedding of
the mated-CRT graph. -/
theorem ae_unitCellularEmbedding
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∃ h : IsLocallyFinite 1 (bm ω),
      ∃ H : CellularEmbedding (graph 1 (bm ω) h) 0,
        H.cell = fun x : ℤ => η ω '' Icc ((x : ℝ) - 1) x := by
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFinite 1 (bm ω) := by
    have hmap := MatedCRTHarmonic.ae_isLocallyFinite_holds γ (P.map bm)
      D.boundaryLawBM 1 one_pos
    exact ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hmap
  have hinterior := ae_curve_cells_have_interior D
  have hnull : ∀ᵐ ω ∂P, ∀ x y : ℤ, x ≠ y →
      volume ((η ω '' Icc ((x : ℝ) - 1) x) ∩
        (η ω '' Icc ((y : ℝ) - 1) y)) = 0 := by
    refine ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
    filter_upwards [D.areaParam, D.spaceFilling] with ω harea hspace
    rcases harea with ⟨⟨φ, _, hη⟩, harea⟩
    rcases hspace with ⟨_, _, _, hvol⟩
    intro hxy
    exact volume_inter_unit_cells_zero hη hvol hxy
  filter_upwards [hlocal, ae_peanosphere D, ae_sideStrict_allMeshes D,
      D.areaParam, D.spaceFilling, hinterior, hnull] with
    ω hlocal hP hside harea hspace hinterior hnull
  rcases harea with ⟨⟨φ, hφ0, hη⟩, _⟩
  rcases hspace with ⟨hsurj, htrans, hηL0, hvol⟩
  have hη0 : η ω 0 = 0 := by rw [hη, hφ0, hηL0]
  have Hinterior : ∀ x : ℤ, (interior (η ω '' Icc ((x : ℝ) - 1) x)).Nonempty :=
    hinterior
  have Hnull : ∀ x y : ℤ, x ≠ y →
      volume ((η ω '' Icc ((x : ℝ) - 1) x) ∩
        (η ω '' Icc ((y : ℝ) - 1) y)) = 0 := hnull
  let H := cellularEmbeddingOfCurve hlocal hP (by simpa [CellFamily.mesh] using hside 0)
    hη0 hη hvol Hinterior Hnull
  exact ⟨hlocal, H, rfl⟩

end MatedCRTHarmonic.MoTInput
