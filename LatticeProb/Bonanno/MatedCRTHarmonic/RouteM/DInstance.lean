/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.DInstance at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Core.CellInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiContinuity
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DDrawing
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.JDrawn

/-!
# Route M: the monotone drawing of the mated-CRT map (Propositions M1 + M2)

The drawing construction and Details (a). For a path `ω` of the pair `(L, R)`,
a Peanosphere bundle `P : Peanosphere ω η`, G0 (`SideStrict ε ω`) and a
cellular embedding `H` of the mated-CRT map `G^ε = MatedCRT.graph ε ω h` whose cells are the space-filling-curve cells
`H_x = η([ε(x − 1), εx])`, this module assembles the Core structure `CellularEmbedding.MonotoneDrawing`
(`Core/CellInterfaces.lean`):

* `Ψ := shearedStripMap P`, with Proposition M1 (`RouteM/PsiContinuity.lean`: continuous, surjective, proper,
  path-connected fibres);
* `pt := drawPt ε`, `arc x y _ := dArc ε ω x y`, with Proposition M2 (`RouteM/DDrawing.lean`).

`matedCRTDrawing` is the drawing, `matedCRT_monotoneDrawing` its existence in TF3's shape
(`Nonempty H.MonotoneDrawing`). The mesh `ε` is positive automatically (`mesh_pos_of_cell_eq`: the cells have
non-empty interior). `matedCRTDrawing_sharedVertex` is TF3's (SV) for this drawing (TFJ's
`exists_mem_support_of_mem_range`).
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace MatedCRTHarmonic.RouteM

variable {ε : ℝ} {ω : MatedCRT.Path2} {η : ℝ → ℂ} {h : MatedCRT.IsLocallyFinite ε ω}

/-- The mesh is positive when the curve cells `η([ε(x − 1), εx])` are the cells of a cellular embedding (cells have
non-empty interior: for `ε = 0` a cell is a point, for `ε < 0` it is empty). -/
theorem mesh_pos_of_cell_eq (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
    (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) : 0 < ε := by
  obtain ⟨z, hz⟩ := H.interior_cell_nonempty 0
  rw [hcell] at hz
  simp only [Int.cast_zero, zero_sub, mul_neg, mul_one, mul_zero] at hz
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, neg_zero, Icc_self, image_singleton, interior_singleton] at hz
    exact hz
  · rw [Icc_eq_empty (by linarith), image_empty, interior_empty] at hz
    exact hz

/-- **The monotone drawing of the mated-CRT map** (TF3 §5, Propositions M1 + M2; TF3 Details (a)'s
`MatedCRT.monotoneDrawing`): the sheared strip map of the Peanosphere bundle together with the explicit drawing
`drawPt`, `dArc` of the mated-CRT graph. -/
def matedCRTDrawing (P : Peanosphere ω η) (hG : SideStrict ε ω) (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
    (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) : H.MonotoneDrawing where
  Ψ := shearedStripMap P
  continuous_Ψ := shearedStripMap_continuous P
  surjective_Ψ := shearedStripMap_surjective P
  tendsto_Ψ := shearedStripMap_tendsto_cocompact P
  isPreconnected_fiber := shearedStripMap_fiber_isPreconnected P
  pt := drawPt ε
  pt_injective := drawPt_injective (mesh_pos_of_cell_eq H hcell)
  arc x y _ := dArc ε ω x y
  arc_injective _ _ hadj := injective_dArc hG (mesh_pos_of_cell_eq H hcell) hadj
  arc_symm _ _ hadj := dArc_swap hadj.ne
  arc_inter _ _ _ _ hadj hadj' hne₁ hne₂ := dArc_inter hG (mesh_pos_of_cell_eq H hcell) hadj hadj' hne₁ hne₂
  pt_mem_arc _ _ _ hadj hv := eq_or_eq_of_drawPt_mem_dArc hG (mesh_pos_of_cell_eq H hcell) hadj hv
  Ψ_pt x := by
    rw [hcell]
    exact shearedStripMap_drawPt_mem P (mesh_pos_of_cell_eq H hcell) x
  Ψ_arc _ _ hadj t := by
    rw [hcell]
    exact shearedStripMap_dArc_mem P hG (mesh_pos_of_cell_eq H hcell) hadj t

section API

variable (P : Peanosphere ω η) (hG : SideStrict ε ω) (H : CellularEmbedding (MatedCRT.graph ε ω h) 0)
  (hcell : H.cell = fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))

@[simp] theorem matedCRTDrawing_Ψ : (matedCRTDrawing P hG H hcell).Ψ = shearedStripMap P := rfl

@[simp] theorem matedCRTDrawing_pt : (matedCRTDrawing P hG H hcell).pt = drawPt ε := rfl

@[simp] theorem matedCRTDrawing_arc (x y : ℤ) (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) :
    (matedCRTDrawing P hG H hcell).arc x y hadj = dArc ε ω x y := rfl

end API

end MatedCRTHarmonic.RouteM
