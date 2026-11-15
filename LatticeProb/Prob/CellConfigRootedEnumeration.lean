import LatticeProb.Prob.CellConfigCellDiameterSublinear

/-! # Rooted conductance sums over cells -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigCappedSquare

/-- The rooted conductance sum can be indexed by any bijective enumeration of
all cells, including every cell containing the origin. -/
theorem originRowSum_eq_tsum_cells {ι : Type*} (H : GMSSpace)
    (e : ι ≃ H.1.cells) :
    originRowSum id H = ∑' i : ι,
      originAreaRatio (e i : Cell) * ENNReal.ofReal (H.1.pi (e i)) := by
  classical
  have hsupp : Function.support (fun n : ℕ =>
      (H.1.slot n).elim 0 (fun K => originAreaRatio K * slotRowMass id H n)) ⊆
      {n : ℕ | (H.1.slot n).isSome} := by
    intro n hn
    cases h : H.1.slot n with
    | none =>
      exact absurd (show (fun n : ℕ => (H.1.slot n).elim 0
        (fun K => originAreaRatio K * slotRowMass id H n)) n = 0 by simp [h]) hn
    | some K => simp [h]
  have hterm : ∀ v : Code.Vertex H.1.code,
      (H.1.slot v.val).elim 0 (fun K => originAreaRatio K * slotRowMass id H v.val) =
        originAreaRatio (CellConfig.cellEquiv H.2 v : Cell) *
          ENNReal.ofReal (H.1.pi (CellConfig.cellEquiv H.2 v)) := by
    intro v
    have heq : CellConfig.label H.2 (CellConfig.cellEquiv H.2 v) = v.val := by
      simpa only [CellConfig.cellEquiv_symm_val] using
        congrArg Subtype.val ((CellConfig.cellEquiv H.2).symm_apply_apply v)
    rw [CellConfig.slot_val v]
    change originAreaRatio (CellConfig.cellEquiv H.2 v : Cell) * slotRowMass id H v.val =
      originAreaRatio (CellConfig.cellEquiv H.2 v : Cell) *
        ENNReal.ofReal (H.1.pi (CellConfig.cellEquiv H.2 v))
    rw [ofReal_pi_eq_slotRowMass H (CellConfig.cellEquiv H.2 v), heq]
  calc
    originRowSum id H = ∑' n : ℕ, (H.1.slot n).elim 0
        (fun K => originAreaRatio K * slotRowMass id H n) := rfl
    _ = ∑' v : Code.Vertex H.1.code, (H.1.slot v.val).elim 0
        (fun K => originAreaRatio K * slotRowMass id H v.val) :=
          (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' v : Code.Vertex H.1.code,
        originAreaRatio (CellConfig.cellEquiv H.2 v : Cell) *
          ENNReal.ofReal (H.1.pi (CellConfig.cellEquiv H.2 v)) := tsum_congr hterm
    _ = ∑' K : H.1.cells, originAreaRatio (K : Cell) * ENNReal.ofReal (H.1.pi K) :=
      (CellConfig.cellEquiv H.2).tsum_eq
        (fun K : H.1.cells => originAreaRatio (K : Cell) * ENNReal.ofReal (H.1.pi K))
    _ = ∑' i : ι, originAreaRatio (e i : Cell) * ENNReal.ofReal (H.1.pi (e i)) :=
      (e.tsum_eq (fun K : H.1.cells =>
        originAreaRatio (K : Cell) * ENNReal.ofReal (H.1.pi K))).symm

end LatticeProb.CellConfigCappedSquare
