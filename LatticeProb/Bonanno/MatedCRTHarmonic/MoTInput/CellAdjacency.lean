/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.CellAdjacency at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DLevels
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DInstance

/-!
# The mated-CRT edge relation gives intersecting SLE cells

This is the adjacency axiom of a `CellularEmbedding`, derived from the boundary-minimum edge
criterion, the strict-side Brownian event, and the Peanosphere merge rule.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

private theorem edge_intersects_cells {ε : ℝ} {ω : Path2} {η : ℝ → ℂ}
    (hε : 0 < ε) (P : RouteM.Peanosphere ω η) (hG : RouteM.SideStrict ε ω)
    {x y : ℤ} {b : Bool} (hedge : IsEdge ε ω (x, y, b)) :
    ((η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
      (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))).Nonempty := by
  rcases hedge with ⟨hxy, hkind⟩
  change x < y at hxy
  rcases hkind with hsucc | hside
  · have hy : y = x + 1 := hsucc.1
    subst y
    refine ⟨η (ε * (x : ℝ)), ⟨ε * (x : ℝ), ?_, rfl⟩, ⟨ε * (x : ℝ), ?_, rfl⟩⟩
    · constructor
      · have hlt : (x : ℝ) - 1 ≤ x := by linarith
        exact mul_le_mul_of_nonneg_left hlt hε.le
      · exact le_rfl
    · constructor
      · simp only [Int.cast_add, Int.cast_one]
        have heq : ε * ((x : ℝ) + 1 - 1) = ε * x := by ring
        rw [heq]
      · simp only [Int.cast_add, Int.cast_one]
        exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  · have hnon : y ≠ x + 1 := hside.1
    have hlt : x + 1 < y := by omega
    let X : ℝ → ℝ := fun t => if b then (ω t).2 else (ω t).1
    have hstrict := hG b x y hlt hside.2
    have hwindow : RouteM.dWinLo ε X x y < RouteM.dWinHi ε X x y := by
      simpa [RouteM.dWinLo, RouteM.dWinHi, MatedCRT.SideCond, X] using hstrict
    have hcont : Continuous X := by
      dsimp [X]
      split_ifs
      · exact continuous_snd.comp ω.continuous
      · exact continuous_fst.comp ω.continuous
    obtain ⟨hd, hlevel⟩ := RouteM.lowArcData_dPorts hcont hε hlt hwindow
    have hmerge : RouteM.directRel X
        (RouteM.dPort₁ ε X x y) (RouteM.dPort₂ ε X x y) := hd.rel
    have hdirect :
        RouteM.directRel (RouteM.lCoord ω) (RouteM.dPort₁ ε X x y) (RouteM.dPort₂ ε X x y) ∨
          RouteM.directRel (RouteM.rCoord ω) (RouteM.dPort₁ ε X x y) (RouteM.dPort₂ ε X x y) := by
      cases b
      · exact Or.inl hmerge
      · exact Or.inr hmerge
    have hη : η (RouteM.dPort₁ ε X x y) = η (RouteM.dPort₂ ε X x y) := by
      exact P.merge _ _ hdirect
    refine ⟨η (RouteM.dPort₁ ε X x y), ?_, ?_⟩
    · exact ⟨RouteM.dPort₁ ε X x y, ⟨hd.mem₁.1.le, hd.mem₁.2.le⟩, rfl⟩
    · exact ⟨RouteM.dPort₂ ε X x y, ⟨hd.mem₂.1.le, hd.mem₂.2.le⟩, hη.symm⟩

/-- Under G0, each edge of the mated-CRT graph joins two cells whose SLE interval images meet. -/
theorem cell_intersects_of_matedCRT_adj {ε : ℝ} {ω : Path2} {η : ℝ → ℂ}
    (hε : 0 < ε) (P : RouteM.Peanosphere ω η) (hG : RouteM.SideStrict ε ω)
    {h : IsLocallyFinite ε ω} {x y : ℤ}
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) :
    ((η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
      (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))).Nonempty := by
  have hadj' : x ≠ y ∧
      ((∃ e : Edge ε ω, e.1.1 = x ∧ e.1.2.1 = y) ∨
       ∃ e : Edge ε ω, e.1.1 = y ∧ e.1.2.1 = x) := by
    change x ≠ y ∧
      ((∃ e : Edge ε ω, e.1.1 = x ∧ e.1.2.1 = y) ∨
       ∃ e : Edge ε ω, e.1.1 = y ∧ e.1.2.1 = x) at hadj
    exact hadj
  rcases hadj'.2 with hxy | hyx
  · obtain ⟨e, hsrc, htgt⟩ := hxy
    have hcell := edge_intersects_cells (ε := ε) (ω := ω) (η := η)
      (x := e.1.1) (y := e.1.2.1) (b := e.1.2.2) hε P hG e.2
    obtain ⟨z, hx, hy⟩ := hcell
    have hsrc' : e.1.1 = x := by simpa [MatedCRT.graph] using hsrc
    have htgt' : e.1.2.1 = y := by simpa [MatedCRT.graph] using htgt
    exact ⟨z, by simpa only [hsrc'] using hx, by simpa only [htgt'] using hy⟩
  · obtain ⟨e, hsrc, htgt⟩ := hyx
    have hcell := edge_intersects_cells (ε := ε) (ω := ω) (η := η)
      (x := e.1.1) (y := e.1.2.1) (b := e.1.2.2) hε P hG e.2
    obtain ⟨z, hy, hx⟩ := hcell
    have hsrc' : e.1.1 = y := by simpa [MatedCRT.graph] using hsrc
    have htgt' : e.1.2.1 = x := by simpa [MatedCRT.graph] using htgt
    exact ⟨z, by simpa only [htgt'] using hx, by simpa only [hsrc'] using hy⟩

end MatedCRTHarmonic.MoTInput
