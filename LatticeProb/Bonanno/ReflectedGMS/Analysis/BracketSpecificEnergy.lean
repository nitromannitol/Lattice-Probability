/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Analysis.BracketSpecificEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea

/-!
The ordinary-edge bracket trace is twice the actual ENNReal specific-energy
density.  The rooted version uses the existing global boundary mask through
`rootAt`; no integrability or finite-specific-energy assumption is needed.
-/

-- Merged from `ReflectedGMS/Analysis/BracketNormalization.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_BracketNormalization

/-!
The trace of the ordinary-edge bracket has the manuscript's ordered-edge
energy normalization.  Local finiteness is used explicitly, so no real
`tsum` below is interpreted as a nonsummable sum.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace ReflectedGMS.RootDensities

variable {V : Type*} [Countable V]

private theorem summable_conductance_mul_coordinateSquare
    (F : IndexedCells V) (hF : Geometry F) (Phi : V → Plane) (v : V) (i : Fin 2) :
    Summable (fun w : V ↦
      F.graph.c v w * (Phi w i - Phi v i) * (Phi w i - Phi v i)) := by
  apply summable_of_hasFiniteSupport
  refine (hF.2.2.2.2.2.2.1 v).subset ?_
  intro w hw
  simp only [Function.mem_support] at hw
  rw [SimpleGraph.mem_neighborSet, ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
  have hc : F.graph.c v w ≠ 0 := by
    intro hc
    apply hw
    simp [hc]
  exact lt_of_le_of_ne (F.graph.c_nonneg v w) hc.symm

/-- Deterministic normalization behind `trace Gamma = 2 * specific energy`.
The right side is an actual finite-neighbor sum, by `Geometry`'s local
finiteness; hence the real-valued `tsum` is legitimate. -/
theorem trace_bracketDensity_eq_invArea_mul_tsum_normSq
    (F : IndexedCells V) (hF : Geometry F) (Phi : V → Plane) (v : V) :
    Matrix.trace (StatementIngredients.bracketDensity F Phi v) =
      (StatementIngredients.cellArea F v)⁻¹ *
        ∑' w : V, F.graph.c v w * ‖Phi w - Phi v‖ ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, StatementIngredients.bracketDensity]
  rw [← Finset.mul_sum]
  rw [← Summable.tsum_finsetSum (fun i _ ↦
    summable_conductance_mul_coordinateSquare F hF Phi v i)]
  congr 1
  apply tsum_congr
  intro w
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq (Phi w - Phi v)).symm

end ReflectedGMS.RootDensities

end Merged_BracketNormalization

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace ReflectedGMS.RootDensities

variable {V : Type*} [Countable V]

private theorem summable_conductance_mul_normSq
    (F : IndexedCells V) (hF : Geometry F) (Phi : V → Plane) (v : V) :
    Summable (fun w : V ↦ F.graph.c v w * ‖Phi w - Phi v‖ ^ 2) := by
  apply summable_of_hasFiniteSupport
  refine (hF.2.2.2.2.2.2.1 v).subset ?_
  intro w hw
  simp only [Function.mem_support] at hw
  rw [SimpleGraph.mem_neighborSet, ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
  have hc : F.graph.c v w ≠ 0 := by
    intro hc
    apply hw
    simp [hc]
  exact lt_of_le_of_ne (F.graph.c_nonneg v w) hc.symm

/-- Vertexwise ENNReal normalization of the ordinary-edge bracket trace. -/
theorem ofReal_trace_bracketDensity_eq_two_mul_specificEnergyDensity
    (F : IndexedCells V) (hF : Geometry F) (Phi : V → Plane) (v : V) :
    ENNReal.ofReal (Matrix.trace (StatementIngredients.bracketDensity F Phi v)) =
      2 * specificEnergyDensity F Phi v := by
  rw [trace_bracketDensity_eq_invArea_mul_tsum_normSq F hF Phi v]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr
    (StatementIngredients.cellArea_pos F hF v).le)]
  rw [ENNReal.ofReal_inv_of_pos (StatementIngredients.cellArea_pos F hF v)]
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun w ↦ mul_nonneg (F.graph.c_nonneg v w) (sq_nonneg ‖Phi w - Phi v‖))
    (summable_conductance_mul_normSq F hF Phi v)]
  simp_rw [ENNReal.ofReal_mul (F.graph.c_nonneg v _)]
  unfold specificEnergyDensity
  rw [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  calc
    _ = 1 * ((ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ *
        ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
          ENNReal.ofReal (‖Phi w - Phi v‖ ^ 2)) := by rw [one_mul]
    _ = (2 * (2 : ℝ≥0∞)⁻¹) *
        ((ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ *
          ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
            ENNReal.ofReal (‖Phi w - Phi v‖ ^ 2)) := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ = _ := by ac_rfl

/-- Rooted normalization, including the actual global-boundary mask. -/
theorem ofReal_trace_rootedGamma_eq_two_mul_rootedSpecificEnergyDensity
    (F : IndexedCells V) (hF : Geometry F) (Phi : V → Plane) (z : Plane) :
    ENNReal.ofReal (Matrix.trace (rootedGamma F Phi z)) =
      2 * rootedSpecificEnergyDensity F Phi z := by
  generalize hroot : rootAt F z = root
  cases root with
  | none => simp [rootedGamma, rootedSpecificEnergyDensity, hroot]
  | some v =>
      simpa [rootedGamma, rootedSpecificEnergyDensity, hroot] using
        ofReal_trace_bracketDensity_eq_two_mul_specificEnergyDensity F hF Phi v

end ReflectedGMS.RootDensities
