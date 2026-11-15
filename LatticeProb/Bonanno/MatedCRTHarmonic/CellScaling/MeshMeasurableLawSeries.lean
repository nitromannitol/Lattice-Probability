/- Copied from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableLaw at commit fdb5cad;
   selected declarations with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableLawCylinders
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurablePrefix

set_option autoImplicit false
set_option linter.deprecated false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling

noncomputable def meshGridCodePrefixTerm (ε : ℝ) (x : ℤ) (z : ℂ) (r : ℝ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (d : MatedCRT.Path2 × C(ℝ, ℂ)) : ℝ≥0∞ := by
  classical
  exact if meshGridCodePrefixValid ε d.1 n s ∧ meshGridCodePrefixGeometry ε z r n s d then
    meshGridCodePrefixWeight ε x s n d.1 else 0

theorem measurable_meshGridCodePrefixTerm (ε : ℝ) (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (r : ℝ) (n : ℕ) (s : ℕ → MeshGridStateCode) :
    Measurable (meshGridCodePrefixTerm ε x z r n s) := by
  classical
  have hv : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodePrefixValid ε d.1 n s} :=
    (measurableSet_meshGridCodePrefixValid ε n s).preimage measurable_fst
  have hg := measurableSet_meshGridCodePrefixGeometry ε hε z r n s
  have hw : Measurable (fun d : MatedCRT.Path2 × C(ℝ, ℂ) =>
      meshGridCodePrefixWeight ε x s n d.1) :=
    (measurable_meshGridCodePrefixWeight ε x s n).comp measurable_fst
  unfold meshGridCodePrefixTerm
  exact Measurable.ite (hv.inter hg) hw measurable_const

abbrev MeshGridPrefixIndex := Σ n : ℕ, Fin (n + 1) → MeshGridStateCode

def meshGridPrefixIndexSeq (j : MeshGridPrefixIndex) (i : ℕ) : MeshGridStateCode :=
  j.2 ⟨min i j.1, by omega⟩

theorem meshGridPrefixIndexSeq_get (j : MeshGridPrefixIndex) (i : ℕ) (hi : i ≤ j.1) :
    meshGridPrefixIndexSeq j i = j.2 ⟨i, by omega⟩ := by
  simp [meshGridPrefixIndexSeq, Nat.min_eq_left hi]

noncomputable def meshGridCodeAnnularProbability (ε : ℝ) (x : ℤ)
    (z : ℂ) (r : ℝ) (d : MatedCRT.Path2 × C(ℝ, ℂ)) : ℝ≥0∞ :=
  ∑' j : MeshGridPrefixIndex,
    meshGridCodePrefixTerm ε x z r j.1 (meshGridPrefixIndexSeq j) d

theorem measurable_meshGridCodeAnnularProbability (ε : ℝ) (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (r : ℝ) :
    Measurable (meshGridCodeAnnularProbability ε x z r) := by
  unfold meshGridCodeAnnularProbability
  apply Measurable.ennreal_tsum
  intro j
  exact measurable_meshGridCodePrefixTerm ε hε x z r j.1 (meshGridPrefixIndexSeq j)

end MatedCRTHarmonic.CellScaling
