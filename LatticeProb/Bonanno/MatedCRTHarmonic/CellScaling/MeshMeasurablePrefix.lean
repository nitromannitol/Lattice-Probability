/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurablePrefix at commit fdb5cad;
   selected declarations with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableDisconnect
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableCurveGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableWalkWeights

set_option autoImplicit false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.CellScaling

def meshGridCodePrefixGeometry (ε : ℝ) (z : ℂ) (r : ℝ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (d : MatedCRT.Path2 × C(ℝ, ℂ)) : Prop :=
  (∀ i < n, (meshCells ε d.2 (meshGridStateVertexCode (s i)) ∩
    annulus z (r / 2) (3 * r / 2)).Nonempty) ∧
  ¬(meshCells ε d.2 (meshGridStateVertexCode (s n)) ∩
    annulus z (r / 2) (3 * r / 2)).Nonempty ∧
  meshGridCodeDisconnects ε d.1
    {y | ∃ i < n, meshGridStateVertexCode (s i) = y}
    (verticesMeeting (meshCells ε d.2) (sphere z (3 * r / 4)))
    (verticesMeeting (meshCells ε d.2) (sphere z (5 * r / 4))) ∧
  (∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
    annulus z (r / 3) (5 * r / 3))

/-- For every fixed state-code prefix, all first-exit geometric and graph-separation
conditions are Borel in the path/curve data. -/
theorem measurableSet_meshGridCodePrefixGeometry (ε : ℝ) (hε : 0 ≤ ε)
    (z : ℂ) (r : ℝ) (n : ℕ) (s : ℕ → MeshGridStateCode) :
    MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodePrefixGeometry ε z r n s d} := by
  classical
  let hit (i : ℕ) : Set (MatedCRT.Path2 × C(ℝ, ℂ)) :=
    {d | (meshCells ε d.2 (meshGridStateVertexCode (s i)) ∩
      annulus z (r / 2) (3 * r / 2)).Nonempty}
  have hhit (i : ℕ) : MeasurableSet (hit i) :=
    measurable_meshCell_meets_annulus Prod.snd measurable_snd hε
      (meshGridStateVertexCode (s i)) z (r / 2) (3 * r / 2)
  have hpre : MeasurableSet {d | ∀ i < n, d ∈ hit i} := by
    rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) | ∀ i < n, d ∈ hit i} =
      ⋂ i : ℕ, {d | i < n → d ∈ hit i} by ext d; simp]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < n
    · simpa [hi] using hhit i
    · simp [hi]
  have hdisc : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodeDisconnects ε d.1
        {y | ∃ i < n, meshGridStateVertexCode (s i) = y}
        (verticesMeeting (meshCells ε d.2) (sphere z (3 * r / 4)))
        (verticesMeeting (meshCells ε d.2) (sphere z (5 * r / 4)))} := by
    apply measurableSet_meshGridCodeDisconnects ε Prod.fst measurable_fst
    · intro a
      exact measurable_meshCell_meets_sphere Prod.snd measurable_snd hε a z (3 * r / 4)
    · intro b
      exact measurable_meshCell_meets_sphere Prod.snd measurable_snd hε b z (5 * r / 4)
  have hcontain : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      ∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
        annulus z (r / 3) (5 * r / 3)} := by
    rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      ∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
        annulus z (r / 3) (5 * r / 3)} =
      ⋂ i : ℕ, {d | i ≤ n → meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
        annulus z (r / 3) (5 * r / 3)} by ext d; simp]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ≤ n
    · simpa [hi] using measurable_meshCell_subset_annulus Prod.snd measurable_snd hε
        (meshGridStateVertexCode (s i)) z (r / 3) (5 * r / 3)
    · simp [hi]
  change MeasurableSet ({d | (∀ i < n, d ∈ hit i) ∧ d ∉ hit n ∧
    meshGridCodeDisconnects ε d.1
      {y | ∃ i < n, meshGridStateVertexCode (s i) = y}
      (verticesMeeting (meshCells ε d.2) (sphere z (3 * r / 4)))
      (verticesMeeting (meshCells ε d.2) (sphere z (5 * r / 4))) ∧
    (∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
      annulus z (r / 3) (5 * r / 3))})
  have hnot : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) | d ∉ hit n} := by
    change MeasurableSet (hit n)ᶜ
    exact (hhit n).compl
  simpa only [Set.setOf_and] using hpre.inter (hnot.inter (hdisc.inter hcontain))

end MatedCRTHarmonic.CellScaling
