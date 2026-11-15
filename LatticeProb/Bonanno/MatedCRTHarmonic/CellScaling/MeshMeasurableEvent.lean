/- Copied from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellScaling.Model and MeshMeasurableEvent at commit fdb5cad;
   local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ScalingGridEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableCurveDiameter
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableLawPartition
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableGraph

set_option autoImplicit false
set_option linter.deprecated false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling

def MeshGridEventMeasurable : Prop :=
  ∀ (k : ℕ) (χ β q ρ p : ℝ), MeasurableSet (meshGridGood k χ β q ρ p)

private def meshGridCodeCenter (ε χ : ℝ) (a b : ℤ) : ℂ :=
  ((ε ^ χ : ℝ) : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I)

private def meshGridCodeRadius (ε χ : ℝ) (c : ℤ) : ℝ := ε ^ χ * c

private def meshGridCodeStatic (ε χ β ρ : ℝ) (a b c : ℤ) : Prop :=
  meshGridCodeCenter ε χ a b ∈ ball (0 : ℂ) ρ ∧
  ε ^ β ≤ meshGridCodeRadius ε χ c ∧
  meshGridCodeRadius ε χ c ≤ ρ ∧
  ball (meshGridCodeCenter ε χ a b) (2 * meshGridCodeRadius ε χ c) ⊆
    ball (0 : ℂ) ρ

private def meshGridCodeControl (k : ℕ) (χ β q ρ p : ℝ)
    (d : MatedCRT.Path2 × C(ℝ, ℂ)) : Prop :=
  (∀ x : ℤ,
    (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (meshCells (CellFamily.mesh k) d.2 x) ≤ CellFamily.mesh k ^ q) ∧
  ∀ a b c : ℤ,
    meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c →
    ∀ x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
      (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
        (meshGridCodeRadius (CellFamily.mesh k) χ c)),
      ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
        (meshGridCodeCenter (CellFamily.mesh k) χ a b)
        (meshGridCodeRadius (CellFamily.mesh k) χ c) d

private theorem measurableSet_meshGridCodeControl (k : ℕ) (χ β q ρ p : ℝ) :
    MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodeControl k χ β q ρ p d} := by
  classical
  have hε : 0 ≤ CellFamily.mesh k := by unfold CellFamily.mesh; positivity
  have hdiam := measurable_meshGridDiameterPart k q ρ
  have houter : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      ∀ a b c : ℤ, meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c →
        ∀ x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
          (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c)),
          ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c) d} := by
    rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      ∀ a b c : ℤ, meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c →
        ∀ x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
          (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c)),
          ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c) d} =
      ⋂ a : ℤ, ⋂ b : ℤ, ⋂ c : ℤ, ⋂ x : ℤ,
        {d | meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c →
          x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
            (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
              (meshGridCodeRadius (CellFamily.mesh k) χ c)) →
          ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c) d} by
        ext d
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h a b c x hs hx
          exact h a b c hs x hx
        · intro h a b c hs x hx
          exact h a b c x hs hx]
    apply MeasurableSet.iInter; intro a
    apply MeasurableSet.iInter; intro b
    apply MeasurableSet.iInter; intro c
    apply MeasurableSet.iInter; intro x
    by_cases hs : meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c
    · have hhit : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
          x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
            (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
              (meshGridCodeRadius (CellFamily.mesh k) χ c))} :=
        measurable_meshCell_meets_sphere Prod.snd measurable_snd hε x
          (meshGridCodeCenter (CellFamily.mesh k) χ a b)
          (meshGridCodeRadius (CellFamily.mesh k) χ c)
      have hprob : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
          ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c) d} :=
        measurableSet_le measurable_const
          (measurable_meshGridCodeAnnularProbability (CellFamily.mesh k) hε x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c))
      have hEq : {d : MatedCRT.Path2 × C(ℝ, ℂ) |
          meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c →
          x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
            (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
              (meshGridCodeRadius (CellFamily.mesh k) χ c)) →
          ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c) d} =
          {d | ¬ x ∈ verticesMeeting (meshCells (CellFamily.mesh k) d.2)
            (sphere (meshGridCodeCenter (CellFamily.mesh k) χ a b)
              (meshGridCodeRadius (CellFamily.mesh k) χ c))} ∪
          {d | ENNReal.ofReal p ≤ meshGridCodeAnnularProbability (CellFamily.mesh k) x
            (meshGridCodeCenter (CellFamily.mesh k) χ a b)
            (meshGridCodeRadius (CellFamily.mesh k) χ c) d} := by
        ext d
        simp [hs, imp_iff_not_or]
      rw [hEq]
      exact hhit.compl.union hprob
    · simp [hs]
  exact hdiam.inter houter

private theorem meshGridGood_iff_codeControl (k : ℕ) (χ β q ρ p : ℝ)
    (d : MatedCRT.Path2 × C(ℝ, ℂ)) :
    d ∈ meshGridGood k χ β q ρ p ↔
      MatedCRT.IsLocallyFinite (CellFamily.mesh k) d.1 ∧
        meshGridCodeControl k χ β q ρ p d := by
  classical
  constructor
  · rintro ⟨hlf, hraw⟩
    rcases hraw with ⟨hdiam, hgrid⟩
    refine ⟨hlf, ?_, ?_⟩
    · simpa only [one_mul, mul_one] using hdiam
    · intro a b c hs x hx
      rcases hs with ⟨hz, hlo, hhi, hball⟩
      have h := hgrid a b c (by simpa only [meshGridCodeCenter, one_mul, mul_one] using hz)
        (by simpa only [meshGridCodeRadius, one_mul, mul_one] using hlo)
        (by simpa only [meshGridCodeRadius, one_mul, mul_one] using hhi)
        (by simpa only [meshGridCodeCenter, meshGridCodeRadius, one_mul, mul_one] using hball)
      have hwalk := h x (by simpa only [meshGridCodeCenter, meshGridCodeRadius, one_mul,
        mul_one] using hx)
      rw [meshGridCodeAnnularProbability_eq_walkLaw (CellFamily.mesh k) d.1 hlf d.2 x
        (meshGridCodeCenter (CellFamily.mesh k) χ a b)
        (meshGridCodeRadius (CellFamily.mesh k) χ c)]
      simpa only [meshGridCodeCenter, meshGridCodeRadius, one_mul, mul_one] using hwalk
  · rintro ⟨hlf, hcontrol⟩
    refine ⟨hlf, ?_⟩
    rcases hcontrol with ⟨hdiam, hgrid⟩
    constructor
    · simpa only [one_mul, mul_one] using hdiam
    · intro a b c hz hlo hhi hball x hx
      have hs : meshGridCodeStatic (CellFamily.mesh k) χ β ρ a b c :=
        ⟨by simpa only [meshGridCodeCenter, one_mul, mul_one] using hz,
         by simpa only [meshGridCodeRadius, one_mul, mul_one] using hlo,
         by simpa only [meshGridCodeRadius, one_mul, mul_one] using hhi,
         by simpa only [meshGridCodeCenter, meshGridCodeRadius, one_mul, mul_one] using hball⟩
      have hc := hgrid a b c hs x (by simpa only [meshGridCodeCenter, meshGridCodeRadius,
        one_mul, mul_one] using hx)
      rw [meshGridCodeAnnularProbability_eq_walkLaw (CellFamily.mesh k) d.1 hlf d.2 x
        (meshGridCodeCenter (CellFamily.mesh k) χ a b)
        (meshGridCodeRadius (CellFamily.mesh k) χ c)] at hc
      simpa only [meshGridCodeCenter, meshGridCodeRadius, one_mul, mul_one] using hc

/-- The exact scaled-grid data event is Borel in the Brownian path and curve data. -/
theorem MeshGridEventMeasurable_holds : MeshGridEventMeasurable := by
  intro k χ β q ρ p
  have hlf : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      MatedCRT.IsLocallyFinite (CellFamily.mesh k) d.1} :=
    (measurableSet_matedCRT_isLocallyFinite (CellFamily.mesh k)).preimage measurable_fst
  have hc := measurableSet_meshGridCodeControl k χ β q ρ p
  have hEq : meshGridGood k χ β q ρ p =
      {d | MatedCRT.IsLocallyFinite (CellFamily.mesh k) d.1} ∩
        {d | meshGridCodeControl k χ β q ρ p d} := by
    ext d
    exact meshGridGood_iff_codeControl k χ β q ρ p d
  rw [hEq]
  exact hlf.inter hc

end MatedCRTHarmonic.CellScaling
