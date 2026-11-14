/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.TightTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 








set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

 



theorem twoSidedTight_of_bounded_compare
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ι → Ω → ℝ≥0∞) (C : ℝ) (hC : 0 < C)
    (hX : IsTwoSidedTight P X)
    (hYmeas : ∀ i : ι, AEMeasurable (Y i) P)
    (hYX : ∀ i ω, Y i ω ≤ ENNReal.ofReal C * X i ω)
    (hXY : ∀ i ω, X i ω ≤ ENNReal.ofReal C * Y i ω) :
    IsTwoSidedTight P Y := by
  refine ⟨hYmeas, ?_⟩
  intro ε hε
  obtain ⟨M, hM, hXM⟩ := hX.2 ε hε
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro i
  have hCne0 : ENNReal.ofReal C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  have hCtop : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCM : ENNReal.ofReal (C * M) = ENNReal.ofReal C * ENNReal.ofReal M :=
    ENNReal.ofReal_mul hC.le
  have hInv : ENNReal.ofReal (C * M)⁻¹ * ENNReal.ofReal C =
      ENNReal.ofReal M⁻¹ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos hC hM).le)]
    congr 1
    field_simp
  have hUpperSet : {ω | ENNReal.ofReal (C * M) < Y i ω} ⊆
      {ω | ENNReal.ofReal M < X i ω} := by
    intro ω hω
    by_contra hn
    have hXω : X i ω ≤ ENNReal.ofReal M := le_of_not_gt hn
    have hYω : Y i ω ≤ ENNReal.ofReal (C * M) := by
      calc
        Y i ω ≤ ENNReal.ofReal C * X i ω := hYX i ω
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal M := by gcongr
        _ = ENNReal.ofReal (C * M) := hCM.symm
    exact (not_lt_of_ge hYω) hω
  have hLowerSet : {ω | Y i ω < ENNReal.ofReal (C * M)⁻¹} ⊆
      {ω | X i ω < ENNReal.ofReal M⁻¹} := by
    intro ω hω
    calc
      X i ω ≤ ENNReal.ofReal C * Y i ω := hXY i ω
      _ < ENNReal.ofReal C * ENNReal.ofReal (C * M)⁻¹ := by
        simpa only [mul_comm] using ENNReal.mul_lt_mul_left hCne0 hCtop hω
      _ = ENNReal.ofReal M⁻¹ := by rw [mul_comm]; exact hInv
  exact ⟨(measure_mono hUpperSet).trans (hXM i).1,
    (measure_mono hLowerSet).trans (hXM i).2⟩

end SupercriticalLQGUniqueness.B2.Polylog
