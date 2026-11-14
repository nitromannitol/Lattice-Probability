/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistProbTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.TightTransfer

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem two_sided_tail_of_probabilistic_compare
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ≥0∞) (C M ε : ℝ)
    (hC : 0 < C) (hM : 0 < M)
    (hXup : P {ω | ENNReal.ofReal M < X ω} ≤ ENNReal.ofReal ε)
    (hXlow : P {ω | X ω < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal ε)
    (hcmp : P {ω | ¬
      (Y ω ≤ ENNReal.ofReal C * X ω ∧
       X ω ≤ ENNReal.ofReal C * Y ω)} ≤ ENNReal.ofReal ε) :
    P {ω | ENNReal.ofReal (C * M) < Y ω} ≤
        ENNReal.ofReal ε + ENNReal.ofReal ε ∧
      P {ω | Y ω < ENNReal.ofReal (C * M)⁻¹} ≤
        ENNReal.ofReal ε + ENNReal.ofReal ε := by
  have hCM : ENNReal.ofReal (C * M) =
      ENNReal.ofReal C * ENNReal.ofReal M :=
    ENNReal.ofReal_mul hC.le
  have hInv : ENNReal.ofReal C * ENNReal.ofReal (C * M)⁻¹ =
      ENNReal.ofReal M⁻¹ := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    field_simp
  have hCne0 : ENNReal.ofReal C ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  have hCtop : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hUpperSub :
      {ω | ENNReal.ofReal (C * M) < Y ω} ⊆
        {ω | ENNReal.ofReal M < X ω} ∪
        {ω | ¬
          (Y ω ≤ ENNReal.ofReal C * X ω ∧
           X ω ≤ ENNReal.ofReal C * Y ω)} := by
    intro ω hω
    by_cases hX : ENNReal.ofReal M < X ω
    · exact Or.inl hX
    · right
      intro hgood
      have hY : Y ω ≤ ENNReal.ofReal (C * M) := by
        calc Y ω ≤ ENNReal.ofReal C * X ω := hgood.1
          _ ≤ ENNReal.ofReal C * ENNReal.ofReal M := by
              gcongr
              exact le_of_not_gt hX
          _ = ENNReal.ofReal (C * M) := hCM.symm
      exact (not_lt_of_ge hY) hω
  have hLowerSub :
      {ω | Y ω < ENNReal.ofReal (C * M)⁻¹} ⊆
        {ω | X ω < ENNReal.ofReal M⁻¹} ∪
        {ω | ¬
          (Y ω ≤ ENNReal.ofReal C * X ω ∧
           X ω ≤ ENNReal.ofReal C * Y ω)} := by
    intro ω hω
    by_cases hX : X ω < ENNReal.ofReal M⁻¹
    · exact Or.inl hX
    · right
      intro hgood
      have hX' : X ω < ENNReal.ofReal M⁻¹ := by
        calc X ω ≤ ENNReal.ofReal C * Y ω := hgood.2
          _ < ENNReal.ofReal C * ENNReal.ofReal (C * M)⁻¹ := by
              simpa only [mul_comm] using
                ENNReal.mul_lt_mul_left hCne0 hCtop hω
          _ = ENNReal.ofReal M⁻¹ := hInv
      exact hX hX'
  constructor
  · exact (measure_mono hUpperSub).trans
      ((measure_union_le _ _).trans (add_le_add hXup hcmp))
  · exact (measure_mono hLowerSub).trans
      ((measure_union_le _ _).trans (add_le_add hXlow hcmp))

end SupercriticalLQGUniqueness.B2.DG20Pt
