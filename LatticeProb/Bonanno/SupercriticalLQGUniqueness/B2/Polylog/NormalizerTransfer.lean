/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.NormalizerTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.TightTransfer

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

 


theorem tight_of_comparable_normalizers
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a b : ι → ℝ) (E : ι → Ω → ℝ) (Z : ι → Ω → ℝ≥0∞)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (C : ℝ) (hC : 0 < C)
    (hcomp : ∀ i, C⁻¹ * a i ≤ b i ∧ b i ≤ C * a i)
    (hT : IsTwoSidedTight P
      (fun i ω => ENNReal.ofReal ((b i)⁻¹ * E i ω) * Z i ω)) :
    IsTwoSidedTight P
      (fun i ω => ENNReal.ofReal ((a i)⁻¹ * E i ω) * Z i ω) := by
  let X : ι → Ω → ℝ≥0∞ :=
    fun i ω => ENNReal.ofReal ((b i)⁻¹ * E i ω) * Z i ω
  let Y : ι → Ω → ℝ≥0∞ :=
    fun i ω => ENNReal.ofReal ((a i)⁻¹ * E i ω) * Z i ω
  have hFactor (i : ι) (ω : Ω) :
      Y i ω = ENNReal.ofReal (b i / a i) * X i ω := by
    dsimp [X, Y]
    have hreal : (a i)⁻¹ * E i ω = (b i / a i) * ((b i)⁻¹ * E i ω) := by
      field_simp [ne_of_gt (ha i), ne_of_gt (hb i)]
    rw [hreal, ENNReal.ofReal_mul (div_nonneg (hb i).le (ha i).le), mul_assoc]
  have hkPos (i : ι) : 0 ≤ b i / a i := (div_pos (hb i) (ha i)).le
  have hkUpper (i : ι) : b i / a i ≤ C :=
    (div_le_iff₀ (ha i)).2 (hcomp i).2
  have hkLower (i : ι) : 1 ≤ C * (b i / a i) := by
    have h : a i ≤ C * b i := by
      calc
        a i = C * (C⁻¹ * a i) := by field_simp [hC.ne']
        _ ≤ C * b i := mul_le_mul_of_nonneg_left (hcomp i).1 hC.le
    have hd : 1 ≤ (C * b i) / a i := by
      apply (le_div_iff₀ (ha i)).2
      simpa using h
    simpa [mul_div_assoc] using hd
  have hYmeas : ∀ i, AEMeasurable (Y i) P := by
    intro i
    have hEq : Y i = fun ω => ENNReal.ofReal (b i / a i) * X i ω :=
      funext fun ω => hFactor i ω
    rw [hEq]
    exact (hT.1 i).const_mul _
  have hYX : ∀ i ω, Y i ω ≤ ENNReal.ofReal C * X i ω := by
    intro i ω
    rw [hFactor]
    gcongr
    exact hkUpper i
  have hXY : ∀ i ω, X i ω ≤ ENNReal.ofReal C * Y i ω := by
    intro i ω
    rw [hFactor]
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C * ENNReal.ofReal (b i / a i) := by
      rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hkLower i)
    calc
      X i ω = 1 * X i ω := (one_mul _).symm
      _ ≤ (ENNReal.ofReal C * ENNReal.ofReal (b i / a i)) * X i ω :=
        by gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal (b i / a i) * X i ω) := mul_assoc _ _ _
  exact twoSidedTight_of_bounded_compare P X Y C hC hT hYmeas hYX hXY

end SupercriticalLQGUniqueness.B2.Polylog
