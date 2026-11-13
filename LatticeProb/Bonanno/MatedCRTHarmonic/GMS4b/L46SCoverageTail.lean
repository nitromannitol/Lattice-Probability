/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SCoverageTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCoverage
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STailFinite

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

/-- The bundle's polynomial coverage estimate becomes arbitrarily strong
after taking a sufficiently large polynomial time window. -/
theorem l46s_coverage_superpoly
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (s : ℝ) :
    ∃ p : ℝ, 0 ≤ p ∧ ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-(ε ^ (-p))) (ε ^ (-p))} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  obtain ⟨c, hc, C, hC⟩ := D.coverage
  let p : ℝ := (max s 0 + 1) / c
  have hp : 0 < p := by dsimp [p]; positivity
  refine ⟨p, hp.le, max C 0, ?_⟩
  intro ε hε
  have hT : 1 < ε ^ (-p) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε.1 hε.2
    (by linarith : -p < 0)
  have hpow : (ε ^ (-p)) ^ (-c) = ε ^ (max s 0 + 1) := by
    rw [← Real.rpow_mul hε.1.le]
    congr 1
    dsimp [p]
    field_simp
  have hexp : ε ^ (max s 0 + 1) ≤ ε ^ s :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (by linarith [le_max_left s 0])
  calc
    P {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-(ε ^ (-p))) (ε ^ (-p))} ≤
        ENNReal.ofReal (C * (ε ^ (-p)) ^ (-c)) := hC _ hT
    _ = ENNReal.ofReal (C * ε ^ (max s 0 + 1)) := by rw [hpow]
    _ ≤ ENNReal.ofReal (max C 0 * ε ^ s) := by
      apply ENNReal.ofReal_le_ofReal
      calc C * ε ^ (max s 0 + 1) ≤ max C 0 * ε ^ (max s 0 + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.1.le _)
        _ ≤ max C 0 * ε ^ s :=
          mul_le_mul_of_nonneg_left hexp (le_max_right _ _)

end MatedCRTHarmonic.GMS4b
