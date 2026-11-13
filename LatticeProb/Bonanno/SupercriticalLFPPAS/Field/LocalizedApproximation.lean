/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLFPPAS.Field.LocalizedApproximation at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF

/-!
# Localized heat fields converge uniformly on compact sets

The pinned polylogarithmic-localization library proves the compact-uniform approximation for
cutoff radius `ε (log ε⁻¹)^q`.  The manuscript's cutoff is exactly its `q = 1` case, including
the normalized convolution by the cutoff mass.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistC heatMollify)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.B2.Polylog (plMollify)

namespace SupercriticalLFPPAS.Field

/-- The exponent that makes the PL cutoff radius equal to `δ L`. -/
def uniformLocalizationExponent (δ L : ℝ) : ℝ :=
  Real.log L / Real.log (Real.log δ⁻¹)

/-- The normalized localized field with cutoff radius `δ L`, encoded using the PL family. -/
def uniformLocalizedHeatField (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (h : DistC) (z : ℂ) : ℝ :=
  plMollify (uniformLocalizationExponent δ L) δ hδ h z

/-- The variable-exponent PL field above has cutoff radius exactly `δ L`. -/
theorem plRad_uniform_eq (δ L : ℝ)
    (ht : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) :
    SupercriticalLQGUniqueness.B2.Polylog.plRad (uniformLocalizationExponent δ L) δ = δ * L := by
  have htpos : 0 < Real.log δ⁻¹ := lt_trans (by norm_num) ht
  have hLpos : 0 < L := lt_of_lt_of_le htpos hL
  have hlogt : Real.log (Real.log δ⁻¹) ≠ 0 := (Real.log_pos ht).ne'
  have hlogt' : Real.log (Real.log (1 / δ)) ≠ 0 := by simpa [one_div] using hlogt
  rw [SupercriticalLQGUniqueness.B2.Polylog.plRad,
    uniformLocalizationExponent, Real.rpow_def_of_pos htpos]
  congr 1
  rw [show Real.log (Real.log δ⁻¹) *
        (Real.log L / Real.log (Real.log δ⁻¹)) = Real.log L by
          field_simp [hlogt']]
  exact Real.exp_log hLpos

end SupercriticalLFPPAS.Field
