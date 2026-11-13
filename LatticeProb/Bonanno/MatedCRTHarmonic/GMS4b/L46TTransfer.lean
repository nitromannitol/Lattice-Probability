/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46TTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TShift
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TPhase
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Transfer

/-!
# Hölder transfer of localized bad events

The gamma-cone estimate is transferred only through events reconstructed
from the restricted field pair and the common imaginary-geometry phase.
The source and target event identities are
The missing measurable conclusion of [18, Lemma 4.3].
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

/-- The localized inner-degree failure on a spatial test region. -/
def l46tInnerBad {Ω : Type*} (c : Ω → ℝ → ℂ) (S : Set ℂ)
    (ε : ℝ) (k : ℕ) (ζ : ℝ) : Set Ω :=
  {ω | ∃ z ∈ S,
    ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
      ((degreeIn ε (c ω) z : ℕ∞) : ℝ≥0∞)}

/-- Failure of the localization event for the degree ball. -/
def l46tEscapeBad {Ω : Type*} (c : Ω → ℝ → ℂ) (S U : Set ℂ)
    (ε : ℝ) : Set Ω :=
  {ω | ∃ t : ℝ, c ω t ∈ S ∧ ¬ locBall ε (c ω) t ⊆ U}
/-- The still-open measurable part of [18, Lemma 4.3], in the exact form
needed by the two applications of `local_configuration_badEvent_le_holder`.
It reconstructs the escape event and the inner-degree failure on its
complement, under both specified field laws. -/
structure L46TLocalReconstruction {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V U : TopologicalSpace.Opens ℂ)
    (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → LQGMetric.DistC) (uγ : Ωγ → ℝ)
    (h₀ hIG₀ : Ω₀ → LQGMetric.DistC) (u₀ : Ω₀ → ℝ)
    (cγ : Ωγ → ℝ → ℂ) (c₀ : Ω₀ → ℝ → ℂ)
    (S : Set ℂ) (ε : ℝ) (k : ℕ) (ζ : ℝ) : Type where
  reconstruct : L46TLocalFieldPhase V → GMS4c.LocalConfiguration U
  reconstruct_measurable : Measurable reconstruct
  escapeBad : Set (GMS4c.LocalConfiguration U)
  escapeBad_measurable : MeasurableSet escapeBad
  innerBad : Set (GMS4c.LocalConfiguration U)
  innerBad_measurable : MeasurableSet innerBad
  gamma_escape : l46tEscapeBad cγ S U ε =ᵐ[Pγ]
    {ω | reconstruct (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ escapeBad}
  target_escape : l46tEscapeBad c₀ S U ε =ᵐ[P₀]
    {ω | reconstruct (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ escapeBad}
  gamma_inner : (l46tInnerBad cγ S ε k ζ ∩ (l46tEscapeBad cγ S U ε)ᶜ) =ᵐ[Pγ]
    {ω | reconstruct (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ innerBad}
  target_inner : (l46tInnerBad c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) =ᵐ[P₀]
    {ω | reconstruct (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ innerBad}


/-- A finite Hölder factor preserves a polynomial probability bound, dividing
The source exponent by its conjugate `q`. -/
theorem l46t_holder_power_bound (K : ℝ≥0∞) (hK : K < ⊤)
    (q C ε s : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    K * (ENNReal.ofReal (C * ε ^ (q * s))) ^ (1 / q) ≤
      ENNReal.ofReal (K.toReal * (max C 0) ^ (1 / q) * ε ^ s) := by
  have hεpow : 0 ≤ ε ^ (q * s) := (Real.rpow_pos_of_pos hε _).le
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hmono : C * ε ^ (q * s) ≤ max C 0 * ε ^ (q * s) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hεpow
  have hreal : (max C 0 * ε ^ (q * s)) ^ (1 / q) =
      (max C 0) ^ (1 / q) * ε ^ s := by
    rw [Real.mul_rpow hC hεpow, ← Real.rpow_mul hε.le]
    congr 1
    field_simp
  calc
    K * (ENNReal.ofReal (C * ε ^ (q * s))) ^ (1 / q) ≤
        K * (ENNReal.ofReal (max C 0 * ε ^ (q * s))) ^ (1 / q) := by
          gcongr
    _ = ENNReal.ofReal (K.toReal * (max C 0) ^ (1 / q) * ε ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC hεpow) (one_div_nonneg.mpr hq.le), hreal]
      conv_lhs => rw [← ENNReal.ofReal_toReal hK.ne]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      congr 1
      ring

/-- Pull back a field under the translation sending `z₀` to the cone root. -/
def l46tTranslatedField {Ω : Type*} (z₀ : ℂ)
    (h : Ω → LQGMetric.DistC) : Ω → LQGMetric.DistC :=
  fun ω => LQGMetric.affineComp 1 (-z₀) (h ω)

/-- The actual source comparison disk lies a positive distance from the
translated gamma-cone singularity. -/
def l46tObservation (ρ : ℝ) (w : ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨ball w ((1 - ρ) / 4), isOpen_ball⟩

/-- The disk in which Lemma 4.3 reconstructs localized degree data. -/
def l46tLocalRegion (ρ : ℝ) (w : ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨ball w ((1 - ρ) / 8), isOpen_ball⟩

end MatedCRTHarmonic.GMS4b
