/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop48CanonicalCompletion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48PrimedIntegral
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalMoments
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48Rate
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ThickLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.ZeroConeL46
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OCondMean

/-!
# Canonical Proposition 4.8 completion boundary

H3 is the a.s. Borel factor for the geometric part of the all-visit point
variable of [18] (4.22), lines 2183–2208 and 2292–2298. The circle-average
condition is evaluated separately at its larger radius. the bundle construction already proves
The primed Lemma 4.3 event reconstruction consumed by Proposition 4.5. The source-corrected
completion theorem and the sole remaining good-event second-moment input
are in `Prop48CanonicalCorrected`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT LQGMetric LQGMetric.Blueprint

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- One schema of thickened-field GMC readers, for the local balls used at
all centres and scales. -/
def ThickGMCReaders
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Type :=
  ∀ (V : TopologicalSpace.Opens ℂ) (δ : ℝ), 0 < δ →
    GMS4.Prop48ThickLocalGMCFromFieldInput P γ
      (fun ω => coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) V δ

/-- H3: the geometric all-visit point factor is a.s. Borel from the GMC
reader and the two thickened local fields with IG phase. The conditioning
circle averages are separate inputs and may lie outside this local disk. -/
structure Prop48PrimedBorelLocalFactorInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ : ℝ)
    (H2 : ThickGMCReaders D) : Type where
  factor_exists : ∀ ε (hε : ε ∈ Ioo (0 : ℝ) 1) z,
    let V := ballO z (4 * ε ^ q)
    let W := GMS4c.thickOpen V (ε ^ q)
    let reader := H2 V (ε ^ q) (Real.rpow_pos_of_pos hε.1 q)
    ∃ factor : ((Measure ℂ × DistOn W) × (DistOn W × ℝ)) → ℝ,
      Measurable factor ∧ (fun ω => maskedUStarPrime D hγ ε q ζ z ω) =ᵐ[P]
        fun ω => if max |fieldCircleAverage D hγ
          (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω|
          |igCircleAverage hIG₀ U
            (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z ω| ≤
            2 * q * Real.log ε⁻¹ then factor
      ((reader.reconstruct (restrictTo W
          (coneField (X₀ ω)
            (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))),
        restrictTo W (coneField (X₀ ω)
          (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))),
        (restrictTo W (hIG₀ ω), U ω)) else 0

end MatedCRTHarmonic.GMS4.Canonical

