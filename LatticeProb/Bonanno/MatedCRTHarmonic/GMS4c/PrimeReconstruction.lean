/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.PrimeReconstruction at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimeAreaInput
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimeReconstructionAdapter
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OAffinePos
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionCoverage
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ZeroCone
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalCircleProcess
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.Main

/-! The exact all-visit measurable reconstruction input for the bundle construction. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
  MatedCRTHarmonic.GMS4cP

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field}
  {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Measurable Lemma 4.3 in the local configuration form: the Borel GMC
reader and the S7 excursion reader recover the actual configuration under
both cone laws, almost surely. -/
theorem prime_zeroConeConfigInput_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    L43PZeroConeConfigInput D hγ ρ w :=
  l43pZeroConeConfigInput_of_area D hγ hρ.2 w
    (prime_zeroConeAreaInput_holds D hγ hρ w hw)

/-- **The exact `BundleSec4.L46TLocalReconstructionPrime` instance** on every
admissible disk, including the translated gamma field, the zero-cone field,
phase, all-visit inner-degree event and cross-excursion Borel counts. -/
def bundle_l46tLocalReconstructionPrime_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ)
    (k : ℕ) (ζ ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    BundleSec4.L46TLocalReconstructionPrime
      (l46tObservation ρ w) (l46tLocalRegion ρ w) P P
      (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) (BundleSec4.coneFieldVersion D))
      (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) U
      (GMS4b.l46tZeroConeFieldVersion D) hIG₀ U
      (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
      (l46tZeroConeCellModel D hγ).curve
      (ball w ((1 - ρ) / 16)) ε k ζ :=
  bundle_primeReconstruction_versioned_of_configInput D hγ hρ w hw
    (prime_zeroConeConfigInput_holds D hγ hρ w hw) hε k ζ

end MatedCRTHarmonic.GMS4c

