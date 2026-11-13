/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.L46TAdapter at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.L46TGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TTransfer

/-!
# The Cameron–Martin comparison on L46T's observation disk

The source fields are pulled back by `z ↦ z-z₀`, where
`z₀=w+(1-ρ)/2`. The target is the normalized whole-plane GFF version of
the zero-cone on `l46tObservation ρ w`, with the original independent IG
field. The density has some exponent above one.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set TopologicalSpace Metric LQGMetric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

/-- The exact `GMS4c.LocalFieldLawComparison` structure on the observation
region named by L46T, using measurable versions of the frozen cone fields.
The a.e. identities identify those versions with the actual frozen fields. -/
theorem IsMatingOfTreesCoupling.exists_l46tLocalFieldLawComparison
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    let z₀ : ℂ := w + (((1 - ρ) / 2 : ℝ) : ℂ)
    ∃ (hγm h₀m : Ω → DistC),
      Measurable hγm ∧
      (fun ω => coneField (X ω)
        (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω))) =ᵐ[P] hγm ∧
      IsNormalizedWPGFF h₀m P ∧
      (fun ω => restrictTo (GMS4b.l46tObservation ρ w) (coneField (X₀ ω)
        (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω)))) =ᵐ[P]
        (fun ω => restrictTo (GMS4b.l46tObservation ρ w) (h₀m ω)) ∧
      ∃ p q : ℝ, 1 < p ∧
        Nonempty (GMS4c.LocalFieldLawComparison (GMS4b.l46tObservation ρ w) P P
          (GMS4b.l46tTranslatedField z₀ hγm)
          (GMS4b.l46tTranslatedField z₀ hIG₀)
          h₀m hIG₀ p q) := by
  let s : ℝ := 1 - ρ
  let a : ℝ := s / 4
  let b : ℝ := s / 2
  let z₀ : ℂ := w + ((b : ℝ) : ℂ)
  let t : ℂ := -z₀
  let W : Opens ℂ := ⟨ball w a, isOpen_ball⟩
  let V : Opens ℂ := ⟨ball w b, isOpen_ball⟩
  obtain ⟨hK, hCone, hWV, hKW, hKV, hadm, hne, hV₁, hVR, hWunit⟩ :=
    l46t_affine_geometry hρ w hw
  have hres := IsMatingOfTreesCoupling.exists_affineZeroConeComparison hC hγ
    W V t hK hCone hWV hKW hKV hadm hne hV₁ hVR hWunit
  exact hres

end MatedCRTHarmonic.GMSCM
