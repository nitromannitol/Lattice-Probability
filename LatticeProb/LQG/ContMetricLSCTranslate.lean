import LatticeProb.LQG.ContMetricLSC
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.TranslateDist

/-!
# Translation invariance for continuous metrics as extended metrics

The translated field `h(· + z)` has two encodings in the library: the Ding-Gwynne form
`translateDist z h = h ∘ (φ ↦ φ(· - z))` and the Gwynne-Miller affine form
`affineComp 1 z h = h(1 · + z)`. They are equal (`translateDist_eq_affineComp_one`).

Consequently Axiom IV′ (translation invariance) for a map `h ↦ D_h` into continuous metrics, in
the Gwynne-Miller form `D_{h(· + z)}(u, v) = D_h(u + z, v + z)`, gives Axiom IV′ in the
Ding-Gwynne form for the lower semicontinuous extended metrics `contToLSCMetric ∘ D`
(`translation_contToLSCMetric`). The Gwynne-Miller form itself is the coordinate change formula at
`r = 1` (`translation_affineComp_of_coord`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.LQG

/-- The test function translation `φ ↦ φ(· - z)` is the affine pullback with `r = 1`. -/
theorem testTranslate_eq_testAffinePull_one (z : ℂ) (φ : LQGMetric.TestC) :
    SupercriticalLQGUniqueness.testTranslate z φ = LQGMetric.testAffinePull 1 z φ := by
  ext x
  rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero φ x, Complex.ofReal_one, div_one]
  rfl

/-- **The two encodings of the translated field agree**: `⟨h(· + z), φ⟩ = ⟨h, φ(· - z)⟩` is the
affine composition `h(1 · + z)`. -/
theorem translateDist_eq_affineComp_one (z : ℂ) (h : LQGMetric.DistC) :
    SupercriticalLQGUniqueness.translateDist z h = LQGMetric.affineComp 1 z h := by
  ext φ
  simp only [SupercriticalLQGUniqueness.translateDist, LQGMetric.affineComp, one_pow, inv_one,
    one_smul]
  exact congrArg h (testTranslate_eq_testAffinePull_one z φ)

/-- **Axiom IV′ transfers**: translation invariance of `h ↦ D_h` in the Gwynne-Miller form gives
translation invariance of `h ↦ contToLSCMetric D_h` in the Ding-Gwynne form. -/
theorem translation_contToLSCMetric {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (htr : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (D (LQGMetric.affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (contToLSCMetric (D (SupercriticalLQGUniqueness.translateDist z (h ω)))).1 (u, v) =
          (contToLSCMetric (D (h ω))).1 (u + z, v + z) := by
  intro Ω _ P _ h hh z
  filter_upwards [htr P h hh z] with ω hω u v
  have e1 := contToLSCMetric_apply (D (LQGMetric.affineComp 1 z (h ω))) (u, v)
  have e2 := contToLSCMetric_apply (D (h ω)) (u + z, v + z)
  rw [translateDist_eq_affineComp_one]
  calc (contToLSCMetric (D (LQGMetric.affineComp 1 z (h ω)))).1 (u, v)
      = ENNReal.ofReal ((D (LQGMetric.affineComp 1 z (h ω))).1 (u, v)) := e1
    _ = ENNReal.ofReal ((D (h ω)).1 (u + z, v + z)) := by rw [hω u v]
    _ = (contToLSCMetric (D (h ω))).1 (u + z, v + z) := e2.symm

/-- **Translation invariance from the coordinate change formula** (Gwynne-Miller (1.15) at
`r = 1`, where the additive constant `Q' log r` vanishes). -/
theorem translation_affineComp_of_coord {Q' : ℝ} {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (D (LQGMetric.affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z) := by
  intro Ω _ P _ h hh z
  filter_upwards [hcoord P h hh 1 one_pos z] with ω hω u v
  have := hω u v
  rw [Real.log_one, mul_zero, LQGMetric.GFFLaw.addConst_zero'] at this
  simpa using this.symm

/-- Axiom IV′ in the Ding-Gwynne form for `contToLSCMetric ∘ D`, from the coordinate change
formula of `D`. -/
theorem translation_contToLSCMetric_of_coord {Q' : ℝ}
    {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hcoord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (r * u + z, r * v + z) =
          (D (LQGMetric.addConst (LQGMetric.affineComp r z (h ω)) (Q' * Real.log r))).1 (u, v)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (contToLSCMetric (D (SupercriticalLQGUniqueness.translateDist z (h ω)))).1 (u, v) =
          (contToLSCMetric (D (h ω))).1 (u + z, v + z) :=
  translation_contToLSCMetric (translation_affineComp_of_coord hcoord)

end LatticeProb.LQG
