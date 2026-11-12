/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.Lateral at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Lateral
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
DMS Def 4.10 and Lemmas 4.2–4.4 : the lateral part
`h − h_{|·|}(0)` of a whole-plane GFF is the projection onto `H₂(ℂ)` (functions with mean zero on circles
about `0`); its law is invariant under every fixed dilation `z ↦ r z`. This is the lateral input of
DMS Prop 4.13(i). In the present formalization (`CellScaling.lateralPart`,
`DistC` with the cylinder σ-algebra of pairings):

  `map_affineComp_lateralPart`: `law (affineComp r 0 (lateralPart X)) = law (lateralPart X)`, `r > 0`.

Proof: pairings of the lateral part are a.s. the pairings of `X` with the mean-zero tests `φ − φ̄`
; symmetrization commutes with dilation
(`symmTest_testAffinePull_zero`); the law of the mean-zero pairings of a
whole-plane GFF is unique (LQGMetric `GFFLaw.map_pairProc_eq`) and dilation preserves the
whole-plane GFF property (LQGMetric `IsWholePlaneGFF.affineComp`); a measure on `DistC` is
determined by its finite-dimensional pairing laws (`distC_measure_ext`, Mathlib's projective-limit
uniqueness). This extends `map_scaledLateralPairProc_eq` (for `TestC0`-indexed pairings),
here for the `DistC`-valued field itself.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace MatedCRTHarmonic.ConeScaling

open LQGMetric MatedCRTHarmonic.GMCFacts

/-! ### Measures on `DistC` -/

/-- The pairing map of a distribution. -/
def evDist (h : DistC) : TestC → ℝ := fun φ => h φ

theorem measurable_evDist : Measurable evDist :=
  measurable_pi_iff.2 fun φ => GFFInv.measurable_pair φ

/-- A measure on `DistC` is determined by the law of its pairing process (the σ-algebra of `DistC`
is the cylinder σ-algebra of pairings). -/
theorem distC_measure_ext {μ ν : Measure DistC} (h : μ.map evDist = ν.map evDist) : μ = ν := by
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  change μ (evDist ⁻¹' t) = ν (evDist ⁻¹' t)
  rw [← Measure.map_apply measurable_evDist ht, ← Measure.map_apply measurable_evDist ht, h]

/-- The lateral part is a measurable function of the field. -/
theorem measurable_lateralPart : Measurable CellScaling.lateralPart := by
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  have hR : Measurable fun p : DistC × ℂ => CellScaling.radialAvg p.1 p.2 :=
    measurable_circleAvg.comp (f := fun p : DistC × ℂ => (p.1, ‖p.2‖, (0 : ℂ)))
      (measurable_fst.prodMk ((measurable_norm.comp measurable_snd).prodMk measurable_const))
  exact (GFFInv.measurable_pair φ).sub
    (MoTPort.ConeMeas2.measurable_ofFunC_apply (F := CellScaling.radialAvg) hR φ)

/-! ### Symmetrization and dilation -/

/-- Radial symmetrization commutes with a positive dilation about the origin. -/
theorem symmTest_testAffinePull_zero {r : ℝ} (hr : 0 < r) (φ : TestC) :
    symmTest (testAffinePull r 0 φ) = testAffinePull r 0 (symmTest φ) := by
  ext w
  simp only [symmTest_apply, rotSymm, testAffinePull_apply _ _ hr.ne', sub_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [mul_div_assoc]

/-- The mean-zero test function `φ − φ̄`. -/
def latTest (φ : TestC) : TestC0 := ⟨φ - symmTest φ, integral_sub_symmTest φ⟩

theorem latTest_testAffinePull {r : ℝ} (hr : 0 < r) (φ : TestC) :
    (latTest (testAffinePull r 0 φ)).1 = testAffinePull r 0 (latTest φ).1 := by
  simp only [latTest, map_sub, symmTest_testAffinePull_zero hr]

/-! ### The law of the lateral part -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- **Dilation invariance of the lateral law** (DMS Def 4.10, Lemmas 4.2–4.4): for a whole-plane GFF
`X` and `r > 0`, `affineComp r 0 (lateralPart X)` has the law of `lateralPart X`. -/
theorem map_affineComp_lateralPart (hX : IsWholePlaneGFF X P) {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => affineComp r 0 (CellScaling.lateralPart (X ω))) =
      P.map (fun ω => CellScaling.lateralPart (X ω)) := by
  have := hX.gaussian.isProbabilityMeasure
  have hXm := hX.measurable
  have hL : Measurable fun ω => CellScaling.lateralPart (X ω) := measurable_lateralPart.comp hXm
  have hAL : Measurable fun ω => affineComp r 0 (CellScaling.lateralPart (X ω)) :=
    MoTPort.ConeMeas.measurable_affineComp_joint.comp (measurable_const.prodMk hL)
  apply distC_measure_ext
  rw [Measure.map_map measurable_evDist hAL, Measure.map_map measurable_evDist hL]
  have hfin : ∀ I : Finset TestC,
      (P.map (evDist ∘ fun ω => affineComp r 0 (CellScaling.lateralPart (X ω)))).map I.restrict =
        (P.map (evDist ∘ fun ω => CellScaling.lateralPart (X ω))).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_evDist.comp hAL),
      Measure.map_map (Finset.measurable_restrict I) (measurable_evDist.comp hL)]
    have hleft : (I.restrict ∘ evDist ∘ fun ω => affineComp r 0 (CellScaling.lateralPart (X ω))) =ᵐ[P]
        fun ω (i : I) => affineComp r 0 (X ω) (latTest i.1).1 := by
      filter_upwards [ae_all_iff.2 fun i : I => ae_lateralPart_apply hX (testAffinePull r 0 i.1)]
        with ω hω
      funext i
      have h1 := hω i
      simp only [Function.comp_apply, Finset.restrict, evDist, GFFInv.affineComp_apply]
      rw [h1, ← latTest_testAffinePull hr]
      rfl
    have hright : (I.restrict ∘ evDist ∘ fun ω => CellScaling.lateralPart (X ω)) =ᵐ[P]
        fun ω (i : I) => X ω (latTest i.1).1 := by
      filter_upwards [ae_all_iff.2 fun i : I => ae_lateralPart_apply hX i.1] with ω hω
      funext i
      exact hω i
    rw [Measure.map_congr hleft, Measure.map_congr hright]
    let F : (TestC0 → ℝ) → (I → ℝ) := fun q i => q (latTest i.1)
    have hF : Measurable F := measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hlaw := congrArg (Measure.map F) (GFFLaw.map_pairProc_eq (hX.affineComp hr 0) hX)
    rw [Measure.map_map hF (GFFLaw.measurable_pairProc (hX.affineComp hr 0).measurable),
      Measure.map_map hF (GFFLaw.measurable_pairProc hXm)] at hlaw
    exact hlaw
  exact IsProjectiveLimit.unique
    (P := fun I => (P.map (evDist ∘ fun ω => CellScaling.lateralPart (X ω))).map I.restrict)
    hfin (fun _ => rfl)

end MatedCRTHarmonic.ConeScaling
