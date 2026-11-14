/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiGlueBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PathDifferenceEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiTriangle

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_phi_glue_bound
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P : Measure Ω₁) (Q : Measure Ω₂) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (K : Set ℂ)
    (X Y₁ : ℂ → Ω₁ → ℝ) (Y₂ Φ : ℂ → Ω₂ → ℝ)
    (hY₁c : ∀ ω, Continuous fun z => Y₁ z ω)
    (hY₁m : ∀ z, Measurable (Y₁ z))
    (hY₂c : ∀ ω, Continuous fun z => Y₂ z ω)
    (hY₂m : ∀ z, Measurable (Y₂ z))
    (hΦc : ∀ ω, Continuous fun z => Φ z ω)
    (hΦm : ∀ z, Measurable (Φ z))
    (hlaw : P.map (pathC Y₁ hY₁c) = Q.map (pathC Y₂ hY₂c))
    (a b : ℝ) :
    let R := dg20GlueMeasure P Q (pathC Y₁ hY₁c)
      (pathC Y₂ hY₂c) (pathC Φ hΦc) (measurable_pathC hY₁c hY₁m)
    R {p | ∃ z ∈ K, a + b < |X z p.1 - p.2 z|} ≤
      P {ω | ∃ z ∈ K, a < |X z ω - Y₁ z ω|} +
      Q {ω | ∃ z ∈ K, b < |Y₂ z ω - Φ z ω|} := by
  dsimp only
  set R := dg20GlueMeasure P Q (pathC Y₁ hY₁c)
      (pathC Y₂ hY₂c) (pathC Φ hΦc) (measurable_pathC hY₁c hY₁m)
  have hjoint := dg20GlueMeasure_joint P Q (pathC Y₁ hY₁c)
    (pathC Y₂ hY₂c) (pathC Φ hΦc)
    (measurable_pathC hY₁c hY₁m) (measurable_pathC hY₂c hY₂m)
    (measurable_pathC hΦc hΦm) hlaw
  have hfst := dg20GlueMeasure_fst P Q (pathC Y₁ hY₁c)
    (pathC Y₂ hY₂c) (pathC Φ hΦc) (measurable_pathC hY₁c hY₁m)
  have hA : R {p | ∃ z ∈ K, a < |X z p.1 - Y₁ z p.1|} ≤
      P {ω | ∃ z ∈ K, a < |X z ω - Y₁ z ω|} := by
    let A : Set Ω₁ := {ω | ∃ z ∈ K, a < |X z ω - Y₁ z ω|}
    calc
      R {p | ∃ z ∈ K, a < |X z p.1 - Y₁ z p.1|} = R (Prod.fst ⁻¹' A) := rfl
      _ ≤ (R.map Prod.fst) A := Measure.le_map_apply measurable_fst.aemeasurable A
      _ = P A := by simpa only [R] using congrArg (fun m : Measure Ω₁ => m A) hfst
  have hB : R {p | ∃ z ∈ K, b < |Y₁ z p.1 - p.2 z|} ≤
      Q {ω | ∃ z ∈ K, b < |Y₂ z ω - Φ z ω|} := by
    let E := dg20PathDiffEvent K b
    have hE : MeasurableSet E := (dg20PathDiffEvent_isOpen K b).measurableSet
    let f : Ω₁ × C(ℂ, ℝ) → C(ℂ, ℝ) × C(ℂ, ℝ) :=
      fun p => (pathC Y₁ hY₁c p.1, p.2)
    let g : Ω₂ → C(ℂ, ℝ) × C(ℂ, ℝ) :=
      fun ω => (pathC Y₂ hY₂c ω, pathC Φ hΦc ω)
    have hf : Measurable f :=
      ((measurable_pathC hY₁c hY₁m).comp measurable_fst).prodMk measurable_snd
    have hg : Measurable g :=
      (measurable_pathC hY₂c hY₂m).prodMk (measurable_pathC hΦc hΦm)
    have hfg : R.map f = Q.map g := by simpa only [R, f, g] using hjoint
    calc
      R {p | ∃ z ∈ K, b < |Y₁ z p.1 - p.2 z|} = R (f ⁻¹' E) := rfl
      _ = (R.map f) E := (Measure.map_apply hf hE).symm
      _ = (Q.map g) E := by rw [hfg]
      _ = Q {ω | ∃ z ∈ K, b < |Y₂ z ω - Φ z ω|} := by
        rw [Measure.map_apply hg hE]
        rfl
      _ ≤ _ := le_rfl
  have hsum : R {p | ∃ z ∈ K, a < |X z p.1 - Y₁ z p.1|} +
      R {p | ∃ z ∈ K, b < |Y₁ z p.1 - p.2 z|} ≤
      P {ω | ∃ z ∈ K, a < |X z ω - Y₁ z ω|} +
      Q {ω | ∃ z ∈ K, b < |Y₂ z ω - Φ z ω|} :=
    add_le_add hA hB
  exact (dg20_heat_phi_bad_event_measure_le R K
    (fun z (p : Ω₁ × C(ℂ, ℝ)) => X z p.1)
    (fun z (p : Ω₁ × C(ℂ, ℝ)) => Y₁ z p.1)
    (fun z (p : Ω₁ × C(ℂ, ℝ)) => p.2 z) a b).trans hsum

end SupercriticalLQGUniqueness.B2.DG20Pt
