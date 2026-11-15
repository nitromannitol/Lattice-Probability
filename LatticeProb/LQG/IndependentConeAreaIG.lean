import LatticeProb.LQG.StandardBorelIGDrivers
import LatticeProb.LQG.ConeAreaRandomMeasure

/-! # Independent cone area and imaginary-geometry drivers

The cone field and its area measure can be realized independently of a
normalized whole-plane GFF and a uniform phase.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open QuantumZipper LQGMetric MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic

namespace LatticeProb

private abbrev ConeSpace := ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)
private abbrev IGSpace := (ℕ → ℝ) × ℝ

/-- The γ-cone field and its area are jointly independent of an independent
normalized whole-plane GFF and uniform phase, on a standard Borel space. -/
theorem exists_independent_coneArea_ig_standardBorel {γ r : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hr : 0 < r) :
    ∃ (P : Measure (ConeSpace × IGSpace))
      (B B' : ℝ≥0 → (ConeSpace × IGSpace) → ℝ)
      (X H : (ConeSpace × IGSpace) → DistC)
      (U : (ConeSpace × IGSpace) → ℝ),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsBrownianReal B' P ∧
      IndepFun (pathOf B) (pathOf B') P ∧ IsWholePlaneGFF X P ∧
      IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P ∧
      IsNormalizedWPGFF H P ∧ P.map U = volume[|Ico (0 : ℝ) r] ∧
      IndepFun H U P ∧
      AEMeasurable (fun ω => CellScaling.lqgArea γ
        (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P ∧
      IndepFun (fun ω =>
        (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.lqgArea γ (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))))
        (fun ω => (H ω, U ω)) P := by
  obtain ⟨P₁, B, B', X, hP₁, hB, hB', hBB, hX, hXB⟩ :=
    exists_twoBrownian_wholePlaneGFF_standardBorel
  obtain ⟨P₂, hP₂, H, hH⟩ := GFFExist.exists_normalizedWPGFF_nat
  let P₃ : Measure ℝ := volume[|Ico (0 : ℝ) r]
  let : IsProbabilityMeasure P₁ := hP₁
  let : IsProbabilityMeasure P₂ := hP₂
  let : IsProbabilityMeasure P₃ := WPGFFMod.isProbabilityMeasure_unif hr
  let P : Measure (ConeSpace × IGSpace) := P₁.prod (P₂.prod P₃)
  have hfst : MeasurePreserving (Prod.fst : ConeSpace × IGSpace → ConeSpace) P P₁ :=
    measurePreserving_fst
  have hsndfst : MeasurePreserving (fun ω : ConeSpace × IGSpace => ω.2.1) P P₂ :=
    measurePreserving_fst.comp measurePreserving_snd
  have hHlaw : P.map (fun ω => H ω.2.1) = P₂.map H := by
    change P.map (H ∘ fun ω : ConeSpace × IGSpace => ω.2.1) = P₂.map H
    rw [← Measure.map_map hH.1.measurable hsndfst.measurable, hsndfst.map_eq]
  have hXlaw : P.map (fun ω => X ω.1) = P₁.map X := by
    change P.map (X ∘ Prod.fst) = P₁.map X
    rw [← Measure.map_map hX.measurable measurable_fst, hfst.map_eq]
  have hUlaw : P.map (fun ω : ConeSpace × IGSpace => ω.2.2) = P₃ :=
    (measurePreserving_snd.comp (measurePreserving_snd :
      MeasurePreserving (Prod.snd : ConeSpace × IGSpace → IGSpace) P (P₂.prod P₃))).map_eq
  have hBlift := NonVacuity.nv_isBrownianReal hfst hB
  have hB'lift := NonVacuity.nv_isBrownianReal hfst hB'
  have hBBlift : IndepFun (fun ω : ConeSpace × IGSpace => pathOf B ω.1)
      (fun ω => pathOf B' ω.1) P := indepFun_comp_fst hBB
  have hXlift := DFGPS.L217.isWholePlaneGFF_of_map_eq
    (hX.measurable.comp measurable_fst) hX hXlaw
  have hXBlift : IndepFun (fun ω : ConeSpace × IGSpace => X ω.1)
      (fun ω => (pathOf B ω.1, pathOf B' ω.1)) P :=
    indepFun_comp_fst (hXB _ (fun x y => (x, y)))
  refine ⟨P, fun t ω => B t ω.1, fun t ω => B' t ω.1,
    fun ω => X ω.1, fun ω => H ω.2.1, fun ω => ω.2.2,
    inferInstance, hBlift, hB'lift, hBBlift, hXlift, hXBlift,
    DFGPS.T12.isNormalizedWPGFF_of_map_eq (hH.1.measurable.comp hsndfst.measurable) hH hHlaw,
    hUlaw, ?_, ?_, ?_⟩
  · exact NonVacuity.nv_indepFun_snd
      (NonVacuity.nv_indepFun_prod (μ := P₂) (ν := P₃) H id)
  · exact aemeasurable_gammaConeArea hγ hγ2 hXlift hBlift hB'lift hBBlift hXBlift
  · exact NonVacuity.nv_indepFun_prod (μ := P₁) (ν := P₂.prod P₃)
      (fun ω =>
        (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.lqgArea γ (CellScaling.coneField (X ω)
          (CellScaling.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))))
      (fun ω : IGSpace => (H ω.1, ω.2))

end LatticeProb
