import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.TwoBrownianGFF
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFFStd

/-! # Independent Brownian motions and a whole-plane Gaussian free field

The independent drivers can be realized on a fixed standard Borel space.
The product construction follows the existence argument in Leonardo Bonanno's
`MatedCRTHarmonic.MoTPort.Foundations.Cone`, commit `fdb5cad17d11550228cf8dbaf6216e69fc3d2d82`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open QuantumZipper LQGMetric
open MatedCRTHarmonic.MoTPort

namespace LatticeProb

example : StandardBorelSpace (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) := inferInstance

/-- Two independent real Brownian motions and an independent whole-plane GFF
exist on the standard Borel space consisting of three Gaussian sequences. -/
theorem exists_twoBrownian_wholePlaneGFF_standardBorel :
    ∃ (P : Measure (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)))
      (B B' : ℝ≥0 → (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) → ℝ)
      (X : (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) → DistC),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsBrownianReal B' P ∧
      IndepFun (pathOf B) (pathOf B') P ∧ IsWholePlaneGFF X P ∧
      ∀ (E : Type) [MeasurableSpace E] (F : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → E),
        IndepFun X (fun ω => F (pathOf B ω) (pathOf B' ω)) P := by
  obtain ⟨Bm, hB⟩ := BMExist.exists_isBrownianReal_stdP
  obtain ⟨P₂, g, hP₂, hg⟩ := GFFExist.exists_wholePlaneGFF_nat
  let P₁ := LQGDimension.ExistAsm.stdP
  have : IsProbabilityMeasure P₁ := inferInstance
  have : IsProbabilityMeasure P₂ := hP₂
  let P := (P₁.prod P₁).prod P₂
  have hfst : MeasurePreserving (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) => p.1.1) P P₁ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hsnd : MeasurePreserving (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) => p.1.2) P P₁ :=
    measurePreserving_snd.comp measurePreserving_fst
  have hlaw : P.map (fun p => g p.2) = P₂.map g := by
    change ((P₁.prod P₁).prod P₂).map (g ∘ Prod.snd) = P₂.map g
    rw [← Measure.map_map hg.measurable measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]
  refine ⟨P, fun t ω => Bm t ω.1.1, fun t ω => Bm t ω.1.2, fun ω => g ω.2,
    inferInstance, NonVacuity.nv_isBrownianReal hfst hB,
    NonVacuity.nv_isBrownianReal hsnd hB, ?_,
    DFGPS.L217.isWholePlaneGFF_of_map_eq (hg.measurable.comp measurable_snd) hg hlaw, ?_⟩
  · exact indepFun_comp_fst (NonVacuity.nv_indepFun_prod
      (fun ω : ℕ → ℝ => pathOf Bm ω) (fun ω : ℕ → ℝ => pathOf Bm ω))
  · intro E _ F
    exact (NonVacuity.nv_indepFun_prod (μ := P₁.prod P₁) (ν := P₂)
      (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => F (pathOf Bm ω.1) (pathOf Bm ω.2)) g).symm

end LatticeProb
