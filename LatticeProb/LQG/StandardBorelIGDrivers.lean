import LatticeProb.LQG.StandardBorelConeDrivers
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFWP
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P0

/-! # Independent cone and imaginary-geometry drivers

A normalized whole-plane Gaussian free field and an independent uniform phase
can be adjoined to the cone drivers on a standard Borel probability space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open QuantumZipper LQGMetric MatedCRTHarmonic.MoTPort

namespace LatticeProb

private abbrev ConeSpace := ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)
private abbrev IGSpace := (ℕ → ℝ) × ℝ

example : StandardBorelSpace (ConeSpace × IGSpace) := by
  have : StandardBorelSpace ConeSpace := inferInstance
  have : StandardBorelSpace IGSpace := inferInstance
  exact StandardBorelSpace.prod

/-- A normalized whole-plane GFF and a uniform phase, independent of each other
and jointly independent of the Brownian and GFF cone drivers. -/
theorem exists_cone_ig_drivers_standardBorel {r : ℝ} (hr : 0 < r) :
    ∃ (P : Measure ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)))
      (B B' : ℝ≥0 → ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)) → ℝ)
      (X H : ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)) → DistC)
      (U : ((((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × ((ℕ → ℝ) × ℝ)) → ℝ),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsBrownianReal B' P ∧
      IndepFun (pathOf B) (pathOf B') P ∧ IsWholePlaneGFF X P ∧
      IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P ∧
      IsNormalizedWPGFF H P ∧ P.map U = volume[|Ico (0 : ℝ) r] ∧
      IndepFun H U P ∧ IndepFun (fun ω => (H ω, U ω))
        (fun ω => (X ω, pathOf B ω, pathOf B' ω)) P := by
  obtain ⟨P₁, B, B', X, hP₁, hB, hB', hBB', hX, hXB⟩ :=
    exists_twoBrownian_wholePlaneGFF_standardBorel
  obtain ⟨P₂, hP₂, H, hH⟩ := GFFExist.exists_normalizedWPGFF_nat
  let P₃ : Measure ℝ := volume[|Ico (0 : ℝ) r]
  have : IsProbabilityMeasure P₁ := hP₁
  have : IsProbabilityMeasure P₂ := hP₂
  have : IsProbabilityMeasure P₃ := WPGFFMod.isProbabilityMeasure_unif hr
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
  have hUlaw : P.map (fun ω => ω.2.2) = P₃ := by
    exact (measurePreserving_snd.comp (measurePreserving_snd :
      MeasurePreserving (Prod.snd : ConeSpace × IGSpace → IGSpace) P (P₂.prod P₃))).map_eq
  refine ⟨P, fun t ω => B t ω.1, fun t ω => B' t ω.1,
    fun ω => X ω.1, fun ω => H ω.2.1, fun ω => ω.2.2,
    inferInstance, NonVacuity.nv_isBrownianReal hfst hB,
    NonVacuity.nv_isBrownianReal hfst hB', indepFun_comp_fst hBB',
    DFGPS.L217.isWholePlaneGFF_of_map_eq (hX.measurable.comp measurable_fst) hX hXlaw,
    indepFun_comp_fst (hXB _ (fun x y => (x, y))),
    DFGPS.T12.isNormalizedWPGFF_of_map_eq (hH.1.measurable.comp hsndfst.measurable) hH hHlaw,
    hUlaw, ?_, ?_⟩
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hs' : (fun ω : ConeSpace × IGSpace => H ω.2.1) ⁻¹' s =
        Set.univ ×ˢ ((fun p : IGSpace => H p.1) ⁻¹' s) := by ext; simp
    have ht' : (fun ω : ConeSpace × IGSpace => ω.2.2) ⁻¹' t =
        Set.univ ×ˢ ((Prod.snd : IGSpace → ℝ) ⁻¹' t) := by ext; simp
    rw [hs', ht', Set.prod_inter_prod, Set.inter_self, Measure.prod_prod,
      Measure.prod_prod, Measure.prod_prod, measure_univ]
    simp only [one_mul]
    exact (NonVacuity.nv_indepFun_prod (μ := P₂) (ν := P₃) H id).measure_inter_preimage_eq_mul s t hs ht
  · exact (NonVacuity.nv_indepFun_prod (μ := P₁) (ν := P₂.prod P₃)
      (fun ω => (X ω, pathOf B ω, pathOf B' ω)) (fun ω => (H ω.1, ω.2))).symm

end LatticeProb
