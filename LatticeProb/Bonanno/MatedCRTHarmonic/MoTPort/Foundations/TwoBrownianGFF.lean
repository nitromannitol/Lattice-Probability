/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules QuantumZipper.Proofs.Probability.BMExistence and
   MatedCRTHarmonic.MoTPort.Foundations.Cone at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82.
   The declarations below retain their source statements and proofs. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Field
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Pointwise

namespace QuantumZipper

/-- **Brownian motion exists.** -/
theorem brownianMotionExists : NonVacuity.BrownianMotionExists := by
  obtain ⟨B, hB⟩ := BMExist.exists_isBrownianReal_stdP
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, B, inferInstance, hB⟩


end QuantumZipper

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper LQGMetric

/-- independence of two random variables survives passing to a product space through the first
coordinate (two-variable form of `Wedge.iIndepFun_comp_fst`) -/
theorem indepFun_comp_fst {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {f : α → γ} {g : α → δ} {μ : Measure α}
    {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν] (h : IndepFun f g μ) :
    IndepFun (fun p : α × β => f p.1) (fun p => g p.1) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have e1 : (fun p : α × β => f p.1) ⁻¹' s = (f ⁻¹' s) ×ˢ (univ : Set β) := by ext; simp
  have e2 : (fun p : α × β => g p.1) ⁻¹' t = (g ⁻¹' t) ×ˢ (univ : Set β) := by ext; simp
  rw [e1, e2, Set.prod_inter_prod, Set.inter_self, Measure.prod_prod, Measure.prod_prod,
    Measure.prod_prod, h s t hs ht, measure_univ]
  simp

/-- the reference space: two independent Brownian motions and an independent whole-plane GFF -/
theorem exists_twoBM_wpGFF :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B B' : ℝ≥0 → Ω → ℝ) (X : Ω → Field),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsBrownianReal B' P ∧
      IndepFun (pathOf B) (pathOf B') P ∧ IsWholePlaneGFF X P ∧
      ∀ (E : Type) [MeasurableSpace E] (F : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → E),
        IndepFun X (fun ω => F (pathOf B ω) (pathOf B' ω)) P := by
  obtain ⟨Ω₁, _, P₁, Bm, hP₁, hB⟩ := brownianMotionExists
  obtain ⟨Ω₂, _, P₂, g, hP₂, hg⟩ := GFFExist.exists_wholePlaneGFF
  have hfst : MeasurePreserving (fun p : (Ω₁ × Ω₁) × Ω₂ => p.1.1) ((P₁.prod P₁).prod P₂) P₁ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hsnd : MeasurePreserving (fun p : (Ω₁ × Ω₁) × Ω₂ => p.1.2) ((P₁.prod P₁).prod P₂) P₁ :=
    measurePreserving_snd.comp measurePreserving_fst
  have hlaw : ((P₁.prod P₁).prod P₂).map (fun p : (Ω₁ × Ω₁) × Ω₂ => g p.2) = P₂.map g := by
    rw [show (fun p : (Ω₁ × Ω₁) × Ω₂ => g p.2) = g ∘ Prod.snd from rfl,
      ← Measure.map_map hg.measurable measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨(Ω₁ × Ω₁) × Ω₂, inferInstance, (P₁.prod P₁).prod P₂, fun t ω => Bm t ω.1.1,
    fun t ω => Bm t ω.1.2, fun ω => g ω.2, inferInstance, NonVacuity.nv_isBrownianReal hfst hB,
    NonVacuity.nv_isBrownianReal hsnd hB, ?_,
    DFGPS.L217.isWholePlaneGFF_of_map_eq (hg.measurable.comp measurable_snd) hg hlaw, ?_⟩
  · exact indepFun_comp_fst (f := fun ω : Ω₁ × Ω₁ => pathOf Bm ω.1)
      (g := fun ω : Ω₁ × Ω₁ => pathOf Bm ω.2) (NonVacuity.nv_indepFun_prod _ _)
  · intro E _ F
    exact (NonVacuity.nv_indepFun_prod (μ := P₁.prod P₁) (ν := P₂)
      (fun ω : Ω₁ × Ω₁ => F (pathOf Bm ω.1) (pathOf Bm ω.2)) g).symm

end MatedCRTHarmonic.MoTPort
