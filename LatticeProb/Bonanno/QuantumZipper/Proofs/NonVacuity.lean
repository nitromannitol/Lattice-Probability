/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.NonVacuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.LQG.Wedge
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess

/-!
# Non-vacuity of the main hypotheses

The hypotheses of the main statements (a Brownian motion independent of a free / zero-boundary
GFF; a quantum wedge independent of a Brownian motion) are jointly satisfiable.

Mathlib (at this pin) defines `IsBrownianReal` but contains **no existence theorem** for
Brownian motion (no Kolmogorov extension over `ℝ≥0`, no continuity theorem / Lévy
construction). We therefore isolate this single missing fact as the proposition
`BrownianMotionExists` and prove everything else from it.

Independence of the coordinates of a product measure is proved *without any measurability
assumption* on the random variables (via `Measure.prod_prod` for arbitrary sets), which
avoids having to prove measurability of the wedge field (which involves `lastZero`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

namespace NonVacuity

/-- The missing existence statement: a standard real Brownian motion exists on some probability
space. (Not in mathlib at this pin.) -/
def BrownianMotionExists : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure P ∧ IsBrownianReal B P

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {Q : Measure Ω'} {f : Ω' → Ω}

theorem nv_map_comp (hf : MeasurePreserving f Q P) {E : Type*} [MeasurableSpace E]
    {X : Ω → E} (hX : AEMeasurable X P) : Q.map (fun ω => X (f ω)) = P.map X := by
  rw [← hf.map_eq] at hX ⊢
  exact (AEMeasurable.map_map_of_aemeasurable hX hf.measurable.aemeasurable).symm

theorem nv_aemeas_comp (hf : MeasurePreserving f Q P) {E : Type*} [MeasurableSpace E]
    {X : Ω → E} (hX : AEMeasurable X P) : AEMeasurable (fun ω => X (f ω)) Q := by
  rw [← hf.map_eq] at hX
  exact hX.comp_aemeasurable hf.measurable.aemeasurable

theorem nv_hasLaw (hf : MeasurePreserving f Q P) {E : Type*} [MeasurableSpace E]
    {X : Ω → E} {μ : Measure E} (h : HasLaw X μ P) : HasLaw (fun ω => X (f ω)) μ Q where
  aemeasurable := nv_aemeas_comp hf h.aemeasurable
  map_eq := by rw [nv_map_comp hf h.aemeasurable, h.map_eq]

theorem nv_hasGaussianLaw (hf : MeasurePreserving f Q P) {E : Type*} [TopologicalSpace E]
    [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E]
    {X : Ω → E} (h : HasGaussianLaw X P) : HasGaussianLaw (fun ω => X (f ω)) Q where
  aemeasurable := nv_aemeas_comp hf h.aemeasurable
  isGaussian_map := by rw [nv_map_comp hf h.aemeasurable]; exact h.isGaussian_map

theorem nv_isGaussianProcess (hf : MeasurePreserving f Q P) {T : Type*}
    {X : T → Ω → ℝ} (h : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω => X t (f ω)) Q :=
  ⟨fun I => nv_hasGaussianLaw hf (h.hasGaussianLaw I)⟩

theorem nv_integral (hf : MeasurePreserving f Q P) {g : Ω → ℝ} (hg : Measurable g) :
    ∫ ω, g (f ω) ∂Q = ∫ ω, g ω ∂P := by
  rw [← hf.map_eq, integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable]

theorem nv_cov (hf : MeasurePreserving f Q P) {g h : Ω → ℝ} (hg : Measurable g)
    (hh : Measurable h) : cov[fun ω => g (f ω), fun ω => h (f ω); Q] = cov[g, h; P] := by
  rw [← hf.map_eq, covariance_map hg.aestronglyMeasurable hh.aestronglyMeasurable
    hf.measurable.aemeasurable]
  rfl

theorem nv_ae_eq (hf : MeasurePreserving f Q P) {g h : Ω → ℝ} (hgh : g =ᵐ[P] h) :
    (fun ω => g (f ω)) =ᵐ[Q] fun ω => h (f ω) :=
  ae_eq_comp hf.measurable.aemeasurable (by rw [hf.map_eq]; exact hgh)

theorem nv_isBrownianReal (hf : MeasurePreserving f Q P) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) : IsBrownianReal (fun t ω => B t (f ω)) Q :=
  ⟨⟨fun I => nv_hasLaw hf (hB.hasLaw I)⟩,
    ae_of_ae_map hf.measurable.aemeasurable (by rw [hf.map_eq]; exact hB.cont)⟩

theorem nv_freeGFF (hf : MeasurePreserving f Q P) {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) : IsFreeGFFModConstH (fun ω => X (f ω)) Q where
  measurable_coord μ := (hX.measurable_coord μ).comp hf.measurable
  gaussian := nv_isGaussianProcess hf hX.gaussian
  centered μ ν hμ hν hm := by
    rw [nv_integral hf (g := fun ω => X ω μ - X ω ν)
      ((hX.measurable_coord μ).sub (hX.measurable_coord ν))]
    exact hX.centered μ ν hμ hν hm
  covariance_eq p q h1 h2 h3 h4 h5 h6 := by
    rw [nv_cov hf (g := fun ω => X ω p.1 - X ω p.2) (h := fun ω => X ω q.1 - X ω q.2)
      ((hX.measurable_coord _).sub (hX.measurable_coord _))
      ((hX.measurable_coord _).sub (hX.measurable_coord _))]
    exact hX.covariance_eq p q h1 h2 h3 h4 h5 h6
  linear μ ν hμ hν a b := nv_ae_eq hf (hX.linear μ ν hμ hν a b)

theorem nv_zeroGFF (hf : MeasurePreserving f Q P) {X : Ω → FieldSample}
    (hX : IsZeroBoundaryGFFH X P) : IsZeroBoundaryGFFH (fun ω => X (f ω)) Q where
  measurable_coord μ := (hX.measurable_coord μ).comp hf.measurable
  gaussian := nv_isGaussianProcess hf hX.gaussian
  centered μ hμ := by
    rw [nv_integral hf (g := fun ω => X ω μ) (hX.measurable_coord μ)]
    exact hX.centered μ hμ
  covariance_eq μ ν hμ hν := by
    rw [nv_cov hf (g := fun ω => X ω μ) (h := fun ω => X ω ν)
      (hX.measurable_coord _) (hX.measurable_coord _)]
    exact hX.covariance_eq μ ν hμ hν

end Transfer

section Indep

variable {α β 𝓧 𝓨 : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- Coordinates of a product probability measure are independent, with no measurability
assumptions on the random variables. -/
theorem nv_indepFun_prod (X : α → 𝓧) (Y : β → 𝓨) :
    IndepFun (fun p : α × β => X p.1) (fun p => Y p.2) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have e1 : (fun p : α × β => X p.1) ⁻¹' s = (X ⁻¹' s) ×ˢ (Set.univ : Set β) := by ext; simp
  have e2 : (fun p : α × β => Y p.2) ⁻¹' t = (Set.univ : Set α) ×ˢ (Y ⁻¹' t) := by ext; simp
  have e3 : (X ⁻¹' s) ×ˢ (Set.univ : Set β) ∩ (Set.univ : Set α) ×ˢ (Y ⁻¹' t)
      = (X ⁻¹' s) ×ˢ (Y ⁻¹' t) := by ext; simp
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp

theorem nv_indepFun_snd {F : β → 𝓧} {G : β → 𝓨} (h : IndepFun F G ν) :
    IndepFun (fun p : α × β => F p.2) (fun p => G p.2) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have e1 : (fun p : α × β => F p.2) ⁻¹' s = (Set.univ : Set α) ×ˢ (F ⁻¹' s) := by ext; simp
  have e2 : (fun p : α × β => G p.2) ⁻¹' t = (Set.univ : Set α) ×ˢ (G ⁻¹' t) := by ext; simp
  have e3 : (Set.univ : Set α) ×ˢ (F ⁻¹' s) ∩ (Set.univ : Set α) ×ˢ (G ⁻¹' t)
      = (Set.univ : Set α) ×ˢ (F ⁻¹' s ∩ G ⁻¹' t) := by ext; simp
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, h s t hs ht]
  simp

omit [IsProbabilityMeasure μ] in
theorem nv_indepFun_fst {F : α → 𝓧} {G : α → 𝓨} (h : IndepFun F G μ) :
    IndepFun (fun p : α × β => F p.1) (fun p => G p.1) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have e1 : (fun p : α × β => F p.1) ⁻¹' s = (F ⁻¹' s) ×ˢ (Set.univ : Set β) := by ext; simp
  have e2 : (fun p : α × β => G p.1) ⁻¹' t = (G ⁻¹' t) ×ˢ (Set.univ : Set β) := by ext; simp
  have e3 : (F ⁻¹' s) ×ˢ (Set.univ : Set β) ∩ (G ⁻¹' t) ×ˢ (Set.univ : Set β)
      = (F ⁻¹' s ∩ G ⁻¹' t) ×ˢ (Set.univ : Set β) := by ext; simp
  rw [e1, e2, e3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, h s t hs ht]
  simp

end Indep

/-- **(1)** A Brownian motion independent of a free-boundary GFF (mod constants) exists,
given the existence of Brownian motion. -/
theorem exists_BM_indep_freeGFF (hBM : BrownianMotionExists) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
      (X : Ω → FieldSample), IsProbabilityMeasure P ∧ IsBrownianReal B P ∧
      IsFreeGFFModConstH X P ∧ IndepFun (pathOf B) X P := by
  obtain ⟨Ω₁, _, P₁, B, hP₁, hB⟩ := hBM
  obtain ⟨Ω₂, _, P₂, X, hP₂, hX⟩ := exists_freeGFF
  exact ⟨Ω₁ × Ω₂, inferInstance, P₁.prod P₂, fun t ω => B t ω.1, fun ω => X ω.2,
    inferInstance, nv_isBrownianReal (measurePreserving_fst) hB,
    nv_freeGFF (measurePreserving_snd) hX, nv_indepFun_prod (pathOf B) X⟩

/-- **(2)** A Brownian motion independent of a zero-boundary GFF exists, given the existence of
Brownian motion. -/
theorem exists_BM_indep_zeroGFF (hBM : BrownianMotionExists) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
      (X : Ω → FieldSample), IsProbabilityMeasure P ∧ IsBrownianReal B P ∧
      IsZeroBoundaryGFFH X P ∧ IndepFun (pathOf B) X P := by
  obtain ⟨Ω₁, _, P₁, B, hP₁, hB⟩ := hBM
  obtain ⟨Ω₂, _, P₂, X, hP₂, hX⟩ := exists_zeroGFF
  exact ⟨Ω₁ × Ω₂, inferInstance, P₁.prod P₂, fun t ω => B t ω.1, fun ω => X ω.2,
    inferInstance, nv_isBrownianReal (measurePreserving_fst) hB,
    nv_zeroGFF (measurePreserving_snd) hX, nv_indepFun_prod (pathOf B) X⟩

/-- **(3)** For `α < Q`, an α-quantum wedge independent of a Brownian motion exists, given the
existence of Brownian motion. The space is `Ω₁ × ((Ω₁ × Ω₁) × Ω₂)`: the independent Brownian
motion, the two wedge Brownian motions, and the free GFF; the wedge field is its own
reference. -/
theorem exists_wedge_indep_BM (hBM : BrownianMotionExists) {γ α : ℝ} (hα : α < Qc γ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → FieldSample)
      (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P ∧ IsQuantumWedge γ α Y P ∧
      IsBrownianReal B P ∧ IndepFun (pathOf B) Y P := by
  obtain ⟨Ω₁, _, P₁, B, hP₁, hB⟩ := hBM
  obtain ⟨Ω₂, _, P₂, X, hP₂, hX⟩ := exists_freeGFF
  -- the reference space
  let P₀ : Measure ((Ω₁ × Ω₁) × Ω₂) := (P₁.prod P₁).prod P₂
  let A₀ : ℝ → (Ω₁ × Ω₁) × Ω₂ → ℝ := fun t ω =>
    wedgePath α (Qc γ) (fun s => B s ω.1.1) (fun s => B s ω.1.2) t
  let Y₀ : (Ω₁ × Ω₁) × Ω₂ → FieldSample := fun ω =>
    canonical γ (wedgeField (lateralPart (X ω.2)) (fun t => A₀ t ω) (Qc γ))
  let P : Measure (Ω₁ × ((Ω₁ × Ω₁) × Ω₂)) := P₁.prod P₀
  have hsnd : MeasurePreserving (fun ω : Ω₁ × ((Ω₁ × Ω₁) × Ω₂) => ω.2) P P₀ :=
    measurePreserving_snd
  have h1 : MeasurePreserving (fun ω : Ω₁ × ((Ω₁ × Ω₁) × Ω₂) => ω.2.1.1) P P₁ :=
    measurePreserving_fst.comp (measurePreserving_fst.comp hsnd)
  have h2 : MeasurePreserving (fun ω : Ω₁ × ((Ω₁ × Ω₁) × Ω₂) => ω.2.1.2) P P₁ :=
    measurePreserving_snd.comp (measurePreserving_fst.comp hsnd)
  have hXm : MeasurePreserving (fun ω : Ω₁ × ((Ω₁ × Ω₁) × Ω₂) => ω.2.2) P P₂ :=
    measurePreserving_snd.comp hsnd
  refine ⟨Ω₁ × ((Ω₁ × Ω₁) × Ω₂), inferInstance, P, fun ω => Y₀ ω.2, fun t ω => B t ω.1,
    inferInstance, ⟨hα, Ω₁ × ((Ω₁ × Ω₁) × Ω₂), inferInstance, P, fun ω => X ω.2.2,
      fun t ω => A₀ t ω.2, inferInstance, nv_freeGFF hXm hX, ?_, ?_, rfl⟩,
    nv_isBrownianReal measurePreserving_fst hB, nv_indepFun_prod (pathOf B) Y₀⟩
  · refine ⟨fun t ω => B t ω.2.1.1, fun t ω => B t ω.2.1.2, nv_isBrownianReal h1 hB,
      nv_isBrownianReal h2 hB, ?_, fun ω t => rfl⟩
    exact nv_indepFun_snd (nv_indepFun_fst (nv_indepFun_prod (pathOf B) (pathOf B)))
  · exact nv_indepFun_snd (nv_indepFun_prod (μ := P₁.prod P₁) (ν := P₂)
      (fun (ω : Ω₁ × Ω₁) (t : ℝ) =>
        wedgePath α (Qc γ) (fun s => B s ω.1) (fun s => B s ω.2) t)
      (fun ω : Ω₂ => X ω)).symm
