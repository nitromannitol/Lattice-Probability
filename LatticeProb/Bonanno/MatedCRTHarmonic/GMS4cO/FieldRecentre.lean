/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.FieldRecentre at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.IGRecentre
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ZeroIG

/-!
# The field side of the recentring in [18] Lemma 4.9, for the 0-quantum cone

Source: [18] ("By Lemma A.2 … the conditional law of
`(h, h^IG)|_{B_{ε^{q−4ζ}}(z)}` given `{h_{ε^{q−4ζ}}(z) = a₁, …}` is absolutely continuous with respect to the law of
The restriction … of a pair `(h^{a₁}, …)` of independent whole-plane GFFs normalized to have circle averages `a₁`
… If we compose `(h^{a₁}, …)` with an affine transformation which takes `𝔻` to `B_{ε^{q−4ζ}}(z)` and subtract
`(a₁, a₂)`, we obtain a new pair of fields with the same law as `(h, h^IG)|_𝔻`"), and ("the `h|_𝔻`
agrees in law with the corresponding restriction of the circle-average embedding of a 0-quantum cone").

For the bundle's 0-cone field `h₀ = coneField X₀ (coneRadial γ 0 B₀ B₀')`, `B̄_r(z) ⊆ 𝔻` and `W ⊆ 𝔻`:

`law(h₀,r(z), (h₀(z + r ·) − h₀,r(z))|_W) = law(h₀,r(z)) ⊗ law(h₀|_W)`
(`L43O.map_circleAvg_restrict_affField_zeroCone`).

The proof uses the identification of `h₀|_𝔻` with a normalized whole-plane GFF `Xt|_𝔻`
(`GMS4.prop48_exists_zeroCone_disk_wholePlaneGFF`), [18] Lemma A.2 in its exact-independence form
(`GMSAppA.lemmaA2_indepFun`, Radon–Nikodym derivative `≡ 1`), and the invariance of the normalized whole-plane GFF
under recentred affine maps.

`L43O.indepFun_prod_prod` rearranges independence of two pairs into independence of the conditioning pair from the
local pair; `L43O.map_recentred_local_zeroCone` assembles the joint law used by the freezing argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

/-! ## Determination by the restriction to the unit disk -/

/-- Two fields with the same restriction to `𝔻` have the same circle average over every circle `∂B_r(z)` with
`B̄_r(z) ⊆ 𝔻`. -/
theorem circleAvg_eq_of_restrict_eq {x y : DistC}
    (hxy : restrictTo (ballO 0 1) x = restrictTo (ballO 0 1) y) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) : circleAvg x r z = circleAvg y r z := by
  obtain ⟨Ψ, -, hΨ⟩ := LQGMetric.DG.r18_circ_factor (ballO (0 : ℂ) 1) hr
    (sphere_subset_closedBall.trans hzr)
  rw [hΨ x, hΨ y, hxy]

/-- Two fields with the same restriction to `𝔻` have the same restriction to any `W ⊆ 𝔻`. -/
theorem restrictTo_eq_of_restrict_eq {x y : DistC}
    (hxy : restrictTo (ballO 0 1) x = restrictTo (ballO 0 1) y) {W : TopologicalSpace.Opens ℂ}
    (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1) : restrictTo W x = restrictTo W y := by
  have hle : W ≤ ballO (0 : ℂ) 1 := hW
  rw [restrictTo_eq_resDist hle, restrictTo_eq_resDist hle, hxy]

/-- Two fields with the same restriction to `𝔻` have the same recentred affine pullback on `W ⊆ 𝔻`, for
`B̄_r(z) ⊆ 𝔻`. -/
theorem restrictTo_affField_eq_of_restrict_eq {x y : DistC}
    (hxy : restrictTo (ballO 0 1) x = restrictTo (ballO 0 1) y) {W : TopologicalSpace.Opens ℂ}
    (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) :
    restrictTo W (IGLaw.affField r 0 z x) = restrictTo W (IGLaw.affField r 0 z y) := by
  rw [restrictTo_affField_eq hW hr z x, restrictTo_affField_eq hW hr z y,
    circleAvg_eq_of_restrict_eq hxy hr hzr]
  congr 2
  have hle : ballO z r ≤ ballO (0 : ℂ) 1 := ball_subset_closedBall.trans hzr
  rw [restrictTo_eq_resDist hle, restrictTo_eq_resDist hle (addConst y _),
    GMSAppA.restrictTo_addConst_eq_addConstOn, GMSAppA.restrictTo_addConst_eq_addConstOn, hxy]

/-! ## The normalized whole-plane GFF -/

/-- The recentred affine pullback of a normalized whole-plane GFF is a normalized whole-plane GFF. -/
theorem isNormalizedWPGFF_affField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsNormalizedWPGFF (fun ω => IGLaw.affField r 0 z (h ω)) P := by
  have hcm : Measurable fun ω => circleAvg (h ω) r z :=
    (measurable_circleAvg_left r z).comp hh.1.measurable
  have hh'gff : IsWholePlaneGFF (fun ω => MoTPort.rotateField 0 (affineComp r z (h ω))) P :=
    IGLaw.IsWholePlaneGFF.rotateField (hh.1.affineComp hr z) 0
  refine ⟨hh'gff.addConst hcm.neg, ?_⟩
  filter_upwards [IGLaw.ae_circleAvg_affineRotate_all hh.1 0 hr z,
    CircleAvg.ae_circleAvg_addConst hh'gff 0 one_pos] with ω hω hadd1
  show circleAvg (addConst (MoTPort.rotateField 0 (affineComp r z (h ω)))
    (-(circleAvg (h ω) r z))) 1 0 = 0
  rw [hadd1, hω 1 one_pos 0]
  simp

/-- **Field side for a normalized whole-plane GFF.** For `B̄_r(z) ⊆ B̄_1(0)` and `W ⊆ 𝔻`,
`law(h_r(z), (h(z + r·) − h_r(z))|_W) = law(h_r(z)) ⊗ law(h|_W)`. -/
theorem map_circleAvg_restrict_affField_wp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {W : TopologicalSpace.Opens ℂ} (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ closedBall (0 : ℂ) 1) :
    P.map (fun ω => (circleAvg (h ω) r z, restrictTo W (IGLaw.affField r 0 z (h ω)))) =
      (P.map fun ω => circleAvg (h ω) r z).prod (P.map fun ω => restrictTo W (h ω)) := by
  have hhm : Measurable h := hh.1.measurable
  have ham : Measurable fun ω => circleAvg (h ω) r z := (measurable_circleAvg_left r z).comp hhm
  have hYm : Measurable fun ω => restrictTo (ballO z r) (addConst (h ω) (-circleAvg (h ω) r z)) :=
    (measurable_restrictTo _).comp (hh.1.addConst ham.neg).measurable
  have hind := GMSAppA.lemmaA2_indepFun hh hr hzr
  have hΘm := measurable_restrictTo_affField_factor (W := W) hr z
  have hind' : IndepFun (fun ω => circleAvg (h ω) r z)
      (fun ω => restrictTo W (IGLaw.affField r 0 z (h ω))) P := by
    refine (hind.comp measurable_id hΘm).congr (ae_of_all _ fun _ => rfl)
      (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, restrictTo_affField_eq hW hr z (h ω)]
  have hAm : Measurable fun ω => restrictTo W (IGLaw.affField r 0 z (h ω)) :=
    (measurable_restrictTo W).comp ((IGLaw.measurable_affField r 0 z).comp hhm)
  rw [(indepFun_iff_map_prod_eq_prod_map_map ham.aemeasurable hAm.aemeasurable).1 hind']
  congr 1
  have hlaw := CircleAvg.map_eq_of_isNormalizedWPGFF (isNormalizedWPGFF_affField hh hr z) hh
  calc P.map (fun ω => restrictTo W (IGLaw.affField r 0 z (h ω)))
      = (P.map fun ω => IGLaw.affField r 0 z (h ω)).map (restrictTo W) :=
        (Measure.map_map (f := fun ω => IGLaw.affField r 0 z (h ω)) (measurable_restrictTo W)
          ((IGLaw.measurable_affField r 0 z).comp hhm)).symm
    _ = (P.map h).map (restrictTo W) := by rw [hlaw]
    _ = P.map (fun ω => restrictTo W (h ω)) :=
        Measure.map_map (measurable_restrictTo W) hhm

/-! ## The 0-quantum cone -/

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The bundle's 0-quantum cone field. -/
abbrev zeroConeField (γ : ℝ) (X₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Field :=
  coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))

/-- **Field side of the Lemma 4.9 recentring for the 0-cone.** For `B̄_r(z) ⊆ 𝔻` and `W ⊆ 𝔻`,
`law(h₀,r(z), (h₀(z + r ·) − h₀,r(z))|_W) = law(h₀,r(z)) ⊗ law(h₀|_W)`. -/
theorem map_circleAvg_restrict_affField_zeroCone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {W : TopologicalSpace.Opens ℂ} (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) :
    P.map (fun ω => (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z,
        restrictTo W (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)))) =
      (P.map fun ω => circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z).prod
        (P.map fun ω => restrictTo W (zeroConeField γ X₀ B₀ B₀' ω)) := by
  have := D.isProbabilityMeasure
  obtain ⟨Xt, hXt, he⟩ := GMS4.prop48_exists_zeroCone_disk_wholePlaneGFF D hγ
  have hzr' : closedBall z r ⊆ closedBall (0 : ℂ) 1 := hzr.trans ball_subset_closedBall
  have e1 : (fun ω => (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z,
        restrictTo W (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)))) =ᵐ[P]
      fun ω => (circleAvg (Xt ω) r z, restrictTo W (IGLaw.affField r 0 z (Xt ω))) := by
    filter_upwards [he] with ω hω
    exact Prod.ext (circleAvg_eq_of_restrict_eq hω hr hzr)
      (restrictTo_affField_eq_of_restrict_eq hω hW hr hzr)
  have e2 : (fun ω => circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) =ᵐ[P]
      fun ω => circleAvg (Xt ω) r z := by
    filter_upwards [he] with ω hω
    exact circleAvg_eq_of_restrict_eq hω hr hzr
  have e3 : (fun ω => restrictTo W (zeroConeField γ X₀ B₀ B₀' ω)) =ᵐ[P]
      fun ω => restrictTo W (Xt ω) := by
    filter_upwards [he] with ω hω
    exact restrictTo_eq_of_restrict_eq hω hW
  rw [Measure.map_congr e1, Measure.map_congr e2, Measure.map_congr e3]
  exact map_circleAvg_restrict_affField_wp hXt hW hr hzr'

end ZeroCone

/-! ## Rearranging independence -/

/-- If `(A₁, L₁) ⟂ (A₂, L₂)`, `A₁ ⟂ L₁` and `A₂ ⟂ L₂`, then `(A₁, A₂) ⟂ (L₁, L₂)`. -/
theorem indepFun_prod_prod {Ω α₁ α₂ β₁ β₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace α₁]
    [MeasurableSpace α₂] [MeasurableSpace β₁] [MeasurableSpace β₂] {P : Measure Ω}
    [IsProbabilityMeasure P] {A₁ : Ω → α₁} {A₂ : Ω → α₂} {L₁ : Ω → β₁} {L₂ : Ω → β₂}
    (hA₁ : AEMeasurable A₁ P) (hA₂ : AEMeasurable A₂ P) (hL₁ : AEMeasurable L₁ P)
    (hL₂ : AEMeasurable L₂ P)
    (h12 : IndepFun (fun ω => (A₁ ω, L₁ ω)) (fun ω => (A₂ ω, L₂ ω)) P)
    (h1 : IndepFun A₁ L₁ P) (h2 : IndepFun A₂ L₂ P) :
    IndepFun (fun ω => (A₁ ω, A₂ ω)) (fun ω => (L₁ ω, L₂ ω)) P := by
  have hA : IndepFun A₁ A₂ P := h12.comp measurable_fst measurable_fst
  have hL : IndepFun L₁ L₂ P := h12.comp measurable_snd measurable_snd
  have hAA := (indepFun_iff_map_prod_eq_prod_map_map hA₁ hA₂).1 hA
  have hLL := (indepFun_iff_map_prod_eq_prod_map_map hL₁ hL₂).1 hL
  have h4 : AEMeasurable (fun ω => ((A₁ ω, A₂ ω), (L₁ ω, L₂ ω))) P :=
    (hA₁.prodMk hA₂).prodMk (hL₁.prodMk hL₂)
  refine (indepFun_iff_map_prod_eq_prod_map_map (hA₁.prodMk hA₂) (hL₁.prodMk hL₂)).2 ?_
  rw [hAA, hLL]
  refine (Measure.prod_eq_generateFrom generateFrom_prod generateFrom_prod isPiSystem_prod
    isPiSystem_prod ((P.map A₁).toFiniteSpanningSetsIn.prod (P.map A₂).toFiniteSpanningSetsIn)
    ((P.map L₁).toFiniteSpanningSetsIn.prod (P.map L₂).toFiniteSpanningSetsIn) ?_).symm
  rintro _ ⟨s₁, hs₁, s₂, hs₂, rfl⟩ _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
  have hs₁' : MeasurableSet s₁ := hs₁
  have hs₂' : MeasurableSet s₂ := hs₂
  have ht₁' : MeasurableSet t₁ := ht₁
  have ht₂' : MeasurableSet t₂ := ht₂
  have e1 : (fun ω => ((A₁ ω, A₂ ω), (L₁ ω, L₂ ω))) ⁻¹' ((s₁ ×ˢ s₂) ×ˢ (t₁ ×ˢ t₂)) =
      (fun ω => (A₁ ω, L₁ ω)) ⁻¹' (s₁ ×ˢ t₁) ∩ (fun ω => (A₂ ω, L₂ ω)) ⁻¹' (s₂ ×ˢ t₂) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    tauto
  have e4 : (fun ω => (A₁ ω, L₁ ω)) ⁻¹' (s₁ ×ˢ t₁) = A₁ ⁻¹' s₁ ∩ L₁ ⁻¹' t₁ := rfl
  have e5 : (fun ω => (A₂ ω, L₂ ω)) ⁻¹' (s₂ ×ˢ t₂) = A₂ ⁻¹' s₂ ∩ L₂ ⁻¹' t₂ := rfl
  rw [Measure.map_apply_of_aemeasurable h4 ((hs₁'.prod hs₂').prod (ht₁'.prod ht₂')), e1,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 h12) _ _ (hs₁'.prod ht₁') (hs₂'.prod ht₂'),
    e4, e5, (indepFun_iff_measure_inter_preimage_eq_mul.1 h1) _ _ hs₁' ht₁',
    (indepFun_iff_measure_inter_preimage_eq_mul.1 h2) _ _ hs₂' ht₂',
    Measure.prod_prod, Measure.prod_prod, Measure.map_apply_of_aemeasurable hA₁ hs₁',
    Measure.map_apply_of_aemeasurable hA₂ hs₂', Measure.map_apply_of_aemeasurable hL₁ ht₁',
    Measure.map_apply_of_aemeasurable hL₂ ht₂']
  ring

end MatedCRTHarmonic.L43O
