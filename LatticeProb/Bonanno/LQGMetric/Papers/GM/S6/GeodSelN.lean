/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.GeodSelN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Blueprint.MQGeodesic
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq

/-!
# A measurable geodesic selector invariant under additive constants (D79 (4))

GM = Gwynne–Miller, arXiv:1905.00383v3. GM's `P^{𝕫,𝕨}` is "the (a.s. unique) `D_h`-geodesic"
(MQ Theorem 1.2, `Blueprint.MQThm1_2Weak`); it is unchanged by adding a constant to `h`
(`D_{h+c} = e^{ξc} D_h`, Weyl scaling). The selector of decision D79 (4), used by Prop 6.1 Step 1:

* `normPsi g = g − ⟨g, ψ₁⟩` with `ψ₁ = bumpTest 0 0` (`∫ ψ₁ = 1`): deterministic, measurable,
  `normPsi (g + c) = normPsi g`;
* `geodSelN D hΓ a b g = Γ a b (normPsi g)` with `Γ a b` a Lusin–Souslin selector
  (`exists_measurable_geodSel`, D31 rule 3) for the law `μψ` of `normPsi h` (the same for every
  whole-plane GFF `h`, by law uniqueness of the normalized field `normGFFLaw_eq`);
* `geodSelN_ae`: for every whole-plane GFF and `a ≠ b`, a.s. `geodSelN … a b (h ω)` is a
  `D_h`-geodesic (Weyl scaling: geodesics of `e^{ξc}D` and `D` coincide).

Own elementary arguments around the cited inputs (MQ Thm 1.2, Lusin–Souslin).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace LQGMetric.GM
open GFFInv Blueprint

/-- the mass-one test function `ψ₁` -/
def psiOne : TestC := bumpTest 0 0

/-- `g − ⟨g, ψ₁⟩`, the field normalized by `ψ₁` -/
def normPsi (g : DistC) : DistC := addConst g (-(g psiOne))

theorem normPsi_addConst (g : DistC) (c : ℝ) : normPsi (addConst g c) = normPsi g := by
  have h1 : ∫ y, psiOne y = 1 := GFFLaw.integral_bumpTest 0 0
  ext φ
  simp only [normPsi, addConst_apply, h1]
  ring

theorem measurable_normPsi : Measurable normPsi := by
  refine measurable_distC_iff.2 fun φ => ?_
  simp only [normPsi, addConst_apply]
  exact (measurable_pair φ).add (((measurable_pair psiOne).neg).const_mul _)

/-- the law of `normPsi h`, for any whole-plane GFF `h` -/
def lawPsi : Measure DistC := normGFFLaw.map normPsi

theorem isWholePlaneGFF_normPsi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsWholePlaneGFF (fun ω => normPsi (h ω)) P :=
  hh.addConst ((measurable_pair psiOne).comp hh.measurable).neg

theorem map_normPsi_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : P.map (fun ω => normPsi (h ω)) = lawPsi := by
  have hN : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) with hh'def
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh.addConst hN, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    simp only [h', hω, add_neg_cancel]
  have e : (fun ω => normPsi (h ω)) = normPsi ∘ h' := by
    funext ω; simp only [Function.comp_apply, h', normPsi_addConst]
  rw [e, lawPsi, normGFFLaw_eq hh', Measure.map_map measurable_normPsi hh'.1.measurable]

/-- MQ Theorem 1.2 under `lawPsi`: a.s. a unique geodesic between fixed distinct points -/
theorem lawPsi_ae_unique (hMQ : MQThm1_2Weak) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {a b : ℂ} (hab : a ≠ b) : ∀ᵐ g ∂lawPsi, ∃! η, IsGeod01 (D g) a b η := by
  by_cases hex : ∃ μ : Measure DistC, IsProbabilityMeasure μ ∧ IsNormalizedWPGFF id μ
  · obtain ⟨μ, hμ, hμN⟩ := hex
    have hlaw : normGFFLaw = μ.map id := normGFFLaw_eq hμN
    rw [Measure.map_id] at hlaw
    have hψ := isWholePlaneGFF_normPsi hμN.1
    have hmap : lawPsi = μ.map (fun g => normPsi (id g)) := by
      rw [lawPsi, hlaw]; rfl
    have : IsProbabilityMeasure lawPsi := by
      rw [hmap]; exact (Measure.isProbabilityMeasure_map_iff hψ.measurable.aemeasurable).2 hμ
    have hid : IsWholePlaneGFF id lawPsi := by rw [hmap]; exact isWholePlaneGFF_id_map hψ
    filter_upwards [hMQ γ hγ hγ2 D c hD lawPsi id hid a b hab] with g hg
    exact hg
  · have h0 : normGFFLaw = 0 := by classical exact dif_neg hex
    simp [lawPsi, h0]

/-- `IsGeod01` is unchanged when the metric is multiplied by a constant `κ > 0` -/
theorem isGeod01_of_dist_eq_mul {D₁ D₂ : ContMetric} {κ : ℝ} (hκ : 0 < κ)
    (hd : ∀ u v : ℂ, D₂.1 (u, v) = κ * D₁.1 (u, v)) {a b : ℂ} {η : C(unitInterval, ℂ)}
    (h : IsGeod01 D₂ a b η) : IsGeod01 D₁ a b η := by
  refine ⟨h.1, h.2.1, fun s t => ?_⟩
  have := h.2.2 s t
  rw [hd, hd] at this
  have : κ * (D₁.1 (η s, η t) - |(t : ℝ) - s| * D₁.1 (a, b)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hκ.ne'
  · linarith

/-- the selector `g ↦ Γ a b (normPsi g)` (`Γ a b` for `a ≠ b`; the constant path at `a = b`) -/
def geodSelN (Γ : ∀ a b : ℂ, a ≠ b → DistC → C(unitInterval, ℂ)) (a b : ℂ) (g : DistC) :
    C(unitInterval, ℂ) :=
  if hab : a = b then ContinuousMap.const _ a else Γ a b hab (normPsi g)

theorem geodSelN_addConst (Γ : ∀ a b : ℂ, a ≠ b → DistC → C(unitInterval, ℂ)) (a b : ℂ)
    (g : DistC) (c : ℝ) : geodSelN Γ a b (addConst g c) = geodSelN Γ a b g := by
  unfold geodSelN; rw [normPsi_addConst]

theorem measurable_geodSelN {Γ : ∀ a b : ℂ, a ≠ b → DistC → C(unitInterval, ℂ)}
    (hΓ : ∀ a b (hab : a ≠ b), Measurable (Γ a b hab)) (a b : ℂ) :
    Measurable (geodSelN Γ a b) := by
  unfold geodSelN
  by_cases hab : a = b
  · simp only [hab, dite_true]; exact measurable_const
  · simp only [hab, dite_false]; exact (hΓ a b hab).comp measurable_normPsi

/-- **the selector exists** (D79 (4)): measurable, invariant under additive constants, and a.s. a
`D_h`-geodesic for every whole-plane GFF and every pair `a ≠ b` -/
theorem exists_geodSelN (hMQ : MQThm1_2Weak) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) :
    ∃ sel : ℂ → ℂ → DistC → C(unitInterval, ℂ),
      (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) ∧
      (∀ a b : ℂ, Measurable (sel a b)) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ a b : ℂ, a ≠ b → ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω)) := by
  have hsel : ∀ a b : ℂ, a ≠ b → ∃ Γ : DistC → C(unitInterval, ℂ), Measurable Γ ∧
      ∀ᵐ g ∂lawPsi, IsGeod01 (D g) a b (Γ g) := fun a b hab =>
    exists_measurable_geodSel D hD.measurable a b lawPsi
      (lawPsi_ae_unique hMQ hγ hγ2 hD hab)
  choose Γ hΓm hΓ using hsel
  refine ⟨geodSelN Γ, geodSelN_addConst Γ, measurable_geodSelN hΓm, ?_⟩
  intro Ω _ P _ h hh a b hab
  have hψ := isWholePlaneGFF_normPsi hh
  have h1 : ∀ᵐ ω ∂P, IsGeod01 (D (normPsi (h ω))) a b (Γ a b hab (normPsi (h ω))) := by
    have := hΓ a b hab
    rw [← map_normPsi_eq hh] at this
    exact ae_of_ae_map hψ.measurable.aemeasurable this
  filter_upwards [h1, hD.ae_dist_addConst (isGFFPlusCont_of_isWholePlaneGFF hh)] with ω h1 hw
  have hsel : geodSelN Γ a b (h ω) = Γ a b hab (normPsi (h ω)) := by
    simp only [geodSelN, hab, dite_false]
  rw [hsel]
  exact isGeod01_of_dist_eq_mul (Real.exp_pos _) (fun u v => hw _ u v) h1

end LQGMetric.GM
