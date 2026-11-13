import LatticeProb.LQG.MatingOfTreesCouplingArea
import LatticeProb.LQG.MatingOfTreesCouplingBoundaryLength
import LatticeProb.LQG.AreaCurveMassMeasurable

/-!
# The parametrization by `γ`-LQG area depends only on the law of the coupling data

The `areaParam` clause of a mating-of-trees coupling says that, almost surely, the curve is `η_L`
run with an order isomorphism of `ℝ` fixing `0`, and every vague limit of the dyadic `γ`-LQG area
approximations of the cone field gives the image of `[s, t]` mass `t - s`. The first part was
transferred to random elements with the law of the coupling data in
`IsCouplingData.ae_exists_orderIso_η_of_map_eq`. This file transfers the second part.

The mass statement is not a measurable property of the data as it stands (it quantifies over all
measures). Once a vague limit exists, it is equivalent to the countable mass condition
`LatticeProb.VagueLimit.CurveMassCondition`, which is measurable in the field and the curve
(`LatticeProb.LQG.measurableSet_curveMassCondition_lqgAreaApprox_comp`); the converse implication
needs no existence. So the mass statement passes from the coupling to any random element with the
same law of the data, provided that a vague limit exists almost surely for the coupling.

* `ae_curveMass_of_map_eq`: the general transfer through the law;
* `IsCouplingData.ae_radGood₀`: the `0`-cone Brownian motions lie in `radGood γ 0` almost surely;
* `IsCouplingData.areaParam_of_map_eq_of_ae_exists`,
  `IsCouplingData.areaParam₀_of_map_eq_of_ae_exists`: the two clauses for a random element with the
  law of the coupling data, given the almost sure existence of a vague limit for the coupling.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

open CouplingData LatticeProb.VagueLimit

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ}

/-- **Transfer of the mass parametrization through the law.** Let `V`, `V'` be measurable random
elements of a measurable space `𝒱` with the same law. Let `g v` be a field that agrees, on a
measurable set `G` containing `V` almost surely, with a measurable field `F v`, and let `c v` be a
measurable continuous curve. If almost surely the dyadic `γ`-LQG area approximations of `g (V ω)`
have a vague limit and every vague limit gives `c (V ω) ([s, t])` mass `t - s`, then almost surely
every vague limit of the approximations of `g (V' ω)` gives `c (V' ω) ([s, t])` mass `t - s`. -/
theorem ae_curveMass_of_map_eq {𝒱 : Type*} [MeasurableSpace 𝒱] {V : Ω → 𝒱} {V' : Ω' → 𝒱}
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    {F g : 𝒱 → LQGMetric.DistC} (hF : Measurable F) {c : 𝒱 → C(ℝ, ℂ)} (hc : Measurable c)
    {G : Set 𝒱} (hG : MeasurableSet G) (hgF : ∀ v ∈ G, g v = F v) (hGae : ∀ᵐ ω ∂P, V ω ∈ G)
    (hex : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimit (CellScaling.lqgAreaApprox γ (g (V ω))) μ)
    (hmass : ∀ᵐ ω ∂P, ∀ μ : Measure ℂ, IsVagueLimit (CellScaling.lqgAreaApprox γ (g (V ω))) μ →
      ∀ s t : ℝ, s ≤ t → μ (c (V ω) '' Icc s t) = ENNReal.ofReal (t - s)) :
    ∀ᵐ ω ∂P', ∀ μ : Measure ℂ, IsVagueLimit (CellScaling.lqgAreaApprox γ (g (V' ω))) μ →
      ∀ s t : ℝ, s ≤ t → μ (c (V' ω) '' Icc s t) = ENNReal.ofReal (t - s) := by
  have hM : MeasurableSet
      (G ∩ {v | CurveMassCondition (CellScaling.lqgAreaApprox γ (F v)) (c v)}) :=
    hG.inter (LatticeProb.LQG.measurableSet_curveMassCondition_lqgAreaApprox_comp γ hF hc)
  have hP : ∀ᵐ ω ∂P,
      V ω ∈ G ∩ {v | CurveMassCondition (CellScaling.lqgAreaApprox γ (F v)) (c v)} := by
    filter_upwards [hGae, hex, hmass] with ω hGω hexω hmassω
    refine ⟨hGω, ?_⟩
    have h := (forall_isVagueLimit_measure_image_Icc_iff (c (V ω)).continuous hexω).1 hmassω
    rw [hgF _ hGω] at h
    exact h
  filter_upwards [ae_comp_of_map_eq hV hV' hlaw hM hP] with ω hω μ hμ s t hst
  rw [hgF _ hω.1] at hμ
  exact IsVagueLimit.measure_image_Icc_of_curveMassCondition (c (V' ω)).continuous hμ hω.2 hst

/-- On `radGood γ α` the circle-average embedding of the `α`-quantum cone built from a pair of
paths is the field with the lateral part of `X` and the radial path `radMap γ α`. -/
theorem coneField_coneRadial_eq_fieldOf_radMap {α : ℝ} (X : Field)
    {p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)} (hp : p ∈ ConeScaling.radGood γ α) :
    coneField X (coneRadial γ α p.1 p.2) =
      ConeScaling.fieldOf (CellScaling.lateralPart X) (ConeScaling.radMap γ α p) := by
  unfold coneField ConeScaling.fieldOf
  congr 2
  funext z
  simp only [ConeScaling.radialOf, ConeScaling.radMap_apply, hp, ↓reduceIte]
  rfl

/-- For `0 < γ < 2` the `0`-cone Brownian motions of a coupling almost surely lie in
`radGood γ 0`: both start at `0` and the drifted path `B₀'_t + Q t` has a bounded zero set. -/
theorem IsCouplingData.ae_radGood₀ {V : Ω → CouplingData} (hC : IsCouplingData γ P V)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ((V ω).B₀, (V ω).B₀') ∈ ConeScaling.radGood γ 0 := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have hQ : 0 < CellScaling.lqgQ γ - 0 := by
    have := CellScaling.lqgQ_sub_pos hγ hγ2
    linarith
  filter_upwards [hCP.bm_B₀.eval_zero_ae_eq_zero, hCP.bm_B₀'.eval_zero_ae_eq_zero,
    CellScaling.ae_goodDrift (γ := γ) (α := 0) hCP.bm_B₀' hQ] with ω h1 h2 hdrift
  exact ⟨h1, h2, hdrift.bddAbove_zeroSet⟩

variable {V : Ω → CouplingData} {V' : Ω' → CouplingData}

/-- **The `areaParam` clause depends only on the law of the data**, given that the area
approximations of the `γ`-quantum cone field of the coupling have a vague limit almost surely. -/
theorem IsCouplingData.areaParam_of_map_eq_of_ae_exists (hC : IsCouplingData γ P V)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V)
    (hex : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X (coneRadial γ γ (V ω).B (V ω).B')))
      μ) :
    ∀ᵐ ω ∂P', (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, (V' ω).η t = (V' ω).ηL (φ t)) ∧
      ∀ μ : Measure ℂ,
        IsVagueLimitC (lqgAreaApprox γ (coneField (V' ω).X (coneRadial γ γ (V' ω).B (V' ω).B'))) μ →
          ∀ s t : ℝ, s ≤ t → μ ((V' ω).η '' Icc s t) = ENNReal.ofReal (t - s) := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have hG : MeasurableSet {v : CouplingData | (v.B, v.B') ∈ ConeScaling.radGood γ γ} :=
    (ConeScaling.measurableSet_radGood γ γ).preimage (measurable_B.prodMk measurable_B')
  have hmass := ae_curveMass_of_map_eq (γ := γ) hV hV' hlaw
    (F := fun v => (coneTriple γ v).1)
    (g := fun v => coneField v.X (coneRadial γ γ v.B v.B'))
    (measurable_fst.comp (measurable_coneTriple γ)) measurable_η hG
    (fun v hv => (coneTriple_fst_of_mem hv).symm) (hC.ae_radGood hγ hγ2) hex
    (hCP.areaParam.mono fun ω h => h.2)
  exact (hC.ae_exists_orderIso_η_of_map_eq hV hV' hlaw).and hmass

/-- **The `areaParam₀` clause depends only on the law of the data**, given that the area
approximations of the `0`-quantum cone field of the coupling have a vague limit almost surely. -/
theorem IsCouplingData.areaParam₀_of_map_eq_of_ae_exists (hC : IsCouplingData γ P V)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V)
    (hex : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC
      (lqgAreaApprox γ (coneField (V ω).X₀ (coneRadial γ 0 (V ω).B₀ (V ω).B₀')))
      μ) :
    ∀ᵐ ω ∂P', (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ ∀ t, (V' ω).η₀ t = (V' ω).ηL (φ t)) ∧
      ∀ μ : Measure ℂ,
        IsVagueLimitC
          (lqgAreaApprox γ (coneField (V' ω).X₀ (coneRadial γ 0 (V' ω).B₀ (V' ω).B₀'))) μ →
          ∀ s t : ℝ, s ≤ t → μ ((V' ω).η₀ '' Icc s t) = ENNReal.ofReal (t - s) := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  have hG : MeasurableSet {v : CouplingData | (v.B₀, v.B₀') ∈ ConeScaling.radGood γ 0} :=
    (ConeScaling.measurableSet_radGood γ 0).preimage (measurable_B₀.prodMk measurable_B₀')
  have hF : Measurable fun v : CouplingData =>
      ConeScaling.fieldOf (CellScaling.lateralPart v.X₀) (ConeScaling.radMap γ 0 (v.B₀, v.B₀')) :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_X₀).prodMk
        ((ConeScaling.measurable_radMap γ 0).comp (measurable_B₀.prodMk measurable_B₀')))
  have hmass := ae_curveMass_of_map_eq (γ := γ) hV hV' hlaw
    (g := fun v => coneField v.X₀ (coneRadial γ 0 v.B₀ v.B₀')) hF measurable_η₀ hG
    (fun v hv => coneField_coneRadial_eq_fieldOf_radMap v.X₀ hv) (hC.ae_radGood₀ hγ hγ2) hex
    (hCP.areaParam₀.mono fun ω h => h.2)
  exact (hC.ae_exists_orderIso_η₀_of_map_eq hV hV' hlaw).and hmass

end MatedCRT

end MatedCRTHarmonic
