import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main

/-!
# Existence of the area limit for affinely transformed quantum cone fields

For a field `h` whose circle averages exist at every scale and whose mollified area measures
converge vaguely as the scale tends to `0` (`HasAreaLimitS γ h μ`), the dyadic `γ`-LQG area
approximations of the transformed field `h(r · + z) + Q log r + c` converge vaguely, to
`e^{γc} (w ↦ (w - z)/r)_* μ` (`isVagueLimitC_lqgAreaApprox_affine`). The argument is the one of
`MatedCRTHarmonic.LQGCoord.lqgArea_affine_eq` (adapted from Leonardo Bonanno's
lean-formalizations), which records only the value of `lqgArea`; here the existence of the limit
is stated on its own, so that the transformed field lies in the set of fields on which `lqgArea`
is a genuine vague limit and not the junk value `0`.

For the `γ`-quantum cone `h = coneFieldOf γ X B B'` built from a whole-plane GFF `X` and Brownian
motions `B, B'` (Duplantier-Miller-Sheffield, Def. 4.10), almost surely, simultaneously for every
`R > 0` and `b > 0`, the area approximations of the rescaled field
`h_b = h(R ·) + Q log R - γ⁻¹ log b` (`coneRescaleField`) have a vague limit
(`ae_exists_isVagueLimitC_lqgAreaApprox_coneRescaleField`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LQGMetric MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord

/-- **Vague convergence of the area approximations of an affinely transformed field**: if `h` has
circle averages at every scale and area limit `μ`, then the dyadic `γ`-LQG area approximations of
`h(r · + z) + Q log r + c` converge vaguely to `e^{γc} (w ↦ (w - z)/r)_* μ`. -/
theorem isVagueLimitC_lqgAreaApprox_affine {γ : ℝ} (hγ : γ ≠ 0) {h : DistC} {μ : Measure ℂ}
    (h1 : HasScaleCircleAvgs h) (h2 : HasAreaLimitS γ h μ) {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) :
    IsVagueLimitC (lqgAreaApprox γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)))
      (ENNReal.ofReal (Real.exp (γ * c)) • μ.map (affT hr z).symm) := by
  set h' := addConst (affineComp r z h) (lqgQ γ * Real.log r + c)
  set T := affT hr z
  set e := ENNReal.ofReal (Real.exp (γ * c))
  have hmapk : ∀ k, lqgAreaApprox γ h' k = (e • areaS γ h (r * dyadicScale k)).map T.symm := by
    intro k
    rw [← map_lqgAreaApprox_affine hγ h1 hr z c k,
      Measure.map_map T.symm.measurable T.measurable, T.symm_comp_self, Measure.map_id]
  constructor
  · intro K hK
    rw [Measure.smul_apply, smul_eq_mul, MeasurableEquiv.map_apply,
      ← MeasurableEquiv.image_eq_preimage_symm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h2.1 _ (hK.image (continuous_affT hr z)))
  · intro f hf hfc
    have hg : Continuous (f ∘ T.symm) := hf.comp (continuous_affT_symm hr z)
    have hgc : HasCompactSupport (f ∘ T.symm) := by
      have := hfc.comp_homeomorph ((Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans
        (Homeomorph.addRight z)).symm
      simpa only [T, affT, DG.affineEquivC, Homeomorph.toMeasurableEquiv_symm_coe] using this
    have hlim := ((h2.2 _ hg hgc).comp (tendsto_mul_dyadicScale hr)).const_smul e.toReal
    have hval : ∀ k, ∫ w, f w ∂lqgAreaApprox γ h' k =
        e.toReal • ∫ w, (f ∘ T.symm) w ∂areaS γ h (r * dyadicScale k) := by
      intro k
      rw [hmapk k, integral_map_equiv, integral_smul_measure]
      rfl
    have hval' : ∫ w, f w ∂(e • μ.map T.symm) = e.toReal • ∫ w, (f ∘ T.symm) w ∂μ := by
      rw [integral_smul_measure, integral_map_equiv]
      rfl
    rw [hval']
    exact hlim.congr fun k => (hval k).symm

/-- **The rescaled quantum cone field has an area limit**: for the `γ`-quantum cone
`h = coneFieldOf γ X B B'` of a whole-plane GFF `X` and Brownian motions `B, B'`, almost surely,
for every `R > 0` and every `b`, the dyadic `γ`-LQG area approximations of
`h_b = h(R ·) + Q log R - γ⁻¹ log b` converge vaguely. -/
theorem ae_exists_isVagueLimitC_lqgAreaApprox_coneRescaleField {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ b₀ : ℝ, ∃ μ : Measure ℂ,
      IsVagueLimitC (lqgAreaApprox γ
        (coneRescaleField γ R b₀ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))) μ := by
  have hαQ := lt_lqgQ hγ hγ2
  filter_upwards [ae_radialGood hX hB hB' hαQ, ae_hasScaleCircleAvgs_wp hX,
    ae_hasAreaLimitS_wp hX hγ hγ2,
    ae_tight_wp hX hγ hγ2 (le_max_left _ _) (coneExp_lt hγ hαQ)] with ω hr hs ha ht
  have hc := coneGood_of hαQ hr hs ha ht
  intro R hR b₀
  rw [coneRescaleField, sub_eq_add_neg, coneFieldOf, coneField_eq_cone]
  exact ⟨_, isVagueLimitC_lqgAreaApprox_affine hγ.ne'
    (hasScaleCircleAvgs_cone hs hc.li₁ hc.li₂ hc.cont₁ hc.cont₂) (hasAreaLimitS_cone hγ hc) hR 0 _⟩

end LatticeProb.LQG
