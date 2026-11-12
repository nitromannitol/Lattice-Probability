import LatticeProb.LQG.RadialLateralIndep
import LatticeProb.Prob.ProbabilityIntegralTransform

/-!
# A uniform variable from the radial part of the whole-plane Gaussian free field

Let `X` be a whole-plane GFF. For the rotation-invariant test function `ρ` obtained by
symmetrizing the unit mollifier, the pairing `X(−Δρ/(2π))` is a centred Gaussian with variance the
Dirichlet energy `(ρ, ρ)_∇ = (2π)⁻¹ ∫ |∇ρ|² > 0` (Green's identity), and it is independent of the
lateral part of `X` (radial–lateral independence, Duplantier–Miller–Sheffield, Lemma 4.9).
Applying its distribution function gives a uniform random variable on `[0, 1]` which is a
measurable function of `X`, independent of the lateral part of `X`, and, together with the lateral
part, independent of any random element independent of `X`.

## Main results

* `LatticeProb.LQG.gradEnergy_pos_of_integral_ne_zero`: a test function with nonzero integral has
  positive Dirichlet energy.
* `LatticeProb.LQG.radialBump`, `isRotInv_radialBump`, `integral_radialBump`.
* `LatticeProb.LQG.radialUniform`, `measurable_radialUniform`.
* `LatticeProb.LQG.IsWholePlaneGFF.map_radialUniform`: `radialUniform X` is uniform on `[0, 1]`.
* `LatticeProb.LQG.IsWholePlaneGFF.indepFun_radialUniform_lateralPart`.
* `LatticeProb.LQG.indepFun_prodMk_right_of_indepFun_prodMk`: if `A ⫫ B` and `(A, B) ⫫ C` then
  `A ⫫ (B, C)`.
* `LatticeProb.LQG.IsWholePlaneGFF.indepFun_radialUniform_lateralPart_prodMk`: for `W`
  independent of `X`, `radialUniform X` is independent of `(lateralPart X, W)`.
-/

open MeasureTheory ProbabilityTheory LQGMetric MatedCRTHarmonic.GMCFacts
  MatedCRTHarmonic.ConeScaling
open scoped NNReal

namespace LatticeProb.LQG

/-- A test function with nonzero integral has positive Dirichlet energy `(2π)⁻¹ ∫ |∇φ|²`. -/
theorem gradEnergy_pos_of_integral_ne_zero (φ : TestC) (hφ : ∫ z, φ z ≠ 0) :
    0 < gradEnergy φ := by
  have hd : Continuous (fderiv ℝ φ) := φ.contDiff.continuous_fderiv (by simp)
  have hg : Continuous fun z => ‖fderiv ℝ φ z‖ ^ 2 := (continuous_norm.comp hd).pow 2
  have hgs : HasCompactSupport fun z => ‖fderiv ℝ φ z‖ ^ 2 :=
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ)).comp_left (g := fun v => ‖v‖ ^ 2) (by simp)
  have hint : Integrable fun z => ‖fderiv ℝ φ z‖ ^ 2 := hg.integrable_of_hasCompactSupport hgs
  unfold gradEnergy
  refine mul_pos (by positivity) ?_
  refine lt_of_le_of_ne (integral_nonneg fun z => by positivity) (Ne.symm fun h0 => hφ ?_)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint).1 h0
  have hzero : ∀ z, fderiv ℝ φ z = 0 := by
    intro z
    have := congrFun ((hg.ae_eq_iff_eq volume continuous_zero).1 hae) z
    simp only [Pi.zero_apply] at this
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  have hconst : ∀ z, φ z = φ 0 := fun z =>
    is_const_of_fderiv_eq_zero (φ.contDiff.differentiable (by simp)) hzero z 0
  obtain ⟨z₀, hz₀⟩ : ∃ z, z ∉ tsupport φ := by
    by_contra h
    push Not at h
    have hc := φ.hasCompactSupport
    rw [HasCompactSupport, Set.eq_univ_of_forall h] at hc
    exact noncompact_univ ℂ hc
  have h0' : ∀ z, φ z = 0 := fun z => by
    rw [hconst z, ← hconst z₀]
    exact image_eq_zero_of_notMem_tsupport hz₀
  simp only [h0', integral_zero]

/-- The rotational symmetrization of the unit mollifier: a rotation-invariant test function with
integral one. -/
noncomputable def radialBump : TestC := symmTest (bumpTest 0 0)

theorem isRotInv_radialBump : IsRotInv radialBump := fun α w => by
  rw [radialBump, isRadialTest_symmTest _ (Complex.exp (α * Complex.I) * w),
    isRadialTest_symmTest _ w, norm_mul, norm_exp_ofReal_mul_I', one_mul]

theorem integral_radialBump : ∫ z, radialBump z = 1 := by
  rw [radialBump, integral_symmTest]
  exact GFFLaw.integral_bumpTest 0 0

theorem gradEnergy_radialBump_pos : 0 < gradEnergy radialBump :=
  gradEnergy_pos_of_integral_ne_zero _ (by rw [integral_radialBump]; exact one_ne_zero)

/-- A uniform variable read off the radial part of a field: the standard distribution function
of the centred Gaussian of variance `(ρ, ρ)_∇` evaluated at the pairing `h(−Δρ/(2π))`, `ρ` the
radial bump. -/
noncomputable def radialUniform (h : DistC) : unitInterval :=
  cdfUnit (gaussianReal 0 (gradEnergy radialBump).toNNReal) (h (cmTest radialBump))

theorem measurable_radialUniform : Measurable radialUniform :=
  (measurable_cdfUnit _).comp ((measurable_pi_apply _).comp measurable_evDist)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- For a whole-plane GFF `X`, `radialUniform X` is uniformly distributed on `[0, 1]`. -/
theorem IsWholePlaneGFF.map_radialUniform (hX : IsWholePlaneGFF X P) :
    P.map (fun ω => radialUniform (X ω)) = volume := by
  have := hX.gaussian.isProbabilityMeasure
  set Y : Ω → ℝ := fun ω => X ω (cmTest radialBump) with hYdef
  have hYm : Measurable Y :=
    (measurable_pi_apply _).comp (measurable_evDist.comp hX.measurable)
  have hG : HasGaussianLaw Y P := hX.gaussian.hasGaussianLaw_eval (cmTest0 radialBump)
  have hmean : P[Y] = 0 := hX.centered (cmTest0 radialBump)
  have hvar : Var[Y; P] = gradEnergy radialBump := by
    rw [← covariance_self hYm.aemeasurable]
    exact (hX.covariance_eq (cmTest0 radialBump) (cmTest0 radialBump)).trans
      (logCov_cmTest_cmTest radialBump)
  have hlaw : P.map Y = gaussianReal 0 (gradEnergy radialBump).toNNReal := by
    rw [hG.map_eq_gaussianReal, hmean, hvar]
  exact map_cdfUnit_gaussianReal_comp hYm
    (Real.toNNReal_pos.2 gradEnergy_radialBump_pos).ne' hlaw

/-- For a whole-plane GFF `X`, `radialUniform X` is independent of the lateral part of `X`. -/
theorem IsWholePlaneGFF.indepFun_radialUniform_lateralPart (hX : IsWholePlaneGFF X P) :
    IndepFun (fun ω => radialUniform (X ω))
      (fun ω => MatedCRTHarmonic.CellScaling.lateralPart (X ω)) P :=
  (IsWholePlaneGFF.indepFun_cmTest_lateralPart hX (ι := Unit) (fun _ => radialBump)
    fun _ => isRotInv_radialBump).comp
    (φ := fun v : Unit → ℝ => cdfUnit (gaussianReal 0 (gradEnergy radialBump).toNNReal) (v ()))
    ((measurable_cdfUnit _).comp (measurable_pi_apply ())) measurable_id

/-- If `A` is independent of `B` and `(A, B)` is independent of `C`, then `A` is independent
of `(B, C)`. -/
theorem indepFun_prodMk_right_of_indepFun_prodMk {β γ δ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] [IsProbabilityMeasure P] {A : Ω → β} {B : Ω → γ}
    {C : Ω → δ} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hAB : IndepFun A B P) (hABC : IndepFun (fun ω => (A ω, B ω)) C P) :
    IndepFun A (fun ω => (B ω, C ω)) P := by
  have hBC : IndepFun B C P := hABC.comp measurable_snd measurable_id
  rw [indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable (hB.prodMk hC).aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map hB.aemeasurable hC.aemeasurable).1 hBC]
  have e1 := (indepFun_iff_map_prod_eq_prod_map_map (hA.prodMk hB).aemeasurable
    hC.aemeasurable).1 hABC
  have e2 := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable).1 hAB
  calc P.map (fun ω => (A ω, (B ω, C ω)))
      = (P.map (fun ω => ((A ω, B ω), C ω))).map MeasurableEquiv.prodAssoc := by
        rw [Measure.map_map (MeasurableEquiv.measurable _) ((hA.prodMk hB).prodMk hC)]
        rfl
    _ = (((P.map A).prod (P.map B)).prod (P.map C)).map MeasurableEquiv.prodAssoc := by
        rw [e1, e2]
    _ = (P.map A).prod ((P.map B).prod (P.map C)) := Measure.prodAssoc_prod

/-- For a whole-plane GFF `X` and a random element `W` independent of `X`, `radialUniform X` is
independent of the pair `(lateralPart X, W)`. -/
theorem IsWholePlaneGFF.indepFun_radialUniform_lateralPart_prodMk (hX : IsWholePlaneGFF X P)
    {δ : Type*} [MeasurableSpace δ] {W : Ω → δ} (hW : Measurable W) (hXW : IndepFun X W P) :
    IndepFun (fun ω => radialUniform (X ω))
      (fun ω => (MatedCRTHarmonic.CellScaling.lateralPart (X ω), W ω)) P := by
  have := hX.gaussian.isProbabilityMeasure
  refine indepFun_prodMk_right_of_indepFun_prodMk
    (measurable_radialUniform.comp hX.measurable) (measurable_lateralPart.comp hX.measurable) hW
    (IsWholePlaneGFF.indepFun_radialUniform_lateralPart hX) ?_
  exact hXW.comp (φ := fun h => (radialUniform h, MatedCRTHarmonic.CellScaling.lateralPart h))
    (measurable_radialUniform.prodMk measurable_lateralPart) measurable_id

end LatticeProb.LQG
