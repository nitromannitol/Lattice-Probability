/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.ZBCMLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41

/-!
# Cameron–Martin for the zero-boundary GFF as a law identity with an explicit density

For a zero-boundary GFF `Z` on `U` and `F ∈ C_c^∞(U)` with `T = ∫ F ·`, the law of `Z + T` has density
`ρ(z) = exp(z(ρ_F) − (F, F)_∇ / 2)` (`ρ_F = −ΔF/(2π)`) with respect to the law of `Z`, and
`E[ρ^s] = exp(s(s−1)(F,F)_∇/2)` for every real `s` — the Radon–Nikodym derivative `exp((h̊, g)_∇ − ½(g, g)_∇)` and the
Gaussian moment computation of the proof of [18] Lemma A.5, for a
deterministic shift. Assembled from LQGMetric's `MQ.map_tiltMeasure_cmSigma` (QuantumZipper's abstract
Cameron–Martin theorem) and `MQ.lintegral_rnDeriv_tilt_rpow`.

* `GMSAppA.zbcm_lintegral` — `∫ Ψ(z + T) dν_Z = ∫ Ψ(z) ρ(z) dν_Z` for measurable `Ψ ≥ 0`.
* `GMSAppA.zbcm_moment` — `∫ ρ^s dν_Z = exp(s(s−1)(F,F)_∇/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

open LQGMetric LQGMetric.MQ QuantumZipper QuantumZipper.CameronMartin MarkovZB MarkovHarm

/-- the Cameron–Martin density `z ↦ exp(z(ρ_F) − (F,F)_∇/2)` on `𝒟'(U)` -/
def zbDensity {U : Opens ℂ} (f : zsSub (U : Set ℂ)) (z : DistOn U) : ℝ :=
  Real.exp (z (cmTestOn f) - dirichletEnergyOn U f.1 / 2)

lemma measurable_zbDensity {U : Opens ℂ} (f : zsSub (U : Set ℂ)) : Measurable (zbDensity f) :=
  Real.measurable_exp.comp ((measurable_distOn_apply _).sub_const _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma tiltDensity_cmSigma {U : Opens ℂ} (hadm : ZBAdmissible U) {Z : Ω → DistOn U}
    (hZ : IsZeroBoundaryGFF U Z P) (f : zsSub (U : Set ℂ)) (ω : Ω) :
    tiltDensity (fun φ ω => Z ω φ) P (cmSigma f) ω = zbDensity f (Z ω) := by
  unfold tiltDensity zbDensity
  rw [covNorm_cmSigma hadm hZ.process f]
  simp only [comb, cmSigma, Finsupp.support_single_ne_zero _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]

/-- **Cameron–Martin, law form**: `∫ Ψ(z + T) dν_Z = ∫ Ψ(z) ρ(z) dν_Z`. -/
theorem zbcm_lintegral {U : Opens ℂ} (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    {Z : Ω → DistOn U} (hZ : IsZeroBoundaryGFF U Z P) (f : zsSub (U : Set ℂ)) {T : DistOn U}
    (hT : ∀ φ : TestOn U, T φ = ∫ x, f.1 x * φ x) {Ψ : DistOn U → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ z, Ψ (z + T) ∂(P.map Z) = ∫⁻ z, Ψ z * ENNReal.ofReal (zbDensity f z) ∂(P.map Z) := by
  set X : TestOn U → Ω → ℝ := fun φ ω => Z ω φ
  have hX : IsZBGFFProcess U X P := hZ.process
  set Q := tiltMeasure X P (cmSigma f)
  have hev : Measurable (fun (T : DistOn U) (φ : TestOn U) => T φ) :=
    measurable_iff_comap_le.2 le_rfl
  have hR' : Measurable fun ω => Z ω + T :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hZ.measurable).add_const (T φ)
  have hμ : P.map (fun ω => Z ω + T) = Q.map Z := by
    refine measure_distOn_ext ?_
    rw [Measure.map_map hev hR', Measure.map_map hev hZ.measurable]
    have e1 : ((fun (T : DistOn U) (φ : TestOn U) => T φ) ∘ Z) = fun ω j => X j ω := rfl
    rw [e1, map_tiltMeasure_cmSigma hadm hne hX f]
    congr 1
    funext ω φ
    simp only [Function.comp_apply, ContinuousLinearMap.add_apply, hT, X]
  have hadd : Measurable fun z : DistOn U => z + T :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const (T φ)
  calc ∫⁻ z, Ψ (z + T) ∂(P.map Z) = ∫⁻ ω, Ψ (Z ω + T) ∂P :=
        lintegral_map (hΨ.comp hadd) hZ.measurable
    _ = ∫⁻ z, Ψ z ∂(P.map fun ω => Z ω + T) := (lintegral_map hΨ hR').symm
    _ = ∫⁻ z, Ψ z ∂(Q.map Z) := by rw [hμ]
    _ = ∫⁻ ω, Ψ (Z ω) ∂Q := lintegral_map hΨ hZ.measurable
    _ = ∫⁻ ω, (fun ω => ((tiltDensity X P (cmSigma f) ω).toNNReal : ℝ≥0∞)) ω * Ψ (Z ω) ∂P :=
        lintegral_withDensity_eq_lintegral_mul P
          (measurable_tiltDensity hX.gaussian hX.measurable (cmSigma f)).real_toNNReal.coe_nnreal_ennreal
          (hΨ.comp hZ.measurable)
    _ = ∫⁻ ω, Ψ (Z ω) * ENNReal.ofReal (zbDensity f (Z ω)) ∂P := by
        refine lintegral_congr fun ω => ?_
        simp only [Pi.mul_apply]
        rw [mul_comm, tiltDensity_cmSigma hadm hZ f ω]
        rfl
    _ = ∫⁻ z, Ψ z * ENNReal.ofReal (zbDensity f z) ∂(P.map Z) :=
        (lintegral_map (hΨ.mul (measurable_zbDensity f).ennreal_ofReal) hZ.measurable).symm

/-- **Moments of the Cameron–Martin density**: `∫ ρ^s dν_Z = exp(s(s−1)(F,F)_∇/2)` for every real `s`. -/
theorem zbcm_moment {U : Opens ℂ} (hadm : ZBAdmissible U) {Z : Ω → DistOn U}
    (hZ : IsZeroBoundaryGFF U Z P) (f : zsSub (U : Set ℂ)) (s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (zbDensity f z) ^ s ∂(P.map Z) =
      ENNReal.ofReal (Real.exp (s * (s - 1) * dirichletEnergyOn U f.1 / 2)) := by
  set X : TestOn U → Ω → ℝ := fun φ ω => Z ω φ
  have hX : IsZBGFFProcess U X P := hZ.process
  have hm := lintegral_rnDeriv_tilt_rpow hX.gaussian hX.measurable hX.centered (cmSigma f) s
  rw [covNorm_cmSigma hadm hX f] at hm
  rw [← hm, lintegral_map ((measurable_zbDensity f).ennreal_ofReal.pow_const s) hZ.measurable]
  have hD : Measurable fun ω => ((tiltDensity X P (cmSigma f) ω).toNNReal : ℝ≥0∞) :=
    (measurable_tiltDensity hX.gaussian hX.measurable (cmSigma f)).real_toNNReal.coe_nnreal_ennreal
  have hrn := Measure.rnDeriv_withDensity P hD
  refine lintegral_congr_ae ?_
  filter_upwards [hrn] with ω hω
  show ENNReal.ofReal (zbDensity f (Z ω)) ^ s = ((tiltMeasure X P (cmSigma f)).rnDeriv P ω) ^ s
  rw [show tiltMeasure X P (cmSigma f) = P.withDensity fun ω =>
    ((tiltDensity X P (cmSigma f) ω).toNNReal : ℝ≥0∞) from rfl, hω,
    tiltDensity_cmSigma hadm hZ f ω]
  rfl

end MatedCRTHarmonic.GMSAppA
