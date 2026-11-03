/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.ZBCM at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovHarm
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedM7D2

/-!
# Cameron–Martin for the zero-boundary GFF, shift by `F ∈ C_c^∞(U)` (task P2-MQ)

MQ (Miller–Qian, arXiv:1812.03913, `lqg_geodesics.tex`, proof of Lemma 4.1, l. 576–583): for a
zero-boundary GFF `h̃` on `U` and `g ∈ C_c^∞(U)`, the law of `h̃ + g` has RN derivative
`exp((h̃, g)_∇ − ‖g‖²_∇/2)` w.r.t. that of `h̃` (Berestycki–Powell arXiv:2404.16642,
Prop. `lem:CMGFF`). Here, for a zero-boundary GFF process `X` on `U` (`IsZBGFFProcess`) and
`F ∈ C_c^∞(U)` with `ρ_F = −ΔF/(2π)` (`MarkovHarm.cmTestOn`), `σ = δ_{ρ_F}`:

* `covShift_cmSigma` : the Cameron–Martin shift `K(ψ, σ) = ⟨ρ_F, ψ⟩_{H⁻¹(U)} = ∫ F ψ`;
* `covNorm_cmSigma` : `K(σ, σ) = (F, F)_∇` (Dirichlet energy on `U`);
* `map_tiltMeasure_cmSigma` : `law(X + ∫ F ·)` = the `exp(X(ρ_F) − (F,F)_∇/2)`-tilt of `P`,
  pushed forward (QZ's abstract `CameronMartin.map_tiltMeasure_path`);
* `lintegral_rnDeriv_tilt_rpow` : `∫ (dQ/dP)^q dP = exp(q(q−1)K(σ,σ)/2)` for the tilt `Q`.

The key identity `zbRiesz U ρ_F = ∇F` is `MarkovHarm.zbRiesz_cmTestOn` (Green's identity).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric.MQ

open QuantumZipper QuantumZipper.K3 QuantumZipper.CameronMartin MarkovZB MarkovHarm

/-- `zbRiesz U ρ_F = ∇F`, with the auxiliary whole-plane GFF supplied by `exists_wholePlaneGFF`. -/
lemma zbRiesz_cmTestOn_mq {U : Opens ℂ} (hadm : ZBAdmissible U) (f : zsSub U) :
    zbRiesz U (cmTestOn f) = gradFeat U f := by
  obtain ⟨Ω, _, P, h, hP, hh⟩ := GFFExist.exists_wholePlaneGFF
  exact zbRiesz_cmTestOn hh hadm f

/-- `σ = δ_{ρ_F}` -/
def cmSigma {U : Opens ℂ} (f : zsSub U) : TestOn U →₀ ℝ := Finsupp.single (cmTestOn f) 1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Opens ℂ} {X : TestOn U → Ω → ℝ}

lemma covShift_cmSigma (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    (hX : IsZBGFFProcess U X P) (f : zsSub U) (ψ : TestOn U) :
    covShift X P (cmSigma f) ψ = ∫ x, f.1 x * ψ x := by
  simp only [covShift, covK, cmSigma, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
  rw [hX.covariance_eq, zeroGFFTestCov_eq_inner hadm, zbRiesz_cmTestOn_mq hadm,
    inner_zbRiesz_gradFeat hadm (exists_pos_energy_zeroSpace_m7d U.isOpen hne) ψ f.2]

lemma covNorm_cmSigma (hadm : ZBAdmissible U) (hX : IsZBGFFProcess U X P) (f : zsSub U) :
    covNorm X P (cmSigma f) = dirichletEnergyOn U f.1 := by
  simp only [covNorm, covShift, covK, cmSigma, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  rw [hX.covariance_eq, zeroGFFTestCov_eq_inner hadm, zbRiesz_cmTestOn_mq hadm,
    real_inner_self_eq_norm_sq, norm_gradFeat_sq (hV.smooth _ f.2) (hV.energy _ f.2)]

/-- **Cameron–Martin for the zero-boundary GFF** (law form). -/
theorem map_tiltMeasure_cmSigma (hadm : ZBAdmissible U) (hne : (U : Set ℂ).Nonempty)
    (hX : IsZBGFFProcess U X P) (f : zsSub U) :
    (tiltMeasure X P (cmSigma f)).map (fun ω j => X j ω) =
      P.map (fun ω j => X j ω + ∫ x, f.1 x * j x) := by
  rw [map_tiltMeasure_path hX.gaussian hX.measurable hX.centered (cmSigma f)]
  congr 1
  funext ω j
  rw [covShift_cmSigma hadm hne hX f j]

/-- the `q`-th moment of the Cameron–Martin density: `E[D^q] = exp(q(q−1)K(σ,σ)/2)` -/
theorem lintegral_rnDeriv_tilt_rpow {I : Type*} {Y : I → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hmeas : ∀ i, Measurable (Y i)) (hcent : ∀ i, P[Y i] = 0) (σ : I →₀ ℝ) (q : ℝ) :
    ∫⁻ ω, ((tiltMeasure Y P σ).rnDeriv P ω) ^ q ∂P =
      ENNReal.ofReal (Real.exp (q * (q - 1) * covNorm Y P σ / 2)) := by
  have hP := hY.isProbabilityMeasure
  set K := covNorm Y P σ
  set D := tiltDensity Y P σ
  have hDm : Measurable D := measurable_tiltDensity hY hmeas σ
  have hrn := Measure.rnDeriv_withDensity P (hDm.real_toNNReal.coe_nnreal_ennreal)
  have e1 : ∫⁻ ω, ((tiltMeasure Y P σ).rnDeriv P ω) ^ q ∂P =
      ∫⁻ ω, ENNReal.ofReal (D ω ^ q) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrn] with ω hω
    rw [tiltMeasure, hω]
    exact ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)
  set Z : Ω → ℝ := fun ω => q * comb Y σ ω
  have hZ : HasGaussianLaw Z P := by
    have h := hasGaussianLaw_finsetComb hY σ.support (fun i => q * σ i)
    have e : (fun ω => ∑ i ∈ σ.support, q * σ i * Y i ω) = Z := by
      funext ω; simp only [Z, comb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rwa [e] at h
  have hZm : P[Z] = 0 := by
    have h := integral_finsetComb hY hcent σ.support (fun i => q * σ i)
    have e : (fun ω => ∑ i ∈ σ.support, q * σ i * Y i ω) = Z := by
      funext ω; simp only [Z, comb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rwa [e] at h
  obtain ⟨hi, he⟩ := gauss_exp hY hcent hZ hZm
  have hVZ : Var[Z; P] = q ^ 2 * K := by
    rw [variance_const_mul, variance_comb hY]
  have eD : (fun ω => D ω ^ q) = fun ω => Real.exp (Z ω) * Real.exp (-(q * K / 2)) := by
    funext ω
    rw [show D ω = Real.exp (comb Y σ ω - K / 2) from rfl, ← Real.exp_mul, ← Real.exp_add]
    congr 1; simp only [Z]; ring
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [eD, integral_mul_const, he, hVZ, ← Real.exp_add]
    congr 2; ring
  · rw [eD]; exact hi.mul_const _
  · exact Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (Real.exp_pos _).le _

end LQGMetric.MQ
