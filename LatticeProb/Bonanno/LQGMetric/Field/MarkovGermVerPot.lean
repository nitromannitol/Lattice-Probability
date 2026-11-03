/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVerPot at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer

/-!
# Mean-zero pairings are whole-plane Dirichlet pairings: the cutoff identity (task P2-MKD, part 2)

Node (a) of `handoff/P2-MKD.md`: for `ψ ∈ 𝓓₀(ℂ)` the pairing `⟨h, ψ⟩` is the Dirichlet pairing
`(h, u_ψ)_∇` with the logarithmic potential `u_ψ(x) = ∫ −log|x−y| ψ(y) dy`
(`−Δu_ψ = 2πψ`). Here:

* `logPot`, `contDiff_logPot` (a convolution with `log|·|`, as QuantumZipper
  `K3.contDiff_Vpot`), `integral_mul_logPot`: `∫ ρ u_ψ = logCov ρ ψ`;
* `gradEnergy_cut`: the IMS-type identity `E(χ u_ψ) = ∫ ψ u_ψ + (2π)⁻¹ ∫ u_ψ² |∇χ|²` for a cutoff
  `χ ∈ C_c^∞` equal to `1` on `supp ψ` (QuantumZipper `K3.energy_mul_gpot` is the same identity
  for the half-plane Green potential);
* `norm_cmLin_cut_sub_sq`: hence `‖(h, χ u_ψ)_∇ − ⟨h, ψ⟩‖²_{L²(P)} = (2π)⁻¹ ∫ u_ψ² |∇χ|²`.

Source: the Green-function representation of the whole-plane GFF covariance
(Berestycki–Powell arXiv:2404.16642, §1.8 / whole-plane GFF; Sheffield math/0312099 §2.6:
`(h, a)_∇ = (h, ρ)` for `−Δa = ρ`). The identity is the standard integration by parts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace Laplacian
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the logarithmic potential `u_ψ(x) = ∫ −log|x−y| ψ(y) dy` -/
def logPot (ψ : ℂ → ℝ) (x : ℂ) : ℝ := ∫ y, -Real.log ‖x - y‖ * ψ y

lemma logPot_eq_neg_Vpot (ψ : ℂ → ℝ) : logPot ψ = fun x => -Vpot ψ x := by
  funext x
  rw [logPot, Vpot, ← integral_neg]
  congr 1; funext y
  rw [norm_sub_rev]; ring

lemma contDiff_logPot (ψ : TestC) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logPot ψ) := by
  have hc := ψ.hasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (n := ⊤) ψ.contDiff locallyIntegrable_log_norm
  have e : Vpot ψ = MeasureTheory.convolution ψ (fun v : ℂ => Real.log ‖v‖)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := funext (Vpot_eq_conv ψ)
  have e2 : logPot ψ = fun x => -(MeasureTheory.convolution ψ (fun v : ℂ => Real.log ‖v‖)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) x := by rw [logPot_eq_neg_Vpot, e]
  rw [e2]
  exact hc.neg

/-- `∫ ρ u_ψ = logCov ρ ψ` -/
lemma integral_mul_logPot (ρ ψ : ℂ → ℝ) : ∫ x, ρ x * logPot ψ x = logCov ρ ψ := by
  unfold logCov logPot
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext y; ring

omit [IsProbabilityMeasure P] in
/-- symmetry of the covariance on mean-zero test functions -/
lemma logCov_comm_of_gff (hh : IsWholePlaneGFF h P) (a b : TestC0) :
    logCov a.1 b.1 = logCov b.1 a.1 := by
  rw [← hh.covariance_eq, ← hh.covariance_eq, covariance_comm]

/-- `C_c^∞(ℂ)` as test functions -/
def ofSmooth {f : ℂ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    zsSub ((⊤ : Opens ℂ) : Set ℂ) :=
  ⟨f, hf, hc, subset_univ _⟩

/-- pointwise: `|∇(χu)|² = ⟨∇u, ∇(χ²u)⟩ + u²|∇χ|²` -/
lemma norm_fderiv_mul_sq {χ u : ℂ → ℝ} {z : ℂ} (hχ : DifferentiableAt ℝ χ z)
    (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ (fun x => χ x * u x) z‖ ^ 2 =
      gradInner u (fun x => χ x * (χ x * u x)) z + u z ^ 2 * ‖fderiv ℝ χ z‖ ^ 2 := by
  have h1 : fderiv ℝ (fun x => χ x * u x) z = χ z • fderiv ℝ u z + u z • fderiv ℝ χ z :=
    fderiv_mul hχ hu
  have h2 : fderiv ℝ (fun x => χ x * (χ x * u x)) z =
      χ z • (χ z • fderiv ℝ u z + u z • fderiv ℝ χ z) + (χ z * u z) • fderiv ℝ χ z :=
    (fderiv_mul hχ (hχ.mul hu)).trans (by
      have h1' : fderiv ℝ (χ * u) z = χ z • fderiv ℝ u z + u z • fderiv ℝ χ z := h1
      rw [h1', Pi.mul_apply])
  rw [norm_fderiv_sq_eq_gradInner, norm_fderiv_sq_eq_gradInner, gradInner, gradInner, gradInner,
    h1, h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- the test function `C_c^∞(ℂ) ∋ f` -/
abbrev tC {f : ℂ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    TestC := zsTest (ofSmooth hf hc).2

lemma smooth_le {f : ℂ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (n : ℕ) :
    ContDiff ℝ n f := hf.of_le (by exact_mod_cast le_top)

omit [IsProbabilityMeasure P] in
/-- **IMS identity**: `E(χ u_ψ) = ∫ ψ u_ψ + (2π)⁻¹ ∫ u_ψ² |∇χ|²` for `χ = 1` on `supp ψ` -/
theorem gradEnergy_cut (hh : IsWholePlaneGFF h P) (ψ : TestC0) {χ : ℂ → ℝ}
    (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ x ∈ tsupport (ψ.1 : ℂ → ℝ), χ x = 1) :
    gradEnergy (fun x => χ x * logPot ψ.1 x) = (∫ x, ψ.1 x * logPot ψ.1 x) +
      (2 * Real.pi)⁻¹ * ∫ x, logPot ψ.1 x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 := by
  set u := logPot ψ.1 with hu
  have hus := contDiff_logPot ψ.1
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => χ x * (χ x * u x) :=
    hχs.mul (hχs.mul hus)
  have hgc : HasCompactSupport fun x => χ x * (χ x * u x) := hχc.mul_right
  have hψu : ∀ x, ψ.1 x * (χ x * (χ x * u x)) = ψ.1 x * u x := fun x => by
    by_cases hx : x ∈ tsupport (ψ.1 : ℂ → ℝ)
    · rw [hχ1 x hx]; ring
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
  -- `∫ ⟨∇u, ∇g⟩ = 2π ∫ ψ u`
  have hG : ∫ z, gradInner u (fun x => χ x * (χ x * u x)) z = 2 * Real.pi * ∫ x, ψ.1 x * u x := by
    rw [integral_gradInner_eq_neg_integral_mul_laplacian (smooth_le hus 1) (smooth_le hgs 2) hgc]
    have e1 : ∀ z, u z * Δ (fun x => χ x * (χ x * u x)) z =
        -(2 * Real.pi) * (cmTest (tC hgs hgc) z * u z) := fun z => by
      rw [cmTest_apply]
      have : ((tC hgs hgc : TestC) : ℂ → ℝ) = fun x => χ x * (χ x * u x) := rfl
      rw [this]
      field_simp
    have e2 : ∫ z, u z * Δ (fun x => χ x * (χ x * u x)) z =
        -(2 * Real.pi) * ∫ z, cmTest (tC hgs hgc) z * u z := by
      rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall e1)
    have hsym : logCov (cmTest (tC hgs hgc)) ψ.1 = logCov ψ.1 (cmTest (tC hgs hgc)) :=
      logCov_comm_of_gff hh (cmTest0 (tC hgs hgc)) ψ
    rw [e2, integral_mul_logPot, hsym, logCov_cmTest_right]
    have : ∫ x, ψ.1 x * (tC hgs hgc) x = ∫ x, ψ.1 x * u x :=
      integral_congr_ae (Eventually.of_forall fun x => hψu x)
    rw [this]; ring
  have hi1 : Integrable fun z => gradInner u (fun x => χ x * (χ x * u x)) z := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold gradInner
      have c1 := (smooth_le hus 1).continuous_fderiv one_ne_zero
      have c2 := (smooth_le hgs 1).continuous_fderiv one_ne_zero
      fun_prop
    · refine (hgc.fderiv (𝕜 := ℝ)).mono fun z hz => ?_
      intro h0
      apply hz
      simp [gradInner, h0]
  have hi2 : Integrable fun z => u z ^ 2 * ‖fderiv ℝ χ z‖ ^ 2 := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c1 := (smooth_le hχs 1).continuous_fderiv one_ne_zero
      have c0 := hus.continuous
      fun_prop
    · refine (hχc.fderiv (𝕜 := ℝ)).mono fun z hz => ?_
      intro h0
      apply hz
      simp [h0]
  rw [gradEnergy]
  have ept : ∀ z, ‖fderiv ℝ (fun x => χ x * u x) z‖ ^ 2 =
      gradInner u (fun x => χ x * (χ x * u x)) z + u z ^ 2 * ‖fderiv ℝ χ z‖ ^ 2 := fun z =>
    norm_fderiv_mul_sq ((smooth_le hχs 1).differentiable one_ne_zero z)
      ((smooth_le hus 1).differentiable one_ne_zero z)
  simp_rw [ept]
  rw [integral_add hi1 hi2, hG]
  field_simp

/-- **The cutoff identity in `L²(P)`**: `‖(h, χ u_ψ)_∇ − ⟨h, ψ⟩‖² = (2π)⁻¹ ∫ u_ψ² |∇χ|²` -/
theorem norm_cmLin_cut_sub_sq (hh : IsWholePlaneGFF h P) (ψ : TestC0) {χ : ℂ → ℝ}
    (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ x ∈ tsupport (ψ.1 : ℂ → ℝ), χ x = 1) :
    ‖cmLin hh ⊤ (ofSmooth (hχs.mul (contDiff_logPot ψ.1)) (hχc.mul_right (f' := logPot ψ.1))) -
        (memLp_pair hh ψ).toLp (pairProc h ψ)‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ x, logPot ψ.1 x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2 := by
  set F := ofSmooth (hχs.mul (contDiff_logPot ψ.1)) (hχc.mul_right (f' := logPot ψ.1))
  have hA : ‖cmLin hh ⊤ F‖ ^ 2 = gradEnergy fun x => χ x * logPot ψ.1 x := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [inner_toLp_eq_cov _ _ (centered_pairProc hh _)]
    exact (hh.covariance_eq _ _).trans (logCov_cmTest_cmTest _)
  have hAB : ⟪cmLin hh ⊤ F, (memLp_pair hh ψ).toLp (pairProc h ψ)⟫ =
      ∫ x, ψ.1 x * logPot ψ.1 x := by
    rw [← cmIso_gradLin, inner_cmIso_gradLin]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ψ.1 x * (χ x * logPot ψ.1 x) = ψ.1 x * logPot ψ.1 x
    by_cases hx : x ∈ tsupport (ψ.1 : ℂ → ℝ)
    · rw [hχ1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hB : ‖(memLp_pair hh ψ).toLp (pairProc h ψ)‖ ^ 2 = ∫ x, ψ.1 x * logPot ψ.1 x := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_cov _ _ (centered_pairProc hh _),
      integral_mul_logPot]
    exact hh.covariance_eq ψ ψ
  rw [norm_sub_sq_real, hA, hAB, hB, gradEnergy_cut hh ψ hχs hχc hχ1]
  ring

end MarkovGermVer
end LQGMetric
