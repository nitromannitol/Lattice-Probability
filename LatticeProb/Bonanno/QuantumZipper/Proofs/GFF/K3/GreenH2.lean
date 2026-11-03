/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenH2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower4Trunc

/-!
# GFF-K3, nodes H6 and H7: `dualNormSq H (zeroSpace H) = kernelCov greenH` on `IsAdmissibleH`

* H6 `le_dualNormSq_H`: `B(μ, μ) ≤ dualNormSq H (zeroSpace H) μ`.
  Proof (blueprint H6, with the truncation route of `GreenLower4`): let `D` be the dual norm
  squared (finite by H3), so `|∫ f dμ| ≤ √D √E(f)` on `zeroSpace H`. Pick the smooth
  approximation `σ = σε μ ε` of H4 with `e := ‖v_μ − v_σ‖ = B(μ − σ)^{1/2}` small. By the signed
  H3, `∫ f dσ ≤ (√D + e) √E(f)`, so `kernelCov_densMeas_le` gives `‖v_σ‖ ≤ √D + e`, hence
  `√B(μ,μ) = ‖v_μ‖ ≤ √D + 2e`.
* H7 `dualNormSq_H_eq`, `dualCov_H_eq` (polarization), `closure_H_K3`,
  `isAdmissibleDual_H_of_isAdmissibleH`, `IsZeroBoundaryGFFOn.toH`.
-/

noncomputable section

open MeasureTheory Filter Set Topology Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- The densities `φσ μ ε` of the smoothed measures `σε μ ε` satisfy `GoodDens`. -/
lemma goodDens_φσ {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {ε : ℝ} (hε : 0 < ε) :
    GoodDens (φσ μ ε) ε := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, -⟩ := id hμ
  have := hμf
  refine ⟨hε, contDiff_φσ hε, ?_, fun z => φσ_nonneg hε z, fun z hz => ?_⟩
  · exact HasCompactSupport.intro (isCompact_Kσ hK ε) fun a ha => φσ_eq_zero hKc hε ha
  · by_contra h
    exact hz (φσ_eq_zero hKc hε fun ha => h (Kσ_subset hKH hε ha))

lemma dirichletEnergyOn_nonneg_K3 (D : Set ℂ) (f : ℂ → ℝ) : 0 ≤ dirichletEnergyOn D f :=
  mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)

open GFFExist in
lemma norm_zeroVec_sq {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ‖zeroVec ⟨μ, hμ⟩‖ ^ 2 = kernelCov greenH μ μ := by
  rw [← real_inner_self_eq_norm_sq, zeroVec_inner]

open GFFExist in
lemma norm_zeroVec_sub_sq {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    ‖zeroVec ⟨μ, hμ⟩ - zeroVec ⟨ν, hν⟩‖ ^ 2 = kernelCov2 greenH (μ, ν) (μ, ν) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, zeroVec_inner, kernelCov2]
  ring

lemma kernelCov_greenH_nonneg_K3 {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    0 ≤ kernelCov greenH μ μ := by
  rw [← norm_zeroVec_sq hμ]; positivity

open GFFExist in
/-- **H6.** Lower bound for the dual norm on `ℍ`. -/
theorem le_dualNormSq_H {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ENNReal.ofReal (kernelCov greenH μ μ) ≤ dualNormSq H (zeroSpace H) μ := by
  have hfin := (dualNormSq_H_le hμ).trans_lt ENNReal.ofReal_lt_top
  set D := (dualNormSq H (zeroSpace H) μ).toReal with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hDeq : dualNormSq H (zeroSpace H) μ = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal hfin.ne).symm
  have hstar : ∀ f ∈ zeroSpace H,
      |∫ x, f x ∂μ| ≤ Real.sqrt D * Real.sqrt (dirichletEnergyOn H f) := by
    intro f hf
    rw [← Real.sqrt_mul hD0, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    rcases (dirichletEnergyOn_nonneg_K3 H f).lt_or_eq with hE | hE
    · have h1 : ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn H f) ≤
          ENNReal.ofReal D := by
        rw [← hDeq]
        unfold dualNormSq
        exact le_iSup₂ (f := fun f (_ : f ∈ {f ∈ zeroSpace H | 0 < dirichletEnergyOn H f}) =>
          ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn H f)) f ⟨hf, hE⟩
      have h2 := (ENNReal.ofReal_le_ofReal_iff hD0).mp h1
      rwa [div_le_iff₀ hE] at h2
    · have h := sq_integral_sub_le_energy_mul hμ isAdmissibleH_zero_K3 hf
      rw [integral_zero_measure, sub_zero, ← hE, zero_mul] at h
      rw [← hE, mul_zero]
      exact h
  have hB0 := kernelCov_greenH_nonneg_K3 hμ
  suffices hs : Real.sqrt (kernelCov greenH μ μ) ≤ Real.sqrt D by
    rw [hDeq]
    exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt_iff hD0).mp hs)
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨ε, hε, hd⟩ := exists_σε_close hμ (δ := (η / 2) ^ 2) (by positivity)
  have hσ := isAdmissibleH_σε hμ hε
  have hG := goodDens_φσ hμ hε
  set e := ‖zeroVec ⟨μ, hμ⟩ - zeroVec ⟨σε μ ε, hσ⟩‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have he2 : e ^ 2 = kernelCov2 greenH (μ, σε μ ε) (μ, σε μ ε) := norm_zeroVec_sub_sq hμ hσ
  have heη : e < η / 2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) (he2 ▸ hd)
  -- the hypothesis of `kernelCov_densMeas_le` for `σ` with `C = √D + e`
  have hC : ∀ f ∈ zeroSpace H, ∫ x, f x ∂densMeas (φσ μ ε) ≤
      (Real.sqrt D + e) * Real.sqrt (dirichletEnergyOn H f) := by
    intro f hf
    have h3 := sq_integral_sub_le_energy_mul hμ hσ hf
    rw [← he2] at h3
    have h4 : |∫ x, f x ∂μ - ∫ x, f x ∂σε μ ε| ≤ Real.sqrt (dirichletEnergyOn H f) * e := by
      rw [← Real.sqrt_sq he0, ← Real.sqrt_mul (dirichletEnergyOn_nonneg_K3 H f),
        ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h3
    have h5 := hstar f hf
    change ∫ x, f x ∂σε μ ε ≤ _
    have := le_abs_self (∫ x, f x ∂μ)
    have := neg_abs_le (∫ x, f x ∂μ - ∫ x, f x ∂σε μ ε)
    nlinarith
  have hBσ := kernelCov_densMeas_le hG (by positivity) hC
  change kernelCov greenH (σε μ ε) (σε μ ε) ≤ _ at hBσ
  rw [← norm_zeroVec_sq hσ] at hBσ
  have hvσ : ‖zeroVec ⟨σε μ ε, hσ⟩‖ ≤ Real.sqrt D + e :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hBσ
  have htri : ‖zeroVec ⟨μ, hμ⟩‖ ≤ ‖zeroVec ⟨σε μ ε, hσ⟩‖ + e := by
    calc ‖zeroVec ⟨μ, hμ⟩‖ = ‖zeroVec ⟨σε μ ε, hσ⟩ + (zeroVec ⟨μ, hμ⟩ - zeroVec ⟨σε μ ε, hσ⟩)‖ := by
          rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [← norm_zeroVec_sq hμ, Real.sqrt_sq (norm_nonneg _)]
  linarith

/-- **H7.** The dual norm on `ℍ` equals the Green energy. -/
theorem dualNormSq_H_eq {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    dualNormSq H (zeroSpace H) μ = ENNReal.ofReal (kernelCov greenH μ μ) :=
  le_antisymm (dualNormSq_H_le hμ) (le_dualNormSq_H hμ)

lemma kernelCov_greenH_add_left_K3 {μ ν ρ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (hρ : IsAdmissibleH ρ) :
    kernelCov greenH (μ + ν) ρ = kernelCov greenH μ ρ + kernelCov greenH ν ρ := by
  have := hρ.1; have := hμ.1; have := hν.1
  unfold kernelCov
  exact integral_add_measure (integrable_greenH_prod hμ hρ).integral_prod_left
    (integrable_greenH_prod hν hρ).integral_prod_left

/-- **H7.** The dual covariance on `ℍ` equals `kernelCov greenH`. -/
theorem dualCov_H_eq {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    dualCov H (zeroSpace H) μ ν = kernelCov greenH μ ν := by
  have hs := isAdmissibleH_add hμ hν
  unfold dualCov
  rw [dualNormSq_H_eq hs, dualNormSq_H_eq hμ, dualNormSq_H_eq hν,
    ENNReal.toReal_ofReal (kernelCov_greenH_nonneg_K3 hs),
    ENNReal.toReal_ofReal (kernelCov_greenH_nonneg_K3 hμ),
    ENNReal.toReal_ofReal (kernelCov_greenH_nonneg_K3 hν),
    kernelCov_greenH_add_left_K3 hμ hν hs, ZeroReg.kernelCov_greenH_symm hμ hs,
    ZeroReg.kernelCov_greenH_symm hν hs, kernelCov_greenH_add_left_K3 hμ hν hμ,
    kernelCov_greenH_add_left_K3 hμ hν hν, ZeroReg.kernelCov_greenH_symm hν hμ]
  ring

theorem closure_H_K3 : closure H = Hbar := Complex.closure_setOfPred_lt_im 0

/-- **H7.** `IsAdmissibleH` measures are admissible for the dual norm on `ℍ`. -/
theorem isAdmissibleDual_H_of_isAdmissibleH {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    IsAdmissibleDual H (zeroSpace H) μ := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, -⟩ := id hμ
  exact ⟨hμf, ⟨K, hK, closure_H_K3 ▸ hKH, hKc⟩,
    (dualNormSq_H_le hμ).trans_lt ENNReal.ofReal_lt_top⟩

end QuantumZipper.K3
