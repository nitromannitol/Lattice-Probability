import Mathlib
import LatticeProb.Gauss.CameronMartinLipschitz
import LatticeProb.Gauss.CameronMartinBounded
import LatticeProb.Analysis.SmoothApproxLocallyLipschitz

/-!
# Absolute continuity of the whole-plane Gaussian free field under locally Lipschitz shifts

Let `g : ℂ → ℝ` be locally Lipschitz with compact support and `h` a whole-plane Gaussian free
field. For a finite family `φ_i` of mean-zero test functions and real coefficients `c_i`,

* (energy bound) `|∑ c_i ∫ φ_i g| ≤ C · sd(∑ c_i (h, φ_i))` with `C` depending only on `g`;
* (shift) every measurable set of mean-zero pairings that is null for `h` stays null after the
  shift `(h, φ) ↦ (h, φ) + ∫ φ g`.

The energy bound is obtained by approximating `g` by smooth functions with a uniform gradient bound
and using the Cauchy–Schwarz inequality for the covariance with `(h, q_f)`; the shift statement is
then the Cameron–Martin theorem for bounded functionals of a centred Gaussian process.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal ContDiff

section Aux

/-- The Dirichlet energy of a smooth function with gradient bounded by `K`, supported in the ball of
radius `R`, is at most `K² · vol B(0, R)`. -/
theorem integral_norm_fderiv_sq_le {h : ℂ → ℝ} {K R : ℝ} (hsupp : tsupport h ⊆ closedBall 0 R)
    (hK : ∀ x, ‖fderiv ℝ h x‖ ≤ K) :
    ∫ x, ‖fderiv ℝ h x‖ ^ 2 ≤ K ^ 2 * (volume (closedBall (0 : ℂ) R)).toReal := by
  have hmeas : MeasurableSet (closedBall (0 : ℂ) R) := measurableSet_closedBall
  have hzero : ∀ x, x ∉ closedBall (0 : ℂ) R → ‖fderiv ℝ h x‖ ^ 2 = 0 := fun x hx => by
    have : fderiv ℝ h x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hx (hsupp (tsupport_fderiv_subset ℝ hmem))
    simp [this]
  have hint : Integrable ((closedBall (0 : ℂ) R).indicator fun _ => K ^ 2) :=
    (integrable_indicator_iff hmeas).2
      (integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne)
  calc ∫ x, ‖fderiv ℝ h x‖ ^ 2
      ≤ ∫ x, (closedBall (0 : ℂ) R).indicator (fun _ => K ^ 2) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint
          (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ closedBall (0 : ℂ) R
        · rw [indicator_of_mem hx]
          exact pow_le_pow_left₀ (norm_nonneg _) (hK x) 2
        · rw [indicator_of_notMem hx]
          exact (hzero x hx).le
    _ = K ^ 2 * (volume (closedBall (0 : ℂ) R)).toReal := by
        rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_comm]
        rfl

/-- If `h` and `g` are continuous and `|h - g| ≤ ε`, then the integrals of a
compactly supported continuous `φ` against `h` and `g` differ by at most `ε ∫ |φ|`. -/
theorem abs_integral_mul_sub_le {φ h g : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) (hg : Continuous g) {ε : ℝ} (hε : ∀ x, |h x - g x| ≤ ε) :
    |(∫ x, φ x * h x) - ∫ x, φ x * g x| ≤ ε * ∫ x, |φ x| := by
  have h1 : Integrable (fun x => φ x * h x) :=
    (hφ.mul hh).integrable_of_hasCompactSupport hφc.mul_right
  have h2 : Integrable (fun x => φ x * g x) :=
    (hφ.mul hg).integrable_of_hasCompactSupport hφc.mul_right
  have hφi : Integrable (fun x => |φ x|) :=
    (hφ.integrable_of_hasCompactSupport hφc).abs
  rw [← integral_sub h1 h2, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (g := fun x => ε * |φ x|) (hφi.const_mul ε)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hε x) (abs_nonneg _)

end Aux

section Energy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Energy bound for a locally Lipschitz shift.** There is a constant `C` such that for every finite
family of mean-zero test functions `φ_i` and coefficients `c_i`,
`|∑ c_i ∫ φ_i g| ≤ C · sd (∑ c_i (h, φ_i))`. -/
theorem IsWholePlaneGFF.exists_abs_sum_integral_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {ι : Type*} {g : ℂ → ℝ} (hg : LocallyLipschitz g)
    (hc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ι) (c : ι → ℝ) (φ : ι → ℂ → ℝ),
      (∀ i ∈ s, IsTestFunction univ (φ i)) → (∀ i ∈ s, ∫ x, φ i x = 0) →
      |∑ i ∈ s, c i * ∫ x, φ i x * g x| ≤
        C * Real.sqrt Var[fun w => ∑ i ∈ s, c i * hC w (φ i); P] := by
  obtain ⟨K, R, hKR⟩ := exists_smooth_approx_of_locallyLipschitz hg hc
  set V : ℝ := (volume (closedBall (0 : ℂ) R)).toReal with hV
  refine ⟨Real.sqrt ((2 * Real.pi)⁻¹ * (K ^ 2 * V)), Real.sqrt_nonneg _, ?_⟩
  intro s c φ hφ hφ0
  have hL : ∀ ψ, IsTestFunction univ ψ → MemLp (fun w => hC w ψ) 2 P := fun ψ hψ => by
    have := (hh.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing ψ, hψ⟩).memLp_two
    exact this
  have hZ : MemLp (fun w => ∑ i ∈ s, c i * hC w (φ i)) 2 P := by
    exact memLp_finsetSum s (fun i hi => (hL (φ i) (hφ i hi)).const_mul (c i))
  have hVar : 0 ≤ Var[fun w => ∑ i ∈ s, c i * hC w (φ i); P] := variance_nonneg _ _
  -- the bound for smooth approximants
  have hsmooth : ∀ h : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h →
      tsupport h ⊆ closedBall 0 R → (∀ x, ‖fderiv ℝ h x‖ ≤ K) →
      |∑ i ∈ s, c i * ∫ x, φ i x * h x| ≤
        Real.sqrt ((2 * Real.pi)⁻¹ * (K ^ 2 * V)) *
          Real.sqrt Var[fun w => ∑ i ∈ s, c i * hC w (φ i); P] := by
    intro h hs hhc hsupp hK
    have hq := cmTestFn_isTestFunction hs hhc
    have hcs := covariance_sq_le_variance_mul hZ (hL _ hq)
    have hcov : cov[fun w => ∑ i ∈ s, c i * hC w (φ i), fun w => hC w (cmTestFn h); P] =
        ∑ i ∈ s, c i * ∫ x, φ i x * h x := by
      rw [covariance_fun_sum_left' (fun i hi => (hL (φ i) (hφ i hi)).const_mul (c i)) (hL _ hq)]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [covariance_const_mul_left, hh.cov_pairing_cmTestFn hs hhc (hφ i hi) (hφ0 i hi)]
    rw [hcov, hh.variance_pairing_cmTestFn hs hhc] at hcs
    have henergy := integral_norm_fderiv_sq_le hsupp hK
    have hle : (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * (K ^ 2 * V) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    have hcs' : (∑ i ∈ s, c i * ∫ x, φ i x * h x) ^ 2 ≤
        Var[fun w => ∑ i ∈ s, c i * hC w (φ i); P] * ((2 * Real.pi)⁻¹ * (K ^ 2 * V)) :=
      hcs.trans (mul_le_mul_of_nonneg_left hle hVar)
    have hA : 0 ≤ (2 * Real.pi)⁻¹ * (K ^ 2 * V) :=
      mul_nonneg (by positivity) (mul_nonneg (sq_nonneg K) ENNReal.toReal_nonneg)
    rw [mul_comm] at hcs'
    have := Real.abs_le_sqrt hcs'
    rwa [Real.sqrt_mul hA] at this
  -- pass to the limit `ε → 0`
  set M : ℝ := ∑ i ∈ s, |c i| * ∫ x, |φ i x| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (integral_nonneg fun x => abs_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (1 + M) := div_pos hε (by linarith)
  obtain ⟨h, hs, hhc, hsupp, hK, happ⟩ := hKR _ hε'
  have hgc : Continuous g := hg.continuous
  have hdiff : |(∑ i ∈ s, c i * ∫ x, φ i x * g x) - ∑ i ∈ s, c i * ∫ x, φ i x * h x| ≤
      ε / (1 + M) * M := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hM, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← mul_sub, abs_mul, abs_sub_comm]
    have := abs_integral_mul_sub_le (hφ i hi).1.continuous (hφ i hi).2.1 hs.continuous hgc (fun x => happ x)
    calc |c i| * |(∫ x, φ i x * h x) - ∫ x, φ i x * g x|
        ≤ |c i| * (ε / (1 + M) * ∫ x, |φ i x|) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = ε / (1 + M) * (|c i| * ∫ x, |φ i x|) := by ring
  have hεM : ε / (1 + M) * M ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have h1 := hsmooth h hs hhc hsupp hK
  have h2 := abs_sub_abs_le_abs_sub (∑ i ∈ s, c i * ∫ x, φ i x * g x)
    (∑ i ∈ s, c i * ∫ x, φ i x * h x)
  linarith

end Energy

section Shift

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Absolute continuity under a locally Lipschitz shift.** If `g` is locally Lipschitz with compact
support, `h` is a whole-plane Gaussian free field, and `S` is a measurable set of families of
pairings `(h, φ)` indexed by the mean-zero test functions supported in `D`, then `S` is null for
`(h, φ)_φ` as soon as it is null for `(h, φ)_φ + (∫ φ g)_φ`. -/
theorem IsWholePlaneGFF.measure_shift_eq_zero_of_locallyLipschitz [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : LocallyLipschitz g)
    (hc : HasCompactSupport g) (D : Set ℂ)
    {S : Set ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ)} (hS : MeasurableSet S)
    (h0 : P {w | (fun φ => hC w φ.1) ∈ S} = 0) :
    P {w | (fun φ => hC w φ.1 + ∫ x, φ.1 x * g x) ∈ S} = 0 := by
  classical
  let T := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}
  have hadm : ∀ φ : T, IsTestFunction univ φ.1 := fun φ => ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩
  let o : T → GFFObservable.Admissible := fun φ => ⟨.pairing φ.1, hadm φ⟩
  have hY : IsGaussianProcess (fun (φ : T) w => hC w φ.1) P := hh.isGaussianProcess.comp_right o
  have hYm : ∀ φ : T, Measurable fun w => hC w φ.1 := fun φ =>
    hh.measurable_pairing _ (hadm φ)
  have hcen : ∀ φ : T, P[fun w => hC w φ.1] = 0 := fun φ => hh.integral_eq_zero _ (o φ).2
  obtain ⟨C, -, hC'⟩ := hh.exists_abs_sum_integral_le (ι := T) hg hc
  refine measure_add_eq_zero_of_abs_comb_le (Y := fun (φ : T) w => hC w φ.1) hY hYm hcen
    (fun φ => ∫ x, φ.1 x * g x) (C := C) (fun σ => ?_) hS h0
  have hL : ∀ φ : T, MemLp (fun w => hC w φ.1) 2 P := fun φ =>
    (hh.isGaussianProcess.hasGaussianLaw_eval (o φ)).memLp_two
  have hZm : P[fun w => ∑ t ∈ σ.support, σ t * hC w t.1] = 0 := by
    rw [integral_finsetSum _ fun t _ => ((hL t).integrable one_le_two).const_mul (σ t)]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [integral_const_mul, hcen t, mul_zero]
  have hZaem : AEMeasurable (fun w => ∑ t ∈ σ.support, σ t * hC w t.1) P :=
    (Finset.measurable_sum _ fun t _ => (hYm t).const_mul (σ t)).aemeasurable
  rw [← variance_of_integral_eq_zero hZaem hZm]
  exact hC' σ.support (fun t => σ t) (fun t => t.1) (fun t _ => hadm t) (fun t _ => t.2.2)

end Shift

end LatticeProb.Gauss
