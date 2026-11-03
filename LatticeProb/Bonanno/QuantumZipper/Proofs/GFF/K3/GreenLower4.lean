/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenLower4 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# GFF-K3, node H5: the weak equation of the Green potential and its truncations

For a density `φ` with `GoodDens φ ε` and `σ = densMeas φ`, `u = gpot φ`:

* `weak_gpot`: `(2π)⁻¹ ∫ ⟪∇u, ∇ψ⟫ = ∫ ψ φ` for `ψ ∈ zeroSpace H` (the weak form of
  `-Δu = 2πφ` on `ℍ`). Proof: H2 (`integral_eq_kernelCov_greenDensity`, i.e. the Green
  representation `greenH_represent`, built on the planar Green formula F4) with Fubini packaged in
  `kernelCov`, then the integration by parts F3.
* `gpot_nonpos`: `u ≤ 0` on `{Im ≤ 0}`; `exists_gpot_lt`: `u < δ` far out.
* `trunc δ`: a smooth contraction `ℝ → ℝ`, `0` on `(-∞, δ]`, slope in `[0, 1]`,
  `t - 2δ ≤ trunc δ t`. Then `trunc δ ∘ u ∈ zeroSpace H` (`tpot_mem_zeroSpace`) and
  `E_H(trunc δ ∘ u) ≤ ∫ (trunc δ ∘ u) φ` (`energy_tpot_le`).
* `kernelCov_densMeas_le`: if `∫ f dσ ≤ C √E_H(f)` on `zeroSpace H`, then `B(σ, σ) ≤ C²`.

**Route (deviation from the blueprint's H5).** The blueprint cuts `u` off with `χn` and uses the
IMS identity plus the far-field bound `u ≤ C Im x/(1+|x|)²`. We instead compose `u` with the
smooth truncation `trunc δ`, as in the contraction principle for Dirichlet spaces (Adams–Hedberg,
*Function Spaces and Potential Theory*, 1996, §3.3, Thm 3.3.1: contractions `T` act on `W^{1,p}_0`
with the chain rule `∇(T∘u) = T'(u)∇u`). Testing the weak equation with `T∘u` gives
`E(T∘u) = (2π)⁻¹∫T'(u)²|∇u|² ≤ (2π)⁻¹∫T'(u)|∇u|² = ∫ T(u) dσ`; this combination is our own short
argument. It needs only `u → 0` at infinity (no decay rate), `u ≤ 0` below `ℝ`, and no gradient
bounds of cut-offs.
-/

noncomputable section

open MeasureTheory Filter Set Topology Real Laplacian
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper.K3

/-! ## The smooth truncation -/

lemma continuous_truncSlope (δ : ℝ) :
    Continuous fun x : ℝ => Real.smoothTransition (x / δ - 1) :=
  (Real.smoothTransition.contDiff (n := 0)).continuous.comp (by fun_prop)

/-- `trunc δ t = ∫₀ᵗ s(x/δ - 1) dx` with `s = Real.smoothTransition`. -/
def trunc (δ t : ℝ) : ℝ := ∫ x in (0 : ℝ)..t, Real.smoothTransition (x / δ - 1)

lemma hasDerivAt_trunc (δ t : ℝ) :
    HasDerivAt (trunc δ) (Real.smoothTransition (t / δ - 1)) t :=
  ((continuous_truncSlope δ).integral_hasStrictDerivAt 0 t).hasDerivAt

lemma contDiff_trunc (δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (trunc δ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_trunc δ t).differentiableAt, ?_⟩
  have e : deriv (trunc δ) = fun t => Real.smoothTransition (t / δ - 1) :=
    funext fun t => (hasDerivAt_trunc δ t).deriv
  rw [e]
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma trunc_eq_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) : trunc δ t = 0 := by
  unfold trunc
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
  · simp
  intro x hx
  have hx' : x ≤ δ :=
    (Set.mem_uIcc.mp hx).elim (fun h => h.2.trans ht) (fun h => h.2.trans hδ.le)
  apply Real.smoothTransition.zero_of_nonpos
  have : x / δ ≤ 1 := (div_le_one hδ).mpr hx'
  linarith

lemma trunc_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ trunc δ t := by
  rcases le_total t δ with h | h
  · rw [trunc_eq_zero hδ h]
  · exact intervalIntegral.integral_nonneg (hδ.le.trans h)
      fun x _ => Real.smoothTransition.nonneg _

lemma sub_le_trunc {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : t - 2 * δ ≤ trunc δ t := by
  rcases le_total t (2 * δ) with h | h
  · linarith [trunc_nonneg hδ t]
  · have hsplit : trunc δ t = trunc δ (2 * δ) +
        ∫ x in (2 * δ)..t, Real.smoothTransition (x / δ - 1) :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_truncSlope δ).intervalIntegrable 0 (2 * δ))
        ((continuous_truncSlope δ).intervalIntegrable (2 * δ) t)).symm
    have h1 : ∫ x in (2 * δ)..t, Real.smoothTransition (x / δ - 1) = t - 2 * δ := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp
      intro x hx
      rw [Set.uIcc_of_le h] at hx
      apply Real.smoothTransition.one_of_one_le
      have : 2 ≤ x / δ := (le_div_iff₀ hδ).mpr (by linarith [hx.1])
      linarith
    linarith [trunc_nonneg hδ (2 * δ)]

lemma fderiv_trunc_comp {u : ℂ → ℝ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (δ : ℝ) (v : ℂ) :
    fderiv ℝ (fun x => trunc δ (u x)) z v =
      Real.smoothTransition (u z / δ - 1) * fderiv ℝ u z v := by
  change fderiv ℝ (trunc δ ∘ u) z v = _
  rw [((hasDerivAt_trunc δ (u z)).comp_hasFDerivAt z hu.hasFDerivAt).fderiv]
  simp [smul_eq_mul]

/-! ## The weak equation -/

section Weak

variable {φ : ℂ → ℝ} {ε : ℝ}

/-- **H5 (weak equation).** `(2π)⁻¹ ∫ ⟪∇ gpot φ, ∇ψ⟫ = ∫ ψ φ` for `ψ ∈ zeroSpace H`. -/
theorem weak_gpot (hφ : GoodDens φ ε) {ψ : ℂ → ℝ} (hψ : ψ ∈ zeroSpace H) :
    (2 * π)⁻¹ * ∫ z, gradInner (gpot φ) ψ z = ∫ z, ψ z * φ z := by
  have hμ := isAdmissibleH_densMeas hφ
  obtain ⟨hP, hN⟩ := isAdmissibleH_testMeas_greenDensity hψ
  have hρc : Continuous (greenDensity ψ) :=
    continuous_greenDensity (contDiff_two_of_mem_zeroSpace hψ)
  have hρs := hasCompactSupport_greenDensity hψ.2.1
  have hgc : Continuous (gpot φ) := (contDiff_gpot hφ).continuous
  have key := integral_eq_kernelCov_greenDensity hμ hψ
  rw [ZeroReg.kernelCov_greenH_symm hμ hP, ZeroReg.kernelCov_greenH_symm hμ hN] at key
  have eP : kernelCov greenH (testMeasPos (greenDensity ψ)) (densMeas φ) =
      ∫ x, max (greenDensity ψ x) 0 * gpot φ x :=
    integral_testMeasPos_K3 hρc.measurable (gpot φ)
  have eN : kernelCov greenH (testMeasNeg (greenDensity ψ)) (densMeas φ) =
      ∫ x, max (-greenDensity ψ x) 0 * gpot φ x :=
    integral_testMeasNeg_K3 hρc.measurable (gpot φ)
  have i1 : Integrable fun x => max (greenDensity ψ x) 0 * gpot φ x :=
    ((hρc.max continuous_const).mul hgc).integrable_of_hasCompactSupport
      (hasCompactSupport_max_zero hρs).mul_right
  have i2 : Integrable fun x => max (-greenDensity ψ x) 0 * gpot φ x :=
    ((hρc.neg.max continuous_const).mul hgc).integrable_of_hasCompactSupport
      (hasCompactSupport_max_neg_zero hρs).mul_right
  rw [eP, eN, ← integral_sub i1 i2, integral_densMeas hφ] at key
  have e3 : ∀ x, max (greenDensity ψ x) 0 * gpot φ x - max (-greenDensity ψ x) 0 * gpot φ x =
      -(2 * π)⁻¹ * (gpot φ x * Δ ψ x) := by
    intro x
    rw [← sub_mul, max_sub_max_neg_K3]
    simp only [greenDensity]
    ring
  simp_rw [e3] at key
  rw [integral_const_mul] at key
  rw [integral_gradInner_eq_neg_integral_mul_laplacian
    ((contDiff_gpot hφ).of_le (by simp)) (contDiff_two_of_mem_zeroSpace hψ) hψ.2.1]
  simp_rw [mul_comm (ψ _) (φ _)]
  rw [key]
  ring

lemma ae_ne_volume_K3 (c : ℂ) : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ c :=
  ae_iff.2 (by simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton c)

lemma gpot_eq_integral (hφ : GoodDens φ ε) (x : ℂ) :
    gpot φ x = ∫ y, φ y * greenH x y :=
  integral_densMeas hφ (fun y => greenH x y)

/-- `gpot φ ≤ 0` on the closed lower half-plane. -/
lemma gpot_nonpos (hφ : GoodDens φ ε) {x : ℂ} (hx : x.im ≤ 0) : gpot φ x ≤ 0 := by
  rw [gpot_eq_integral hφ]
  refine integral_nonpos_of_ae ?_
  filter_upwards [ae_ne_volume_K3 (conj x)] with y hy
  show φ y * greenH x y ≤ 0
  by_cases h : φ y = 0
  · simp [h]
  · have hyH : (0 : ℝ) < y.im := hφ.tsupport_subset_H (subset_tsupport φ h)
    refine mul_nonpos_of_nonneg_of_nonpos (hφ.nonneg y) ?_
    have hxc : conj x ∈ Hbar := show (0 : ℝ) ≤ (conj x).im by simp; linarith
    have hne : x - conj y ≠ 0 := by
      intro h0
      apply hy
      rw [sub_eq_zero.mp h0, Complex.conj_conj]
    have h1 : 0 < ‖x - conj y‖ := norm_pos_iff.mpr hne
    have hle := norm_sub_le_norm_sub_conj hxc (show y ∈ Hbar from hyH.le)
    have ea : ‖conj x - y‖ = ‖x - conj y‖ := by
      rw [← Complex.norm_conj]; simp
    have eb : ‖conj x - conj y‖ = ‖x - y‖ := by
      rw [← map_sub, Complex.norm_conj]
    rw [ea, eb] at hle
    have := Real.log_le_log h1 hle
    simp only [greenH]
    linarith

/-- `gpot φ < δ` outside a large ball. -/
lemma exists_gpot_lt (hφ : GoodDens φ ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R, ∀ x : ℂ, R < ‖x‖ → gpot φ x < δ := by
  obtain ⟨R1, hR1⟩ := hφ.compact.isCompact.isBounded.subset_closedBall 0
  set R0 := max R1 0 with hR0
  have hR00 : 0 ≤ R0 := le_max_right _ _
  have hsupp : ∀ y, φ y ≠ 0 → ‖y‖ ≤ R0 := fun y hy => by
    have := hR1 (subset_tsupport φ hy)
    rw [mem_closedBall_zero_iff] at this
    exact this.trans (le_max_left _ _)
  have hφc := hφ.smooth.continuous
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.compact
  set M := ∫ y, φ y with hM
  have hM0 : 0 ≤ M := integral_nonneg hφ.nonneg
  refine ⟨R0 + 1 + 2 * R0 * M / δ, fun x hx => ?_⟩
  set m := ‖x‖ - R0 with hm
  have hq : 0 ≤ 2 * R0 * M / δ := by positivity
  have hm1 : 1 ≤ m := by linarith
  have hmpos : 0 < m := by linarith
  have hpt : ∀ y, φ y * greenH x y ≤ φ y * (2 * R0 / m) := by
    intro y
    by_cases h : φ y = 0
    · simp [h]
    refine mul_le_mul_of_nonneg_left ?_ (hφ.nonneg y)
    have hy := hsupp y h
    have hb : m ≤ ‖x - y‖ := by
      have := norm_sub_norm_le x y; linarith
    have ha : m ≤ ‖x - conj y‖ := by
      have := norm_sub_norm_le x (conj y); rw [Complex.norm_conj] at this; linarith
    have hab : ‖x - conj y‖ - ‖x - y‖ ≤ 2 * R0 := by
      have h1 := norm_sub_norm_le (x - conj y) (x - y)
      have h2 : x - conj y - (x - y) = y - conj y := by ring
      rw [h2] at h1
      have h3 := norm_sub_le y (conj y)
      rw [Complex.norm_conj] at h3
      linarith
    have hapos : 0 < ‖x - conj y‖ := by linarith
    have hbpos : 0 < ‖x - y‖ := by linarith
    have hlog : Real.log ‖x - conj y‖ - Real.log ‖x - y‖ ≤
        (‖x - conj y‖ - ‖x - y‖) / ‖x - y‖ := by
      rw [← Real.log_div hapos.ne' hbpos.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hapos hbpos)
      rw [sub_div, div_self hbpos.ne']
      exact this
    have hfrac : (‖x - conj y‖ - ‖x - y‖) / ‖x - y‖ ≤ 2 * R0 / m := by
      rw [div_le_div_iff₀ hbpos hmpos]
      nlinarith
    simp only [greenH]
    linarith
  have hint : Integrable fun y => φ y * greenH x y :=
    (integrable_greenH_mul hφc hφ.compact x).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  calc gpot φ x = ∫ y, φ y * greenH x y := gpot_eq_integral hφ x
    _ ≤ ∫ y, φ y * (2 * R0 / m) := integral_mono hint (hφi.mul_const _) hpt
    _ = M * (2 * R0 / m) := integral_mul_const _ _
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ hmpos]
      have : 2 * R0 * M / δ < m := by linarith
      rw [div_lt_iff₀ hδ] at this
      linarith

end Weak

end QuantumZipper.K3
