/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127E1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127D1
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# D127 N3, step 1: the truncation test functions `ψ_ε ∘ G_U ρ` (BP Lemma 1.37)

Packet P-127E of DEC-127 (§3, item N3). For a bounded open `U`, a smooth density `ρ ≥ 0` with
compact support in `U`, and `u = G_U ρ = ∫ G_U(·, y) ρ(y) dy`, we build for every `ε > 0` a test
function `f_ε = ψ_ε ∘ u ∈ C_c^∞(U)` with

* `E(f_ε) ≤ ∫ ρ f_ε` (energy bound), and
* `∫ ρ f_ε ≥ B(ρ, ρ) − 2ε ∫ ρ` (`B` the killed-Green form of S3D127B1).

Here `ψ_ε(s) = ∫₀ˢ h_ε`, `h_ε = smoothTransition(·/ε − 1)`: `ψ_ε = 0` on `(−∞, ε]`,
`0 ≤ ψ_ε' ≤ 1`, `ψ_ε(s) ≥ s − 2ε` for `s ≥ 0`. The energy bound is
`∫ |∇f_ε|² = ∫ ψ_ε'(u)² |∇u|² ≤ ∫ ψ_ε'(u) |∇u|² = ∫ ∇f_ε · ∇u = −∫ f_ε Δu = 2π ∫ f_ε ρ`
(Green's first identity `QuantumZipper.K3.integral_gradInner_eq_neg_integral_mul_laplacian`
applied to `f_ε` and a cutoff `χ u` with `χ = 1` near `supp f_ε`; `Δu = −2πρ` on `U` is
`laplacian_greenPot`, S3D127D1).

Source: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
§1.5, Lemma 1.37 (`literature/pdf/2404.16642.txt` l. 1640–1658: `Γ₀(ρ, ρ) = ∫|∇(G ρ)|²`). BP's
proof integrates by parts with `f = G_D ρ` directly; that `G_D ρ` is not compactly supported is
handled here by the truncation `ψ_ε ∘ u` (DEC-127 DV-D127-1, own elementary step).

Hypotheses taken from the running packets: `hN1` (N1, the form of S3D127B1), and for `u`:
`hcont : ContinuousOn u U` and `hsup` (closures of the superlevel sets `{x ∈ U | ε ≤ u x}` are
compact subsets of `U`, the form of `closure_superlevel_subset`, S3D127C4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology InnerProductSpace
open scoped Real Laplacian ContDiff

namespace LQGMetric.CONF.ZBM

open KilledHeat QuantumZipper QuantumZipper.K3

variable {U : Set ℂ} {c : ℂ} {R : ℝ}

/-! ## The truncation profile -/

/-- `h_ε(t) = smoothTransition(t/ε − 1)`: `0` on `(−∞, ε]`, `1` on `[2ε, ∞)` -/
def truncH (ε t : ℝ) : ℝ := Real.smoothTransition (t / ε - 1)

/-- `ψ_ε(s) = ∫₀ˢ h_ε` -/
def truncPsi (ε s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, truncH ε t

lemma continuous_truncH (ε : ℝ) : Continuous (truncH ε) :=
  Real.smoothTransition.continuous.comp ((continuous_id.div_const ε).sub continuous_const)

lemma contDiff_truncH (ε : ℝ) : ContDiff ℝ ∞ (truncH ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.div_const ε).sub contDiff_const)

lemma truncH_nonneg (ε t : ℝ) : 0 ≤ truncH ε t := Real.smoothTransition.nonneg _

lemma truncH_le_one (ε t : ℝ) : truncH ε t ≤ 1 := Real.smoothTransition.le_one _

lemma truncH_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε) : truncH ε t = 0 := by
  unfold truncH
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : t / ε ≤ 1 := (div_le_one hε).2 ht
  linarith

lemma truncH_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε ≤ t) : truncH ε t = 1 := by
  unfold truncH
  refine Real.smoothTransition.one_of_one_le ?_
  have : 2 ≤ t / ε := (le_div_iff₀ hε).2 ht
  linarith

lemma hasDerivAt_truncPsi (ε s : ℝ) : HasDerivAt (truncPsi ε) (truncH ε s) s :=
  ((continuous_truncH ε).integral_hasStrictDerivAt 0 s).hasDerivAt

lemma contDiff_truncPsi (ε : ℝ) : ContDiff ℝ ∞ (truncPsi ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_truncPsi ε s).differentiableAt, ?_⟩
  have : deriv (truncPsi ε) = truncH ε := funext fun s => (hasDerivAt_truncPsi ε s).deriv
  rw [this]
  exact contDiff_truncH ε

lemma truncPsi_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ ε) : truncPsi ε s = 0 := by
  unfold truncPsi
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
  · simp
  · refine truncH_eq_zero hε ?_
    rcases Set.mem_uIcc.1 ht with h | h
    · linarith [h.2]
    · linarith [h.2]

lemma truncPsi_ge {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : s - 2 * ε ≤ truncPsi ε s := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (truncH ε) volume a b :=
    fun a b => (continuous_truncH ε).intervalIntegrable a b
  rcases le_total s (2 * ε) with h | h
  · have : 0 ≤ truncPsi ε s :=
      intervalIntegral.integral_nonneg hs (fun t _ => truncH_nonneg ε t)
    linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * ε)) (hi (2 * ε) s)
    have h1 : 0 ≤ ∫ t in (0 : ℝ)..2 * ε, truncH ε t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => truncH_nonneg ε t)
    have h2 : ∫ t in (2 * ε)..s, truncH ε t = s - 2 * ε := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun t ht => ?_)]
      · simp
      · rw [Set.uIcc_of_le h] at ht
        exact truncH_eq_one hε ht.1
    unfold truncPsi
    linarith

/-! ## Gradients -/

lemma integrable_gradInner {f g : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) : Integrable (gradInner f g) := by
  have hf' := hf.continuous_fderiv one_ne_zero
  have hg' := hg.continuous_fderiv one_ne_zero
  have hcont : Continuous (gradInner f g) := by
    unfold gradInner
    exact ((hf'.clm_apply continuous_const).mul (hg'.clm_apply continuous_const)).add
      ((hf'.clm_apply continuous_const).mul (hg'.clm_apply continuous_const))
  refine hcont.integrable_of_hasCompactSupport (hfc.mono' fun x hx => ?_)
  by_contra hxs
  have : fderiv ℝ f x = 0 :=
    Function.notMem_support.1 fun h => hxs (support_fderiv_subset ℝ h)
  exact hx (by simp [gradInner, this])

/-! ## Step 1: the truncated test functions -/

/-- **D127 N3, step 1** (BP Lemma 1.37, via the truncation `ψ_ε ∘ G_U ρ`, DV-D127-1) -/
theorem exists_trunc_test (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hN1 : ∀ g ∈ QuantumZipper.zeroSpace U, ∀ y ∈ U,
      ∫ x, killedGreen U y x * Δ g x = -(2 * π) * g y)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ z, 0 ≤ ρ z)
    (hcont : ContinuousOn (fun x => ∫ y, killedGreen U x y * ρ y) U)
    (hsup : ∀ ε > 0,
      IsCompact (closure {x | x ∈ U ∧ ε ≤ ∫ y, killedGreen U x y * ρ y}) ∧
        closure {x | x ∈ U ∧ ε ≤ ∫ y, killedGreen U x y * ρ y} ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f ∈ QuantumZipper.zeroSpace U, QuantumZipper.dirichletEnergyOn U f ≤ ∫ y, ρ y * f y ∧
      killedGreenForm U ρ ρ - 2 * ε * ∫ y, ρ y ≤ ∫ y, ρ y * f y := by
  classical
  set u : ℂ → ℝ := fun x => ∫ y, killedGreen U x y * ρ y with hu_def
  have hu := contDiffOn_greenPot hU hUR hN1 hρ hρc hρU hcont
  have hΔ := laplacian_greenPot hU hUR hN1 hρ hρc hρU hcont
  obtain ⟨hKc, hKU⟩ := hsup ε hε
  set K := closure {x | x ∈ U ∧ ε ≤ u x} with hK_def
  set f : ℂ → ℝ := fun x => if x ∈ U then truncPsi ε (u x) else 0 with hf_def
  have hfK : ∀ x, x ∉ K → f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    intro x hx
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    simp only [hf_def]
    split_ifs with hyU
    · refine truncPsi_eq_zero hε ?_
      by_contra hlt
      exact hy (subset_closure ⟨hyU, (lt_of_not_ge hlt).le⟩)
    · rfl
  have hfU : ∀ x ∈ U, f =ᶠ[𝓝 x] (truncPsi ε ∘ u) := by
    intro x hx
    filter_upwards [hU.mem_nhds hx] with y hy
    simp [hf_def, hy]
  have hucd : ∀ x ∈ U, ContDiffAt ℝ ∞ u x := fun x hx => (hu x hx).contDiffAt (hU.mem_nhds hx)
  have hfs : ContDiff ℝ ∞ f := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact (((contDiff_truncPsi ε).contDiffAt).comp x (hucd x hx)).congr_of_eventuallyEq
        (hfU x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hfK x fun h => hx (hKU h))
  have htsK : tsupport f ⊆ K := by
    refine closure_minimal (fun x hx => ?_) isClosed_closure
    by_contra h
    exact hx (hfK x h).self_of_nhds
  have hfZ : f ∈ QuantumZipper.zeroSpace U :=
    ⟨hfs, hKc.of_isClosed_subset (isClosed_tsupport f) htsK, htsK.trans hKU⟩
  -- the cutoff `χ u`
  obtain ⟨χ, hχd, -, hχc, hχU, hχ1⟩ := FrozenMart.exists_cutoff_of_isCompact hKc hU hKU
  set L : ℂ → ℝ := fun x => χ x * u x with hL_def
  have hLU : ∀ x ∈ K, L =ᶠ[𝓝 x] u := by
    intro x hx
    filter_upwards [hχ1 x hx] with y hy
    simp only [hL_def]
    rw [hy, Pi.one_apply, one_mul]
  have hL : ContDiff ℝ 3 L := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact hχd.contDiffAt.mul ((hucd x hx).of_le (by simp))
    · have hev : L =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds
          (fun h => hx (hχU h))] with y hy
        simp [hL_def, image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hLc : HasCompactSupport L := hχc.mul_right
  -- Green's identity and the equation `Δu = −2πρ`
  have hG := integral_gradInner_eq_neg_integral_mul_laplacian (hfs.of_le (by simp))
    (hL.of_le (by norm_num)) hLc
  have hlap : ∫ x, f x * Δ L x = -(2 * π) * ∫ y, ρ y * f y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · show f x * Δ L x = -(2 * π) * (ρ x * f x)
      rw [(laplacian_congr_nhds (hLU x (htsK hx))).eq_of_nhds, hΔ x (hKU (htsK hx))]
      ring
    · show f x * Δ L x = -(2 * π) * (ρ x * f x)
      rw [image_eq_zero_of_notMem_tsupport hx]
      ring
  -- pointwise `|∇f|² ≤ ∇f · ∇L`
  have hpt : ∀ x, gradInner f f x ≤ gradInner f L x := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have hxU := hKU (htsK hx)
      have hdu : HasFDerivAt u (fderiv ℝ u x) x :=
        ((hucd x hxU).differentiableAt (by simp)).hasFDerivAt
      have hdf : HasFDerivAt f (truncH ε (u x) • fderiv ℝ u x) x :=
        ((hasDerivAt_truncPsi ε (u x)).comp_hasFDerivAt x hdu).congr_of_eventuallyEq (hfU x hxU)
      have hdL : fderiv ℝ L x = fderiv ℝ u x := (hLU x (htsK hx)).fderiv_eq
      simp only [gradInner, hdf.fderiv, hdL, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h0 := truncH_nonneg ε (u x)
      have h1 := truncH_le_one ε (u x)
      have hh : truncH ε (u x) * truncH ε (u x) ≤ truncH ε (u x) := by nlinarith
      have hab := add_nonneg (mul_self_nonneg (fderiv ℝ u x 1))
        (mul_self_nonneg (fderiv ℝ u x Complex.I))
      nlinarith [mul_le_mul_of_nonneg_right hh hab]
    · have : fderiv ℝ f x = 0 :=
        Function.notMem_support.1 fun h => hx (support_fderiv_subset ℝ h)
      simp [gradInner, this]
  have hEn : QuantumZipper.dirichletEnergyOn U f ≤ ∫ y, ρ y * f y := by
    unfold QuantumZipper.dirichletEnergyOn
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · simp only [norm_fderiv_sq_eq_gradInner]
      have hmono := integral_mono (integrable_gradInner (hfs.of_le (by simp)) hfZ.2.1
        (hfs.of_le (by simp))) (integrable_gradInner (hfs.of_le (by simp)) hfZ.2.1
        (hL.of_le (by norm_num))) hpt
      rw [hG, hlap] at hmono
      have hπ : 0 < (2 * π)⁻¹ := by positivity
      calc (2 * π)⁻¹ * ∫ z, gradInner f f z
          ≤ (2 * π)⁻¹ * -(-(2 * π) * ∫ y, ρ y * f y) := mul_le_mul_of_nonneg_left hmono hπ.le
        _ = ∫ y, ρ y * f y := by field_simp
    · have : z ∉ Function.support (fderiv ℝ f) :=
        fun h => hz (hfZ.2.2 (support_fderiv_subset ℝ h))
      rw [Function.notMem_support.1 this]
      simp
  refine ⟨f, hfZ, hEn, ?_⟩
  -- the lower bound `∫ ρ f ≥ ∫ ρ u − 2ε ∫ ρ`
  have hρcont : Continuous ρ := hρ.continuous
  obtain ⟨C, hC⟩ := hρcont.norm.bddAbove_range_of_hasCompactSupport hρc.norm
  have hCb : ∀ z, |ρ z| ≤ C := fun z => by simpa [Real.norm_eq_abs] using hC ⟨z, rfl⟩
  have hρi : Integrable ρ := hρcont.integrable_of_hasCompactSupport hρc
  have hB := killedGreenForm_eq_iter hU hR hUR hρcont.measurable hρcont.measurable hCb hρi hρi
  have hI := integrable_killedGreenForm hU hR hUR hρcont.measurable hρcont.measurable hCb hρi hρi
  rw [Measure.volume_eq_prod] at hI
  have hρu : Integrable (fun y => ρ y * u y) := by
    refine hI.integral_prod_left.congr (Eventually.of_forall fun y => ?_)
    simp only [hu_def]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hρf : Integrable (fun y => ρ y * f y) :=
    (hρcont.mul hfs.continuous).integrable_of_hasCompactSupport hρc.mul_right
  have hle : ∫ y, (ρ y * u y - 2 * ε * ρ y) ≤ ∫ y, ρ y * f y := by
    refine integral_mono (hρu.sub (hρi.const_mul _)) hρf fun y => ?_
    by_cases hy : y ∈ U
    · have hu0 : 0 ≤ u y :=
        integral_nonneg fun x => mul_nonneg (killedGreen_nonneg U y x) (hρ0 x)
      have := truncPsi_ge hε hu0
      simp only [hf_def, hy, if_true]
      nlinarith [mul_le_mul_of_nonneg_left this (hρ0 y)]
    · have : ρ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hρU h)
      simp [this]
  rw [integral_sub hρu (hρi.const_mul _), integral_const_mul] at hle
  rw [hB]
  exact hle

end LQGMetric.CONF.ZBM
