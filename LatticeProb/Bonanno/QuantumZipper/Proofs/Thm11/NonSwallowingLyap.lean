/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.NonSwallowingLyap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.LyapunovAlgebra
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.ForwardTamed
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# DF-1/DF-2, analytic layer: the Lyapunov function and its smooth cutoff

For `κ ∈ (0,4]` and `ε ≥ 0` let
`V(z) = −log|z| + ((4−κ)/4) g(arg z) + ε|z|²` (blueprint §1, issue 2, plus a quadratic term
that controls the exit through a large circle). We compute the Dynkin generator of the
`c`-tamed one-point motion `dZ = tamedZField c Z dt − √κ dB` on `V` where the taming is
inactive (`Im z ≥ c`):

  `L V = −(4−κ)/(2|z|²) + ε(κ + 4(x²−y²)/|z|²) ≤ ε(κ+4)`,

and we build a globally smooth function with bounded derivatives (up to order 3) that agrees
with `V` near a closed annular region `{ρ ≤ |z| ≤ R, Im z ≥ c}`.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace QuantumZipper
namespace NonSwallow

open Thm11Lyap FwdHolo

/-- The Lyapunov function `V(z) = −log|z| + ((4−κ)/4) g(arg z) + ε|z|²`. -/
def lyapV (κ ε : ℝ) (z : ℂ) : ℝ :=
  -(Complex.log z).re + (4 - κ) / 4 * gFun κ (Complex.log z).im
    + ε * (z.re * z.re + z.im * z.im)

theorem isOpen_upper : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr hz.ne')

theorem arg_mem_Ioo_of_im_pos {z : ℂ} (hz : 0 < z.im) : Complex.arg z ∈ Ioo 0 Real.pi := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hsin : 0 < Real.sin (Complex.arg z) := by
    rw [Complex.sin_arg]; exact div_pos hz (norm_pos_iff.2 hz0)
  refine ⟨?_, lt_of_le_of_ne (Complex.arg_le_pi z) (fun h => by simp [h] at hsin)⟩
  by_contra hc
  push Not at hc
  linarith [Real.sin_nonpos_of_nonpos_of_neg_pi_le hc (Complex.neg_pi_lt_arg z).le]

theorem log_im_mem_Ioo {z : ℂ} (hz : 0 < z.im) : (Complex.log z).im ∈ Ioo 0 Real.pi := by
  rw [Complex.log_im]; exact arg_mem_Ioo_of_im_pos hz

theorem contDiffAt_lyapV (κ ε : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lyapV κ ε) z := by
  have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.log z :=
    (Complex.contDiffAt_log (mem_slitPlane_of_im_pos hz)).restrict_scalars ℝ
  have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (Complex.log z).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z hlog
  have him : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (Complex.log z).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gFun κ) (Complex.log z).im :=
    (contDiffOn_gFun κ).contDiffAt (isOpen_Ioo.mem_nhds (log_im_mem_Ioo hz))
  have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  exact (hre.neg.add (contDiffAt_const.mul (hg.comp z him))).add
    (contDiffAt_const.mul ((hr.mul hr).add (hi.mul hi)).contDiffAt)

theorem hasFDerivAt_log_real {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt Complex.log
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) z⁻¹).restrictScalars ℝ) z :=
  ((Complex.hasStrictDerivAt_log (mem_slitPlane_of_im_pos hz)).hasDerivAt.hasFDerivAt).restrictScalars
    ℝ

theorem fderiv_lyapV_apply (κ ε : ℝ) {z : ℂ} (hz : 0 < z.im) (w : ℂ) :
    fderiv ℝ (lyapV κ ε) z w = -(w * z⁻¹).re
      + (4 - κ) / 4 * (gPrime κ (Complex.log z).im * (w * z⁻¹).im)
      + ε * (2 * z.re * w.re + 2 * z.im * w.im) := by
  have hlog := hasFDerivAt_log_real hz
  have h1 := Complex.reCLM.hasFDerivAt.comp z hlog
  have h2 := (hasDerivAt_gFun κ (log_im_mem_Ioo hz)).comp_hasFDerivAt z
    (Complex.imCLM.hasFDerivAt.comp z hlog)
  have hre : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have h : HasFDerivAt (lyapV κ ε) _ z :=
    (h1.neg.add (h2.const_mul ((4 - κ) / 4))).add
      (((hre.mul hre).add (him.mul him)).const_mul ε)
  rw [h.fderiv]
  simp [smul_eq_mul]
  ring

/-- The second derivative along a direction `e`, read off a line. -/
theorem iteratedFDeriv_two_eq_of_line {F : ℂ → ℝ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F z) (e : ℂ) {φ : ℝ → ℝ} {φ' : ℝ}
    (hφ : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ F (z + ((s : ℝ) : ℂ) * e) e = φ s)
    (hφ' : HasDerivAt φ φ' 0) :
    iteratedFDeriv ℝ 2 F z ![e, e] = φ' := by
  rw [Dynkin.iteratedFDeriv_two_vec]
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => z + (s : ℂ) * e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const e).const_add z
  have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ F (z + (s : ℂ) * e))
      (fderiv ℝ (fderiv ℝ F) z e) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have happ := hcomp.clm_apply (hasDerivAt_const (0 : ℝ) e)
  simp only [map_zero, add_zero] at happ
  exact (happ.congr_of_eventuallyEq (hφ.mono fun s hs => hs.symm)).unique hφ'

theorem tamedZField_of_le {c : ℝ} {z : ℂ} (hz : c ≤ z.im) : tamedZField c z = 2 / z := by
  simp [tamedZField, proj_of_le hz]

/-- **Generator of `V` for the tamed motion where the taming is inactive.** -/
theorem dynkinGen_lyapV {κ ε c : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : c ≤ z.im) (hz0 : 0 < z.im) :
    dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) (lyapV κ ε) z
      = -(4 - κ) / (2 * (z.re ^ 2 + z.im ^ 2))
        + ε * (κ + 4 * (z.re ^ 2 - z.im ^ 2) / (z.re ^ 2 + z.im ^ 2)) := by
  have hzne : z ≠ 0 := fun h => by simp [h] at hz0
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set q : ℝ → ℂ := fun s => z + (s : ℂ) * e with hqdef
  have hq : HasDerivAt q e 0 := by
    simpa [hqdef] using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const e).const_add z
  have hq0 : q 0 = z := by simp [hqdef]
  have hθ := log_im_mem_Ioo hz0
  -- derivative pieces along the line
  have hinv : HasDerivAt (fun s => (q s)⁻¹) (-(z ^ 2)⁻¹ * e) 0 :=
    (hasDerivAt_inv hzne).comp_of_eq 0 hq hq0.symm
  have hA : HasDerivAt (fun s => e * (q s)⁻¹) (e * (-(z ^ 2)⁻¹ * e)) 0 := hinv.const_mul e
  have hAre : HasDerivAt (fun s => (e * (q s)⁻¹).re) (e * (-(z ^ 2)⁻¹ * e)).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hA rfl
  have hAim : HasDerivAt (fun s => (e * (q s)⁻¹).im) (e * (-(z ^ 2)⁻¹ * e)).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hA rfl
  have hlogq : HasDerivAt (fun s => Complex.log (q s)) (e / q 0) 0 :=
    hq.clog_real (by rw [hq0]; exact mem_slitPlane_of_im_pos hz0)
  have hlogim : HasDerivAt (fun s => (Complex.log (q s)).im) (e / q 0).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hlogq rfl
  set g2 : ℝ := deriv (gPrime κ) (Complex.log z).im with hg2def
  have hg2 : HasDerivAt (gPrime κ) g2 (Complex.log z).im :=
    (hasDerivAt_gPrime κ hθ).differentiableAt.hasDerivAt
  have hG : HasDerivAt (fun s => gPrime κ (Complex.log (q s)).im) (g2 * (e / q 0).im) 0 :=
    hg2.comp_of_eq 0 hlogim (by rw [hq0])
  have hqre : HasDerivAt (fun s => (q s).re) e.re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hq rfl
  have hqim : HasDerivAt (fun s => (q s).im) e.im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hq rfl
  have hφ := (hAre.neg.add ((hG.mul hAim).const_mul ((4 - κ) / 4))).add
    ((((hqre.const_mul 2).mul_const e.re).add ((hqim.const_mul 2).mul_const e.im)).const_mul ε)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ (lyapV κ ε) (z + ((s : ℝ) : ℂ) * e) e =
      (fun s => -(e * (q s)⁻¹).re
        + (4 - κ) / 4 * (gPrime κ (Complex.log (q s)).im * (e * (q s)⁻¹).im)
        + ε * (2 * (q s).re * e.re + 2 * (q s).im * e.im)) s := by
    have hmem : {w : ℂ | 0 < w.im} ∈ 𝓝 (q 0) := isOpen_upper.mem_nhds (by rw [hq0]; exact hz0)
    filter_upwards [hq.continuousAt.preimage_mem_nhds hmem] with s hs
    exact fderiv_lyapV_apply κ ε hs e
  have hC2 : ContDiffAt ℝ 2 (lyapV κ ε) z := (contDiffAt_lyapV κ ε hz0).of_le (by
    exact WithTop.coe_le_coe.2 le_top)
  unfold dynkinGen
  rw [tamedZField_of_le hz, fderiv_lyapV_apply κ ε hz0,
    iteratedFDeriv_two_eq_of_line hC2 e hev hφ]
  simp only [hq0, he, pow_two, mul_inv, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.re_ofNat,
    Complex.im_ofNat]
  -- the ODE of `g` at `θ = arg z`
  have hode := gFun_ode hκ.ne' (arg_mem_Ioo_of_im_pos hz0)
  rw [Complex.sin_arg, Complex.cos_arg hzne] at hode
  rw [← Complex.log_im] at hode
  rw [← hg2def] at hode
  set g1 : ℝ := gPrime κ (Complex.log z).im with hg1def
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnp : 0 < ‖z‖ := norm_pos_iff.2 hzne
  have key : κ / 2 * z.im ^ 2 * g2 + (κ - 4) * z.re * z.im * g1 = -4 * z.im ^ 2 := by
    have h' : κ / 2 * (z.im / ‖z‖) ^ 2 * g2 + (κ - 4) * (z.im / ‖z‖) * (z.re / ‖z‖) * g1
        = -4 * (z.im / ‖z‖) ^ 2 := hode
    field_simp at h'
    linear_combination (z.im / 2) * h'
  have hr2 : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  have hg2e : g2 = (-4 * z.im ^ 2 - (κ - 4) * z.re * z.im * g1) / (κ / 2 * z.im ^ 2) := by
    rw [eq_div_iff (by positivity)]
    linear_combination key
  rw [hg2e]
  clear_value g1 g2
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = κ := ⟨_, Real.sqrt_nonneg κ, Real.sq_sqrt hκ.le⟩
  rw [Real.sqrt_sq hs]
  have hs0 : s ≠ 0 := by rintro rfl; simp at hκ
  have hy0 : z.im ≠ 0 := hz0.ne'
  have hr0 : z.re * z.re + z.im * z.im ≠ 0 := by nlinarith
  field_simp
  ring

theorem dynkinGen_congr {b : ℂ → ℂ} {e : ℂ} {F G : ℂ → ℝ} {z : ℂ} (h : F =ᶠ[𝓝 z] G) :
    dynkinGen b e F z = dynkinGen b e G z := by
  unfold dynkinGen
  rw [h.fderiv_eq, (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h 2).eq_of_nhds]

/-- `L V ≤ −(4−κ)/(2|z|²) + ε(κ+4)` where the taming is inactive. -/
theorem dynkinGen_lyapV_le {κ ε c : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {z : ℂ} (hz : c ≤ z.im)
    (hz0 : 0 < z.im) :
    dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) (lyapV κ ε) z
      ≤ -(4 - κ) / (2 * ‖z‖ ^ 2) + ε * (κ + 4) := by
  rw [dynkinGen_lyapV hκ hz hz0]
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hn2]
  have hr2 : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  have h1 : 4 * (z.re ^ 2 - z.im ^ 2) / (z.re ^ 2 + z.im ^ 2) ≤ 4 := by
    rw [div_le_iff₀ hr2]; nlinarith [sq_nonneg z.im]
  nlinarith

theorem lyapV_eq (κ ε : ℝ) (z : ℂ) :
    lyapV κ ε z = -Real.log ‖z‖ + (4 - κ) / 4 * gFun κ (Complex.arg z) + ε * ‖z‖ ^ 2 := by
  rw [lyapV, Complex.log_re, Complex.log_im, Complex.sq_norm, Complex.normSq_apply]

theorem abs_lyapV_sub_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (ε : ℝ) {z : ℂ} (hz : 0 < z.im) :
    |lyapV κ ε z - (-Real.log ‖z‖ + ε * ‖z‖ ^ 2)| ≤ (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) := by
  rw [lyapV_eq]
  have hg := abs_gFun_le hκ hκ4 (arg_mem_Ioo_of_im_pos hz)
  have e : -Real.log ‖z‖ + (4 - κ) / 4 * gFun κ (Complex.arg z) + ε * ‖z‖ ^ 2
      - (-Real.log ‖z‖ + ε * ‖z‖ ^ 2) = (4 - κ) / 4 * gFun κ (Complex.arg z) := by ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (4 - κ) / 4)]
  exact mul_le_mul_of_nonneg_left hg (by linarith)

/-! ### Regions and the smooth cutoff -/

/-- Closed annular region `{r₁ ≤ |z| ≤ r₂, Im z ≥ c}`. -/
def annReg (r1 r2 c : ℝ) : Set ℂ := {z | r1 ≤ ‖z‖ ∧ ‖z‖ ≤ r2 ∧ c ≤ z.im}

/-- Open annular region `{r₁ < |z| < r₂, Im z > c}`. -/
def annOpen (r1 r2 c : ℝ) : Set ℂ := {z | r1 < ‖z‖ ∧ ‖z‖ < r2 ∧ c < z.im}

theorem isClosed_annReg (r1 r2 c : ℝ) : IsClosed (annReg r1 r2 c) :=
  (isClosed_le continuous_const continuous_norm).inter
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im))

theorem isOpen_annOpen (r1 r2 c : ℝ) : IsOpen (annOpen r1 r2 c) :=
  (isOpen_lt continuous_const continuous_norm).inter
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

theorem isCompact_annReg (r1 r2 c : ℝ) : IsCompact (annReg r1 r2 c) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_annReg r1 r2 c)
    ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r2)).subset fun z hz => by
      rw [mem_closedBall_zero_iff]; exact hz.2.1)

theorem annReg_subset_annOpen {r1 r2 c r1' r2' c' : ℝ} (h1 : r1' < r1) (h2 : r2 < r2')
    (h3 : c' < c) : annReg r1 r2 c ⊆ annOpen r1' r2' c' :=
  fun _ hz => ⟨h1.trans_le hz.1, hz.2.1.trans_lt h2, h3.trans_le hz.2.2⟩

theorem annOpen_subset_annReg {r1 r2 c : ℝ} : annOpen r1 r2 c ⊆ annReg r1 r2 c :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

theorem three_le_smooth : (3 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.2 le_top

/-- **The cutoff Lyapunov function.** A `C³` function with bounded derivatives (up to order 3)
that agrees with `V` near the closed region `{ρ ≤ |z| ≤ R, Im z ≥ c}`. -/
theorem exists_lyap_cutoff (κ ε : ℝ) {ρ R c : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hc : 0 < c) :
    ∃ F : ℂ → ℝ, ∃ C : ℝ, ContDiff ℝ 3 F ∧
      (∀ x, |F x| ≤ C ∧ ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) ∧
      ∀ z ∈ annReg ρ R c, F =ᶠ[𝓝 z] lyapV κ ε := by
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (isOpen_annOpen (ρ / 4) (4 * R) (c / 4)) (isClosed_annReg (ρ / 2) (2 * R) (c / 2))
      (annReg_subset_annOpen (by linarith) (by linarith) (by linarith))
  have hts : tsupport χ ⊆ annReg (ρ / 4) (4 * R) (c / 4) := by
    rw [tsupport, hχs]; exact closure_minimal annOpen_subset_annReg (isClosed_annReg _ _ _)
  have hχc : HasCompactSupport χ :=
    (isCompact_annReg _ _ _).of_isClosed_subset (isClosed_tsupport χ) hts
  set F : ℂ → ℝ := χ * lyapV κ ε with hFdef
  have hFs : ContDiff ℝ 3 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < x.im
    · exact (hχ.contDiffAt.of_le three_le_smooth).mul
        ((contDiffAt_lyapV κ ε hx).of_le three_le_smooth)
    · have hxt : x ∉ tsupport χ := fun h => hx (by have := (hts h).2.2; linarith)
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hxt
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (h0.mono fun y hy => by simp [hFdef, hy])
  have hFc : HasCompactSupport F := hχc.mul_right
  obtain ⟨C0, h0⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  obtain ⟨C1, h1⟩ := (hFs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨C2, h2⟩ := (hFs.continuous_iteratedFDeriv (m := 2) (by norm_num)).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 2)
  obtain ⟨C3, h3⟩ := (hFs.continuous_iteratedFDeriv (m := 3) le_rfl).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 3)
  refine ⟨F, max (max C0 C1) (max C2 C3), hFs, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (h0 x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h1 x).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro z hz
    have hmem : annOpen (ρ / 2) (2 * R) (c / 2) ∈ 𝓝 z :=
      (isOpen_annOpen _ _ _).mem_nhds
        (annReg_subset_annOpen (by linarith) (by linarith) (by linarith) hz)
    filter_upwards [hmem] with y hy
    have : χ y = 1 := (hχ1 y).1 (annOpen_subset_annReg hy)
    simp [hFdef, this]

end NonSwallow
end QuantumZipper
