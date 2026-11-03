/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.MixedM7D1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm

/-!
# K3-mixed M7-a3, half-disc covariance, step D1: smooth even reflections

For the half-disc `U = ball t r ∩ H` (free on the diameter, zero on the arc) the covariance is
obtained by reflecting to the full disc `B = ball t r` with zero boundary values. This file
provides the smooth even "folds" used to transport a test function `f` of `U` to test functions
of `B`: with `evAbs ε y = √(y² + ε²) − ε` (a smooth even approximation of `|y|`),

  `evFold ε z = Re z + i · evAbs ε (Im z)`,  `g_ε = f ∘ evFold ε`,

`g_ε` is smooth and even (`g_ε ∘ conj = g_ε`), `g_ε → f` on `Hbar`, and
`‖∇g_ε(z)‖² = (Df(w) 1)² + (evAbs' ε y · Df(w) I)²` with `w = evFold ε z`, which tends to
`‖∇f(z)‖²` on `H` with the uniform bound `2 sup ‖Df‖²`.

Own elementary construction (the reflection principle for the Neumann problem is classical; the
smooth even fold replaces the usual mollification of the even extension, which is not available
in mathlib at this pin).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate

namespace QuantumZipper.K3

/-- Smooth even approximation of `|y|`. -/
def evAbs (ε y : ℝ) : ℝ := √(y ^ 2 + ε ^ 2) - ε

/-- The derivative of `evAbs ε`. -/
def evAbs' (ε y : ℝ) : ℝ := y / √(y ^ 2 + ε ^ 2)

/-- Smooth even fold of `ℂ` onto (approximately) `Hbar`. -/
def evFold (ε : ℝ) (z : ℂ) : ℂ := (z.re : ℂ) + (evAbs ε z.im) • Complex.I

theorem evAbs_nonneg_m7d {ε : ℝ} (_hε : 0 ≤ ε) (y : ℝ) : 0 ≤ evAbs ε y := by
  unfold evAbs
  have : ε ≤ √(y ^ 2 + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg y])
  linarith

theorem evAbs_le_abs_m7d {ε : ℝ} (hε : 0 ≤ ε) (y : ℝ) : evAbs ε y ≤ |y| := by
  unfold evAbs
  have : √(y ^ 2 + ε ^ 2) ≤ |y| + ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs y, abs_nonneg y]
  linarith

theorem abs_sub_le_evAbs_m7d (ε y : ℝ) : |y| - ε ≤ evAbs ε y := by
  unfold evAbs
  have : |y| ≤ √(y ^ 2 + ε ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  linarith

theorem evAbs_neg_m7d (ε y : ℝ) : evAbs ε (-y) = evAbs ε y := by simp [evAbs]

theorem evAbs_zero_m7d (y : ℝ) : evAbs 0 y = |y| := by
  simp [evAbs, Real.sqrt_sq_eq_abs]

theorem continuous_evAbs_eps_m7d (y : ℝ) : Continuous fun ε => evAbs ε y := by
  unfold evAbs; fun_prop

theorem contDiff_evAbs_m7d {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evAbs ε) := by
  unfold evAbs
  refine (ContDiff.sqrt (by fun_prop) fun y => ?_).sub contDiff_const
  positivity

theorem hasDerivAt_evAbs_m7d {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (evAbs ε) (evAbs' ε y) y := by
  have hpos : 0 < y ^ 2 + ε ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const (ε ^ 2)
  have h2 := (h1.sqrt hpos.ne').sub_const ε
  have h3 : evAbs' ε y = 2 * y / (2 * √(y ^ 2 + ε ^ 2)) := by
    unfold evAbs'; rw [mul_div_mul_left _ _ (two_ne_zero' ℝ)]
  rw [h3]; exact h2

theorem abs_evAbs'_le_m7d (ε y : ℝ) : |evAbs' ε y| ≤ 1 := by
  unfold evAbs'
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (y ^ 2 + ε ^ 2)) with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · rw [div_le_one h, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

theorem evAbs'_neg_m7d (ε y : ℝ) : evAbs' ε (-y) = -evAbs' ε y := by
  simp [evAbs', neg_div]

theorem tendsto_evAbs'_m7d {y : ℝ} (hy : 0 < y) :
    Tendsto (fun ε => evAbs' ε y) (𝓝 0) (𝓝 1) := by
  have hc : Continuous fun ε : ℝ => evAbs' ε y := by
    unfold evAbs'
    refine continuous_const.div (by fun_prop) fun ε => ?_
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  have h0 : evAbs' 0 y = 1 := by
    simp [evAbs', Real.sqrt_sq hy.le, hy.ne']
  simpa [h0] using hc.tendsto 0

/-! ## The fold -/

theorem evFold_re_m7d (ε : ℝ) (z : ℂ) : (evFold ε z).re = z.re := by simp [evFold]

theorem evFold_im_m7d (ε : ℝ) (z : ℂ) : (evFold ε z).im = evAbs ε z.im := by simp [evFold]

theorem evFold_conj_m7d (ε : ℝ) (z : ℂ) : evFold ε (conj z) = evFold ε z := by
  simp [evFold, evAbs_neg_m7d]

theorem evFold_zero_of_mem_Hbar_m7d {z : ℂ} (hz : z ∈ Hbar) : evFold 0 z = z := by
  have hz' : 0 ≤ z.im := hz
  apply Complex.ext <;> simp [evFold, evAbs_zero_m7d, abs_of_nonneg hz']

theorem continuous_evFold_eps_m7d (z : ℂ) : Continuous fun ε => evFold ε z := by
  unfold evFold
  exact continuous_const.add ((continuous_evAbs_eps_m7d _).smul continuous_const)

theorem contDiff_evFold_m7d {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evFold ε) := by
  unfold evFold
  refine (Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff).add ?_
  exact ((contDiff_evAbs_m7d hε).comp Complex.imCLM.contDiff).smul contDiff_const

theorem evFold_mem_Hbar_m7d {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) : evFold ε z ∈ Hbar := by
  show 0 ≤ (evFold ε z).im
  rw [evFold_im_m7d]; exact evAbs_nonneg_m7d hε _

theorem sq_norm_sub_ofReal_m7d (w : ℂ) (t : ℝ) : ‖w - t‖ ^ 2 = (w.re - t) ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

theorem norm_evFold_sub_le_m7d {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) (t : ℝ) :
    ‖evFold ε z - t‖ ≤ ‖z - t‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [sq_norm_sub_ofReal_m7d, sq_norm_sub_ofReal_m7d, evFold_re_m7d, evFold_im_m7d]
  have h1 := evAbs_le_abs_m7d hε z.im
  have h2 := evAbs_nonneg_m7d hε z.im
  have h3 : evAbs ε z.im ^ 2 ≤ |z.im| ^ 2 := pow_le_pow_left₀ h2 h1 2
  rw [sq_abs] at h3
  linarith

theorem norm_sub_le_evFold_m7d {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) (t : ℝ) :
    ‖z - t‖ ≤ ‖evFold ε z - t‖ + ε := by
  set p : ℂ := (z.re : ℂ) + (|z.im| : ℝ) • Complex.I
  have hp : ‖p - t‖ = ‖z - t‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [sq_norm_sub_ofReal_m7d, sq_norm_sub_ofReal_m7d]
    simp [p, sq_abs]
  have hpw : ‖p - evFold ε z‖ ≤ ε := by
    have : p - evFold ε z = ((|z.im| - evAbs ε z.im : ℝ) : ℂ) * Complex.I := by
      simp only [p, evFold, Complex.real_smul]; push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor
    · linarith [evAbs_le_abs_m7d hε z.im]
    · linarith [abs_sub_le_evAbs_m7d ε z.im]
  calc ‖z - t‖ = ‖p - t‖ := hp.symm
    _ ≤ ‖p - evFold ε z‖ + ‖evFold ε z - t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖evFold ε z - t‖ + ε := by linarith

/-- The derivative of the fold. -/
theorem hasFDerivAt_evFold_m7d {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    HasFDerivAt (evFold ε) (Complex.ofRealCLM.comp Complex.reCLM +
      (evAbs' ε z.im • Complex.imCLM).smulRight Complex.I) z := by
  unfold evFold
  refine (Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.add ?_
  exact ((hasDerivAt_evAbs_m7d hε z.im).comp_hasFDerivAt z
    Complex.imCLM.hasFDerivAt).smul_const Complex.I

/-- The squared gradient of `f ∘ evFold ε`. -/
theorem sq_norm_fderiv_comp_evFold_m7d {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℝ}
    (hf : Differentiable ℝ f) (z : ℂ) :
    ‖fderiv ℝ (f ∘ evFold ε) z‖ ^ 2 = (fderiv ℝ f (evFold ε z) 1) ^ 2 +
      (evAbs' ε z.im * fderiv ℝ f (evFold ε z) Complex.I) ^ 2 := by
  rw [((hf _).hasFDerivAt.comp z (hasFDerivAt_evFold_m7d hε z)).fderiv, norm_sq_clm_complex]
  simp
  rw [show ((evAbs' ε z.im : ℂ) * Complex.I) = evAbs' ε z.im • Complex.I from
    (Complex.real_smul).symm, map_smul, smul_eq_mul]

end QuantumZipper.K3
