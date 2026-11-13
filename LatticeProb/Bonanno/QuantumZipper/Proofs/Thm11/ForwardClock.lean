/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.ForwardClock at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardFlow
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardHolo
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Blueprint FD-1, FD-2, FD-3: clock identities, swallowing, two-point kernel

For the forward centered Loewner flow `f_t = fwdMap W t`:

* **FD-1** (clock identities): with the clock `S_t(z) = ∫₀ᵗ |f_s z|⁻² ds` (`fwdClock`),
  `Im f_t z = Im z · e^{-2 S_t}`, `(Im f_t z)² ≥ (Im z)² - 4t`,
  `|f_T'(z)| = e^{Re logDerivFwd} ≥ Im f_T z / Im z`, `|Im logDerivFwd| ≤ 2 S_t`, and the log
  conformal radius `C_t = log Im f_t - Re logDerivFwd` (`fwdLogCR`) has derivative
  `-4 (Im f_t)² / |f_t|⁴`.
* **FD-2** (swallowing): at a finite swallowing time `σ`, `inf_{t<σ} Im f_t z = 0` and the clock
  is unbounded; characterisations of `fwdHull`.
* **FD-3** (two-point kernel): `d/dt G(f_t a, f_t b) = -Im(2/f_t a) Im(2/f_t b)`, so
  `0 ≤ G_t ≤ G`, `G_t` is nonincreasing, `G - G_T = ∫₀ᵀ Im(2/f a) Im(2/f b)`, and this kernel is
  positive semidefinite.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper

namespace FwdClock

variable {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}

/-- The clock `S_t(z) = ∫₀ᵗ |f_s(z)|⁻² ds`. -/
def fwdClock (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℝ := ∫ s in (0 : ℝ)..t, 1 / ‖fwdMap W s z‖ ^ 2

/-- The log conformal radius `C_t(z) = log Im f_t(z) - Re logDerivFwd`. -/
def fwdLogCR (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  Real.log (fwdMap W t z).im - (logDerivFwd W t z).re

/-! ## Calculus helpers -/

lemma hasDerivWithinAt_integral_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} (hg : ContinuousOn g (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun τ => ∫ r in (0 : ℝ)..τ, g r) (g t) (Icc 0 T) t := by
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hint : IntervalIntegrable g volume 0 t :=
    (hg.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg t ht)

lemma monotoneOn_Icc_of_hasDerivWithinAt {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (h : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ f' t) : MonotoneOn f (Icc 0 T) := by
  have hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt f (f' t) t := fun t ht =>
    (hf t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    (fun t ht => (hf t ht).continuousWithinAt)
  · rw [interior_Icc]; exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro t ht; rw [(hd t ht).deriv]; exact h t ht

lemma antitoneOn_Icc_of_hasDerivWithinAt {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (h : ∀ t ∈ Ioo (0 : ℝ) T, f' t ≤ 0) : AntitoneOn f (Icc 0 T) := by
  have hm := monotoneOn_Icc_of_hasDerivWithinAt (f := fun t => -f t) (f' := fun t => -f' t)
    (fun t ht => (hf t ht).neg) (fun t ht => by linarith [h t ht])
  intro a ha b hb hab
  exact neg_le_neg_iff.mp (hm ha hb hab)

lemma hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℂ} {f' : ℂ} {a b t : ℝ}
    (h : HasDerivWithinAt f f' (Icc a b) t) (ht : t ∈ Ico a b) :
    HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

lemma hasDerivWithinAt_log_norm {p : ℝ → ℂ} {p' : ℂ} {s : Set ℝ} {t : ℝ}
    (hp : HasDerivWithinAt p p' s t) (h0 : p t ≠ 0) :
    HasDerivWithinAt (fun r => Real.log ‖p r‖) ((p' / p t).re) s t := by
  have hpos : ‖p t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
  have h3 := (hp.norm_sq.log hpos).const_mul (1 / 2 : ℝ)
  have hf : (fun r => Real.log ‖p r‖) = fun y => 1 / 2 * Real.log (‖p y‖ ^ 2) := by
    funext r; rw [Real.log_pow]; push_cast; ring
  rw [hf]
  refine h3.congr_deriv ?_
  have hn : Complex.normSq (p t) ≠ 0 := by rwa [← Complex.sq_norm]
  rw [Complex.inner, Complex.div_re, Complex.sq_norm]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-! ## Algebra -/

lemma im_two_div (w : ℂ) : (2 / w).im = -2 * w.im / ‖w‖ ^ 2 := by
  rw [Complex.div_im, Complex.sq_norm]; simp; ring

lemma norm_two_div_sq (w : ℂ) : ‖2 / w ^ 2‖ = 2 / ‖w‖ ^ 2 := by
  rw [norm_div, norm_pow, Complex.norm_two]

lemma logCR_alg (w : ℂ) (hy : 0 < w.im) :
    (2 / w).im / w.im + (2 / w ^ 2).re = -4 * w.im ^ 2 / ‖w‖ ^ 4 := by
  have hn : ‖w‖ ^ 4 = (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    rw [show ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 by ring, Complex.sq_norm, Complex.normSq_apply]; ring
  have hd : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  have e1 : (2 / w).im = -2 * w.im / (w.re ^ 2 + w.im ^ 2) := by
    rw [im_two_div, Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : (2 / w ^ 2).re = 2 * (w.re ^ 2 - w.im ^ 2) / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have hd' : w.re * w.re + w.im * w.im ≠ 0 := by nlinarith
    rw [Complex.div_re, map_pow, Complex.normSq_apply]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
    field_simp
    ring
  rw [hn, e1, e2]
  field_simp
  ring

lemma kernel_alg {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) (hxy : x ≠ y) :
    ((2 / x - conj (2 / y)) / (x - conj y)).re - ((2 / x - 2 / y) / (x - y)).re =
      -((2 / x).im * (2 / y).im) := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
  have hcy0 : conj y ≠ 0 := by rwa [map_ne_zero]
  have hq : x - conj y ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have hp : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have e1 : (2 / x - conj (2 / y)) / (x - conj y) = -(2 / x) * conj (2 / y) / 2 := by
    rw [map_div₀, map_ofNat]
    field_simp
    ring
  have e2 : (2 / x - 2 / y) / (x - y) = -(2 / x) * (2 / y) / 2 := by
    field_simp
    ring
  rw [e1, e2]
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-! ## Solutions -/

/-- `s ↦ fwdMap W s z` is itself a forward solution on `[0,T]` when one exists. -/
lemma isForwardSol_fwdMap (hW : Continuous W) (hz : 0 < z.im) (hu : IsForwardSol W z T u) :
    IsForwardSol W z T (fun s => fwdMap W s z) := by
  refine ⟨hu.1.congr fun s hs => fwdMap_eq hW hz hu hs, fun t ht => ?_⟩
  show fwdMap W t z ≠ 0 ∧ fwdMap W t z = z - W t + ∫ s in (0 : ℝ)..t, 2 / fwdMap W s z
  rw [fwdMap_eq hW hz hu ht]
  refine ⟨(hu.2 t ht).1, ?_⟩
  rw [(hu.2 t ht).2]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  simp only [fwdMap_eq hW hz hu ⟨hs.1, hs.2.trans ht.2⟩]

lemma sol_im_pos (hW : Continuous W) (hz : 0 < z.im) (hu : IsForwardSol W z T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : 0 < (u t).im := (im_isForwardSol_le hW hz hu).2 t ht

lemma sol_hasDerivWithinAt_im (hu : IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => (u s).im) ((2 / u t).im) (Icc 0 T) t := by
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (FwdHolo.hasDerivWithinAt_shift hu ht)
  simpa [Function.comp_def] using this

lemma sol_contOn_inv_sq (hu : IsForwardSol W z T u) :
    ContinuousOn (fun s => 1 / ‖u s‖ ^ 2) (Icc 0 T) :=
  continuousOn_const.div (hu.1.norm.pow 2) fun s hs =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu.2 s hs).1)

lemma sol_contOn_two_div_sq (hu : IsForwardSol W z T u) :
    ContinuousOn (fun s => 2 / u s ^ 2) (Icc 0 T) :=
  continuousOn_const.div (hu.1.pow 2) fun s hs => pow_ne_zero 2 (hu.2 s hs).1

/-! ## FD-1: clock identities -/

lemma sol_im_eq_clock (hW : Continuous W) (hz : 0 < z.im) (hu : IsForwardSol W z T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    (u t).im = z.im * Real.exp (-2 * ∫ s in (0 : ℝ)..t, 1 / ‖u s‖ ^ 2) := by
  set S : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, 1 / ‖u s‖ ^ 2 with hS_def
  have hE : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => (u s).im * Real.exp (2 * S s))
      0 (Icc 0 T) τ := by
    intro τ hτ
    have h1 := sol_hasDerivWithinAt_im hu hτ
    have h2 := ((hasDerivWithinAt_integral_Icc (sol_contOn_inv_sq hu) hτ).const_mul 2).exp
    refine HasDerivWithinAt.congr_deriv (h1.mul h2) ?_
    have hn : ‖u τ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu.2 τ hτ).1)
    rw [im_two_div]
    field_simp
    ring
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hmono := monotoneOn_Icc_of_hasDerivWithinAt hE (fun _ _ => le_rfl)
  have hanti := antitoneOn_Icc_of_hasDerivWithinAt hE (fun _ _ => le_rfl)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have heq : (u t).im * Real.exp (2 * S t) = (u 0).im * Real.exp (2 * S 0) :=
    le_antisymm (hanti h0 ht ht.1) (hmono h0 ht ht.1)
  have hS0 : S 0 = 0 := intervalIntegral.integral_same
  have hu0 : (u 0).im = z.im := by rw [FwdHolo.sol_zero hu hT]; simp
  rw [hS0, hu0, mul_zero, Real.exp_zero, mul_one] at heq
  show (u t).im = z.im * Real.exp (-2 * S t)
  rw [← heq, mul_assoc, ← Real.exp_add]; ring_nf; simp

/-- **FD-1 (a).** `Im f_t(z) = Im z · e^{-2 S_t(z)}`. -/
theorem im_fwdMap_eq_clock (hW : Continuous W) (hz : 0 < z.im)
    (hsol : ∃ u, IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fwdMap W t z).im = z.im * Real.exp (-2 * fwdClock W t z) := by
  obtain ⟨u, hu⟩ := hsol
  exact sol_im_eq_clock hW hz (isForwardSol_fwdMap hW hz hu) ht

/-- **FD-1 (b).** `|f_T'(z)| = e^{Re logDerivFwd}`. -/
theorem norm_deriv_fwdMap (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    ‖deriv (fwdMap W T) z‖ = Real.exp (logDerivFwd W T z).re := by
  rw [(FwdHolo.hasDerivAt_fwdMap hW hT hz).deriv, Complex.norm_exp]

/-- **FD-1 (b').** `e^{Re logDerivFwd} ≥ Im f_t(z) / Im z`. -/
theorem im_fwdMap_div_le_exp_re_logDerivFwd (hW : Continuous W) (hz : 0 < z.im)
    (hsol : ∃ u, IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fwdMap W t z).im / z.im ≤ Real.exp (logDerivFwd W t z).re := by
  obtain ⟨u₀, hu₀⟩ := hsol
  have hu := isForwardSol_fwdMap hW hz hu₀
  set u : ℝ → ℂ := fun s => fwdMap W s z
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hi1 : IntervalIntegrable (fun s => 2 / u s ^ 2) volume 0 t :=
    ((sol_contOn_two_div_sq hu).mono hsub).intervalIntegrable_of_Icc ht.1
  have hi2 : IntervalIntegrable (fun s => 1 / ‖u s‖ ^ 2) volume 0 t :=
    ((sol_contOn_inv_sq hu).mono hsub).intervalIntegrable_of_Icc ht.1
  have hre : (logDerivFwd W t z).re = -∫ s in (0 : ℝ)..t, (2 / u s ^ 2).re := by
    show (-∫ s in (0 : ℝ)..t, 2 / u s ^ 2).re = _
    rw [Complex.neg_re]; congr 1; exact (intervalIntegral.intervalIntegral_re hi1).symm
  have hle : ∫ s in (0 : ℝ)..t, (2 / u s ^ 2).re ≤ ∫ s in (0 : ℝ)..t, 2 * (1 / ‖u s‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on ht.1
    · exact ((Complex.continuous_re.comp_continuousOn (sol_contOn_two_div_sq hu)).mono
        hsub).intervalIntegrable_of_Icc ht.1
    · exact hi2.const_mul 2
    · intro s _
      have := Complex.re_le_norm (2 / u s ^ 2)
      rw [norm_two_div_sq] at this
      linarith [show 2 / ‖u s‖ ^ 2 = 2 * (1 / ‖u s‖ ^ 2) by ring]
  rw [intervalIntegral.integral_const_mul] at hle
  have hY := sol_im_eq_clock hW hz hu ht
  rw [div_le_iff₀ hz, hY, hre, mul_comm]
  apply mul_le_mul_of_nonneg_right _ hz.le
  exact Real.exp_le_exp.mpr (by linarith)

/-- **FD-1 (b'').** `|Im logDerivFwd| ≤ 2 S_t`. -/
theorem abs_im_logDerivFwd_le (hW : Continuous W) (hz : 0 < z.im)
    (hsol : ∃ u, IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    |(logDerivFwd W t z).im| ≤ 2 * fwdClock W t z := by
  obtain ⟨u₀, hu₀⟩ := hsol
  have hu := isForwardSol_fwdMap hW hz hu₀
  set u : ℝ → ℂ := fun s => fwdMap W s z
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hi1 : IntervalIntegrable (fun s => 2 / u s ^ 2) volume 0 t :=
    ((sol_contOn_two_div_sq hu).mono hsub).intervalIntegrable_of_Icc ht.1
  have hi2 : IntervalIntegrable (fun s => 1 / ‖u s‖ ^ 2) volume 0 t :=
    ((sol_contOn_inv_sq hu).mono hsub).intervalIntegrable_of_Icc ht.1
  have him : (logDerivFwd W t z).im = -∫ s in (0 : ℝ)..t, (2 / u s ^ 2).im := by
    show (-∫ s in (0 : ℝ)..t, 2 / u s ^ 2).im = _
    rw [Complex.neg_im]; congr 1; exact (intervalIntegral.intervalIntegral_im hi1).symm
  rw [him, abs_neg]
  refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
  show _ ≤ 2 * ∫ s in (0 : ℝ)..t, 1 / ‖u s‖ ^ 2
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on ht.1
  · exact ((Complex.continuous_im.comp_continuousOn (sol_contOn_two_div_sq hu)).abs.mono
      hsub).intervalIntegrable_of_Icc ht.1
  · exact hi2.const_mul 2
  · intro s _
    have := Complex.abs_im_le_norm (2 / u s ^ 2)
    rw [norm_two_div_sq] at this
    linarith [show 2 / ‖u s‖ ^ 2 = 2 * (1 / ‖u s‖ ^ 2) by ring]

/-- **FD-1 (c).** `dC_t/dt = -4 (Im f_t)² / |f_t|⁴`. -/
theorem hasDerivWithinAt_fwdLogCR (hW : Continuous W) (hz : 0 < z.im)
    (hsol : ∃ u, IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => fwdLogCR W s z)
      (-4 * (fwdMap W t z).im ^ 2 / ‖fwdMap W t z‖ ^ 4) (Icc 0 T) t := by
  obtain ⟨u₀, hu₀⟩ := hsol
  have hu := isForwardSol_fwdMap hW hz hu₀
  set u : ℝ → ℂ := fun s => fwdMap W s z
  have hY := sol_hasDerivWithinAt_im hu ht
  have hYpos := sol_im_pos hW hz hu ht
  have h1 := hY.log hYpos.ne'
  have hL := (hasDerivWithinAt_integral_Icc (sol_contOn_two_div_sq hu) ht).neg
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hL
  have h3 := h1.sub h2
  have e := logCR_alg (u t) hYpos
  have h4 := h3.congr_deriv (g' := -4 * (u t).im ^ 2 / ‖u t‖ ^ 4) (by rw [← e]; simp)
  simp only [Function.comp_def, Complex.reCLM_apply] at h4
  exact h4

/-! ## FD-2: swallowing -/

/-- **FD-2 (inf).** At a finite swallowing time `σ`, `inf_{t<σ} Im f_t(z) = 0`. -/
theorem exists_im_fwdMap_lt_of_swallowTime (hW : Continuous W) (hz : 0 < z.im) {σ : ℝ}
    (hσ : swallowTime W z = ENNReal.ofReal σ) {c : ℝ} (hc : 0 < c) :
    ∃ t, 0 ≤ t ∧ t < σ ∧ (fwdMap W t z).im < c := by
  by_contra hcon
  push Not at hcon
  have hσpos : 0 < σ := by
    have := swallowTime_pos hW hz; rw [hσ] at this; exact ENNReal.ofReal_pos.mp this
  have hex : ∀ t, 0 ≤ t → t < σ → ∃ u, IsForwardSol W z t u := by
    intro t ht0 hts
    apply exists_isForwardSol_of_not_mem_fwdHull ht0 hz
    rintro ⟨-, hle⟩
    rw [hσ, ENNReal.ofReal_le_ofReal_iff ht0] at hle
    linarith
  have hc2 : 0 < c / 2 := half_pos hc
  obtain ⟨v, hv0, hvd⟩ := FwdHolo.exists_tf_sol hW hc2 (T := σ + 1) (by linarith) z
  have hvc : ContinuousOn v (Icc 0 (σ + 1)) := fun t ht => (hvd t ht).continuousWithinAt
  have hid : ∀ t, 0 ≤ t → t < σ → c ≤ (v t).im := by
    intro t ht0 hts
    obtain ⟨u, hu⟩ := hex t ht0 hts
    have hTsub : Icc 0 t ⊆ Icc 0 (σ + 1) := Icc_subset_Icc_right (by linarith)
    have huim : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (u s).im := fun s hs => by
      rw [← fwdMap_eq hW hz hu hs]; exact hcon s hs.1 (lt_of_le_of_lt hs.2 hts)
    have hg' : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun r => u r + (W r : ℂ))
        (FwdHolo.tf W (c / 2) s (u s + (W s : ℂ))) (Icc 0 t) s := by
      intro s hs
      have e : FwdHolo.tf W (c / 2) s (u s + (W s : ℂ)) = 2 / u s := by
        show FwdHolo.vf W s (FwdHolo.proj (c / 2) (u s + (W s : ℂ))) = _
        rw [FwdHolo.proj_of_le (by simp; linarith [huim s hs])]
        simp [FwdHolo.vf]
      rw [e]; exact FwdHolo.hasDerivWithinAt_shift hu hs
    have hgc : ContinuousOn (fun r => u r + (W r : ℂ)) (Icc 0 t) :=
      hu.1.add (Complex.continuous_ofReal.comp hW).continuousOn
    have heq := ODE_solution_unique (v := fun s => FwdHolo.tf W (c / 2) s)
      (fun s => FwdHolo.tf_lipschitz hc2 W s) (hvc.mono hTsub)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc
        ((hvd s (hTsub (Ico_subset_Icc_self hs))).mono hTsub) hs)
      hgc (fun s hs => hasDerivWithinAt_Ici_of_Icc (hg' s (Ico_subset_Icc_self hs)) hs)
      (by rw [hv0, FwdHolo.sol_zero hu ht0]; ring)
    have := heq ⟨ht0, le_rfl⟩
    simp only at this
    rw [this]; simpa using huim t ⟨ht0, le_rfl⟩
  have hvAt : ContinuousAt v σ := (hvc σ ⟨hσpos.le, by linarith⟩).continuousAt
    (Icc_mem_nhds hσpos (by linarith))
  have hImAt : ContinuousAt (fun t => (v t).im) σ :=
    Complex.continuous_im.continuousAt.comp hvAt
  have hvσ : c ≤ (v σ).im := by
    refine ge_of_tendsto (x := 𝓝[<] σ) (hImAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsLT hσpos] with t ht using hid t ht.1.le ht.2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hImAt.eventually (lt_mem_nhds (by linarith : c / 2 < (v σ).im)))
  set δ := min (ε / 2) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hsub : Icc 0 (σ + δ) ⊆ Icc 0 (σ + 1) := Icc_subset_Icc_right (by linarith)
  have hall : ∀ t ∈ Icc (0 : ℝ) (σ + δ), c / 2 ≤ (v t).im := by
    intro t ht
    rcases lt_or_ge t σ with h | h
    · linarith [hid t ht.1 h]
    · refine (hball ?_).le
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [ht.2]
  have hsolv := FwdHolo.isForwardSol_of_tf hW hc2 hv0
    (fun t ht => (hvd t (hsub ht)).mono hsub) hall
  have hle := ofReal_le_swallowTime (T := σ + δ) (by linarith) ⟨_, hsolv⟩
  rw [hσ, ENNReal.ofReal_le_ofReal_iff hσpos.le] at hle
  linarith

/-- **FD-2 (clock).** At a finite swallowing time `σ`, the clock `S_t` is unbounded on `[0,σ)`. -/
theorem fwdClock_unbounded_of_swallowTime (hW : Continuous W) (hz : 0 < z.im) {σ : ℝ}
    (hσ : swallowTime W z = ENNReal.ofReal σ) (M : ℝ) :
    ∃ t, 0 ≤ t ∧ t < σ ∧ M < fwdClock W t z := by
  obtain ⟨t, ht0, hts, hlt⟩ := exists_im_fwdMap_lt_of_swallowTime hW hz hσ
    (c := z.im * Real.exp (-2 * M)) (by positivity)
  refine ⟨t, ht0, hts, ?_⟩
  have hsol : ∃ u, IsForwardSol W z t u := by
    apply exists_isForwardSol_of_not_mem_fwdHull ht0 hz
    rintro ⟨-, hle⟩
    rw [hσ, ENNReal.ofReal_le_ofReal_iff ht0] at hle
    linarith
  rw [im_fwdMap_eq_clock hW hz hsol ⟨ht0, le_rfl⟩] at hlt
  have := Real.exp_lt_exp.mp (lt_of_mul_lt_mul_left hlt hz.le)
  linarith

lemma swallowTime_eq_of_mem_fwdHull (hW : Continuous W) {T : ℝ} (h : z ∈ fwdHull W T) :
    ∃ σ ≤ T, swallowTime W z = ENNReal.ofReal σ := by
  obtain ⟨hz, hle⟩ := h
  have hpos := swallowTime_pos hW hz
  have hT : 0 ≤ T := by
    by_contra hT; push Not at hT
    rw [ENNReal.ofReal_of_nonpos hT.le] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl _)
  have hne : swallowTime W z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  exact ⟨(swallowTime W z).toReal, ENNReal.toReal_le_of_le_ofReal hT hle,
    (ENNReal.ofReal_toReal hne).symm⟩

/-- **FD-2 (hull, clock form).** `z ∈ K_T` iff `z ∈ ℍ` has a swallowing time `σ ≤ T` at which
the clock blows up. -/
theorem mem_fwdHull_iff_clock (hW : Continuous W) {T : ℝ} :
    z ∈ fwdHull W T ↔ 0 < z.im ∧ ∃ σ ≤ T, swallowTime W z = ENNReal.ofReal σ ∧
      ∀ M : ℝ, ∃ t, 0 ≤ t ∧ t < σ ∧ M < fwdClock W t z := by
  constructor
  · intro h
    obtain ⟨σ, hσT, hσ⟩ := swallowTime_eq_of_mem_fwdHull hW h
    exact ⟨h.1, σ, hσT, hσ, fwdClock_unbounded_of_swallowTime hW h.1 hσ⟩
  · rintro ⟨hz, σ, hσT, hσ, -⟩
    exact ⟨hz, hσ ▸ ENNReal.ofReal_le_ofReal hσT⟩

/-- **FD-2 (hull, imaginary-part form).** `z ∈ K_T` iff `z ∈ ℍ` has a swallowing time `σ ≤ T`
with `inf_{t<σ} Im f_t(z) = 0`. -/
theorem mem_fwdHull_iff_inf_im (hW : Continuous W) {T : ℝ} :
    z ∈ fwdHull W T ↔ 0 < z.im ∧ ∃ σ ≤ T, swallowTime W z = ENNReal.ofReal σ ∧
      ∀ c > 0, ∃ t, 0 ≤ t ∧ t < σ ∧ (fwdMap W t z).im < c := by
  constructor
  · intro h
    obtain ⟨σ, hσT, hσ⟩ := swallowTime_eq_of_mem_fwdHull hW h
    exact ⟨h.1, σ, hσT, hσ, fun c hc => exists_im_fwdMap_lt_of_swallowTime hW h.1 hσ hc⟩
  · rintro ⟨hz, σ, hσT, hσ, -⟩
    exact ⟨hz, hσ ▸ ENNReal.ofReal_le_ofReal hσT⟩

/-! ## FD-3: two-point kernel -/

section TwoPoint

variable {a b : ℂ} {ua ub : ℝ → ℂ}

lemma sol_greenH_hasDerivWithinAt (hW : Continuous W) (ha : 0 < a.im) (hb : 0 < b.im)
    (hab : a ≠ b) (hua : IsForwardSol W a T ua) (hub : IsForwardSol W b T ub) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => greenH (ua s) (ub s))
      (-((2 / ua t).im * (2 / ub t).im)) (Icc 0 T) t := by
  have hxa := sol_im_pos hW ha hua ht
  have hxb := sol_im_pos hW hb hub ht
  have hne : ua t ≠ ub t := by
    intro h
    have e := FwdHolo.sol_sub_eq hua hub t ht
    rw [h, sub_self] at e
    exact (mul_ne_zero (sub_ne_zero.mpr hab.symm) (Complex.exp_ne_zero _)) e.symm
  have sa := FwdHolo.hasDerivWithinAt_shift hua ht
  have sb := FwdHolo.hasDerivWithinAt_shift hub ht
  have hP : HasDerivWithinAt (fun s => ua s - ub s) (2 / ua t - 2 / ub t) (Icc 0 T) t := by
    exact (sa.sub sb).congr (fun s _ => by simp only [Pi.sub_apply]; ring)
      (by simp only [Pi.sub_apply]; ring)
  have hQ : HasDerivWithinAt (fun s => ua s - conj (ub s)) (2 / ua t - conj (2 / ub t))
      (Icc 0 T) t := by
    refine ((sa.sub sb.star).congr_deriv (by rfl)).congr
      (fun s _ => ?_) ?_ <;>
    · simp only [Pi.sub_apply, Complex.star_def, map_add, Complex.conj_ofReal]; ring
  have hq0 : ua t - conj (ub t) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have h := (hasDerivWithinAt_log_norm hQ hq0).sub (hasDerivWithinAt_log_norm hP
    (sub_ne_zero.mpr hne))
  rw [kernel_alg hxa hxb hne] at h
  exact h

/-- **FD-3 (derivative).** `d/dt G(f_t a, f_t b) = -Im(2/f_t a) Im(2/f_t b)`. -/
theorem hasDerivWithinAt_greenH_fwdMap (hW : Continuous W) (ha : 0 < a.im) (hb : 0 < b.im)
    (hab : a ≠ b) (hsa : ∃ u, IsForwardSol W a T u) (hsb : ∃ u, IsForwardSol W b T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => greenH (fwdMap W s a) (fwdMap W s b))
      (-((2 / fwdMap W t a).im * (2 / fwdMap W t b).im)) (Icc 0 T) t := by
  obtain ⟨u₁, hu₁⟩ := hsa
  obtain ⟨u₂, hu₂⟩ := hsb
  exact sol_greenH_hasDerivWithinAt hW ha hb hab (isForwardSol_fwdMap hW ha hu₁)
    (isForwardSol_fwdMap hW hb hu₂) ht

lemma greenH_sub_ofReal (x y : ℂ) (r : ℝ) : greenH (x - r) (y - r) = greenH x y := by
  simp only [greenH, map_sub, Complex.conj_ofReal, sub_sub_sub_cancel_right]

lemma greenH_fwdMap_zero (hW : Continuous W) (ha : 0 < a.im) (hb : 0 < b.im) (hT : 0 ≤ T)
    (hsa : ∃ u, IsForwardSol W a T u) (hsb : ∃ u, IsForwardSol W b T u) :
    greenH (fwdMap W 0 a) (fwdMap W 0 b) = greenH a b := by
  obtain ⟨u₁, hu₁⟩ := hsa
  obtain ⟨u₂, hu₂⟩ := hsb
  rw [fwdMap_eq hW ha hu₁ ⟨le_rfl, hT⟩, fwdMap_eq hW hb hu₂ ⟨le_rfl, hT⟩,
    FwdHolo.sol_zero hu₁ hT, FwdHolo.sol_zero hu₂ hT, greenH_sub_ofReal]

/-- **FD-3 (monotonicity).** `t ↦ G(f_t a, f_t b)` is nonincreasing on `[0,T]`. -/
theorem antitoneOn_greenH_fwdMap (hW : Continuous W) (ha : 0 < a.im) (hb : 0 < b.im)
    (hab : a ≠ b) (hsa : ∃ u, IsForwardSol W a T u) (hsb : ∃ u, IsForwardSol W b T u) :
    AntitoneOn (fun s => greenH (fwdMap W s a) (fwdMap W s b)) (Icc 0 T) := by
  refine antitoneOn_Icc_of_hasDerivWithinAt
    (fun t ht => hasDerivWithinAt_greenH_fwdMap hW ha hb hab hsa hsb ht) ?_
  intro t ht
  obtain ⟨u₁, hu₁⟩ := hsa
  obtain ⟨u₂, hu₂⟩ := hsb
  have ht' := Ioo_subset_Icc_self ht
  have p1 := sol_im_pos hW ha (isForwardSol_fwdMap hW ha hu₁) ht'
  have p2 := sol_im_pos hW hb (isForwardSol_fwdMap hW hb hu₂) ht'
  have n1 : (2 / fwdMap W t a).im < 0 := by
    rw [im_two_div]
    have : 0 < ‖fwdMap W t a‖ ^ 2 := by
      have := norm_pos_iff.mpr (fun h => by simp [h] at p1 : fwdMap W t a ≠ 0); positivity
    exact div_neg_of_neg_of_pos (by simp at p1 ⊢; linarith) this
  have n2 : (2 / fwdMap W t b).im < 0 := by
    rw [im_two_div]
    have : 0 < ‖fwdMap W t b‖ ^ 2 := by
      have := norm_pos_iff.mpr (fun h => by simp [h] at p2 : fwdMap W t b ≠ 0); positivity
    exact div_neg_of_neg_of_pos (by simp at p2 ⊢; linarith) this
  simp only [neg_nonpos]; exact (mul_pos_of_neg_of_neg n1 n2).le

/-- **FD-3 (bounds).** `0 ≤ G(f_t a, f_t b) ≤ G(a, b)` for `t ∈ [0,T]`. -/
theorem greenH_fwdMap_mem_Icc (hW : Continuous W) (ha : 0 < a.im) (hb : 0 < b.im)
    (hab : a ≠ b) (hsa : ∃ u, IsForwardSol W a T u) (hsb : ∃ u, IsForwardSol W b T u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    0 ≤ greenH (fwdMap W t a) (fwdMap W t b) ∧
      greenH (fwdMap W t a) (fwdMap W t b) ≤ greenH a b := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  refine ⟨?_, ?_⟩
  · obtain ⟨u₁, hu₁⟩ := hsa
    obtain ⟨u₂, hu₂⟩ := hsb
    have h1 := isForwardSol_fwdMap hW ha hu₁
    have h2 := isForwardSol_fwdMap hW hb hu₂
    apply greenH_nonneg (sol_im_pos hW ha h1 ht).le (sol_im_pos hW hb h2 ht).le
    intro h
    have e := FwdHolo.sol_sub_eq h1 h2 t ht
    beta_reduce at e
    rw [h, sub_self] at e
    exact (mul_ne_zero (sub_ne_zero.mpr hab.symm) (Complex.exp_ne_zero _)) e.symm
  · rw [← greenH_fwdMap_zero hW ha hb hT hsa hsb]
    exact antitoneOn_greenH_fwdMap hW ha hb hab hsa hsb ⟨le_rfl, hT⟩ ht ht.1

end TwoPoint

end FwdClock

end QuantumZipper
